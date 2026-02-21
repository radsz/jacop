/*
 * NetworkFlow.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints.netflow;

import static org.jacop.constraints.netflow.Assert.checkFlow;
import static org.jacop.constraints.netflow.Assert.checkStructure;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.RemoveLevelLate;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * The network flow constraint. Use the NetworkBuilder to create a network and instantiate the
 * network.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class NetworkFlow extends Constraint
    implements UsesQueueVariable, Stateful, RemoveLevelLate {

  /** Instance counter. */
  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final int QUEUE_INDEX = 2;
  private static final boolean DO_INSTRUMENTATION = false;
  private static final boolean SHOW_LEVEL = false;

  /** The network. */
  // public final Network network;
  private final Pruning network;

  /** The variables and their handlers. */
  private final Map<IntVar, VarHandler> map;

  /** The set of queued variables. */
  private final Set<IntVar> queue;

  final Statistics statistics = new Statistics();

  /** The cost variable. */
  private IntVar costVariable;

  /** Disables the queue variable function during consistency. */
  private boolean disableQueueVariable;

  private int previousLevel = -1;

  /* Initialization */

  // It can handle duplicates of variables thanks to using MultiVarHandler that takes care of this.
  private NetworkFlow(
      List<Node> nodes, List<Arc> arcs, List<VarHandler> flowVariables, IntVar costVariable) {

    this.network = new Pruning(nodes, arcs, statistics);
    this.map = Var.createEmptyPositioning();
    this.queue = new HashSet<>();
    this.costVariable = costVariable;

    for (VarHandler ds : flowVariables) {
      for (IntVar v : ds.listVariables()) {
        VarHandler handler = map.get(v);
        if (handler == null) {
          map.put(v, ds);
        } else if (handler instanceof MultiVarHandler varHandler) {
          varHandler.add(ds);
        } else {
          map.put(v, new MultiVarHandler(v, handler, ds));
        }
      }
    }

    map.put(
        costVariable,
        new VarHandler() {
          @Override
          public List<IntVar> listVariables() {
            return Collections.singletonList(costVariable);
          }

          @Override
          public int getPruningEvent(Var variable) {
            return IntDomain.ANY;
          }

          @Override
          public void processEvent(IntVar variable, MutableNetwork network) {}
        });

    // fields in superclass
    this.queueIndex = QUEUE_INDEX;
    this.numberId = idNumber.incrementAndGet();

    setScope(Stream.concat(map.keySet().stream(), Stream.of(costVariable)));
  }

  /**
   * It constructs a network flow constraint from a network builder.
   *
   * @param builder the network builder containing nodes, arcs, handlers, and cost variable.
   */
  public NetworkFlow(NetworkBuilder builder) {

    this(builder.nodeList, builder.arcList, builder.handlerList, builder.costVariable);
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    return map.get((IntVar) v).getPruningEvent(v);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not yet implemented as more precise variant exists.");
  }

  @Override
  public void impose(Store store) {

    if (costVariable == null) {
      costVariable = new IntVar(store, 0, 0);
      log.error("WARNING: No cost variable was set, using zero cost.");
    }

    network.initialize(store);

    // register with store
    queueIndex = QUEUE_INDEX;
    store.registerRemoveLevelLateListener(this);
    super.impose(store);
  }

  /* Search {@literal &} Backtracking */
  @Override
  public void queueVariable(int level, Var variable) {

    if (!disableQueueVariable) {
      if (variable == costVariable) {
        return;
      }
      queue.add((IntVar) variable);
    }
  }

  /** Updates the network graph with queued variable changes. */
  private void updateGraph() {
    // update graph
    network.increaseLevel();
    try {
      disableQueueVariable = true;
      for (IntVar variable : queue) {
        VarHandler handler = map.get(variable);
        handler.processEvent(variable, network);
      }
    } finally {
      queue.clear();
      disableQueueVariable = false;
    }
  }

  /** Performs one simplex iteration: run simplex, check feasibility, prune cost min, analyze. */
  private void runOneSimplexIteration(Store store) {
    int result = network.networkSimplex(9999999);

    if (result == -2) {
      throw Store.failException;
    }

    int cost = (int) network.cost((long) costVariable.max() + 1);
    if (cost > costVariable.max()) {
      throw Store.failException;
    }
    if (cost > costVariable.min()) {
      costVariable.domain.inMin(store.level, costVariable, cost);
    }

    int costLimit = costVariable.max() - costVariable.min();
    network.pruneNodesWithSmallDegree();
    network.analyze(costLimit);

    assert checkFlow(network);
    assert checkStructure(network);
  }

  /** Prunes cost minimum from current flow cost, then if all vars are ground, prunes cost max. */
  private void finishConsistencyCostPruning(Store store) {
    int cost = (int) network.cost((long) costVariable.max() + 1);
    if (cost > costVariable.max()) {
      throw Store.failException;
    }
    if (cost > costVariable.min()) {
      costVariable.domain.inMin(store.level, costVariable, cost);
    }

    boolean allVarsGround = true;
    for (IntVar v : map.keySet()) {
      if (!v.singleton()) {
        allVarsGround = false;
        break;
      }
    }
    if (allVarsGround) {
      costVariable.domain.inMax(store.level, costVariable, cost);
    }
  }

  @Override
  public void consistency(Store store) {

    if (SHOW_LEVEL) {
      log.debug("");
      log.debug("--------- Level {}", store.level);
      log.debug("");
    }

    if (DO_INSTRUMENTATION) {
      statistics.consistencyCalls++;
    }
    updateGraph();

    previousLevel = store.level;

    int iteration = 0;
    while (network.needsUpdate(costVariable.max()) || iteration == 0) {

      if (DO_INSTRUMENTATION) {
        statistics.consistencyIterations++;
      }

      iteration++;
      if (SHOW_LEVEL) {
        log.debug("--------- => Iteration {}", iteration);
      }

      runOneSimplexIteration(store);
      updateGraph();
    }

    finishConsistencyCostPruning(store);
  }

  @Override
  public void removeLevel(int level) {
    queue.clear();
  }

  @Override
  public void removeLevelLate(int level) {

    if (SHOW_LEVEL) {
      log.debug("");
      log.debug("######### Level {}", level);
      log.debug("");
    }

    network.backtrack();
  }

  /* Identifiers */
  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : NetworkFlow([");
    for (int i = 0; i < network.nodes.length; i++) {
      result
          .append("(")
          .append(network.nodes[i].name)
          .append(", ")
          .append(network.nodes[i].initialBalance)
          .append(")");
      if (i < network.nodes.length - 1) {
        result.append(", ");
      }
    }

    result.append("], [");
    for (int i = 0; i < network.allArcs.size(); i++) {
      result.append("(");
      result
          .append(network.allArcs.get(i).tail().name)
          .append("->")
          .append(network.allArcs.get(i).head.name);
      if (network.allArcs.get(i).companion.wVar == null) {
        result.append(", ").append(network.allArcs.get(i).cost);
      } else {
        result.append(", ").append(network.allArcs.get(i).companion.wVar);
      }
      result.append(", ").append(network.allArcs.get(i).companion.xVar);
      result.append(")");
      if (i < network.allArcs.size() - 1) {
        result.append(", ");
      }
    }
    result.append("]");

    result.append(", ").append(costVariable).append("}");
    return result.toString();
  }
}
