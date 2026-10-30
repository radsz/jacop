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
import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Copyable;
import org.jacop.api.RemoveLevelLate;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * The network flow constraint. Use the NetworkBuilder to create a network and instantiate the
 * network.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class NetworkFlow extends Constraint
    implements UsesQueueVariable, Stateful, RemoveLevelLate, Copyable<NetworkFlow>, Explainable {

  /** Instance counter. */
  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final int QUEUE_INDEX = 2;
  private static final boolean DO_INSTRUMENTATION = false;
  private static final boolean SHOW_LEVEL = false;

  /** The network. */
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

  /** Pairs of a variable of the caller and the copy the network uses for one of its roles. */
  private final List<IntVar[]> copies = new ArrayList<>();

  /** The network as given to the constructor, or null if it has handlers a copy cannot rebuild. */
  private final Definition definition;

  /**
   * The network as built, before any propagation changes the nodes and arcs: nodes by name and
   * balance, arcs by the positions of their nodes, cost, capacities and variables, and the handlers
   * by the positions of their arcs.
   */
  private record Definition(
      String[] names,
      int[] balances,
      int[][] arcs,
      IntVar[] flows,
      IntVar[] weights,
      Object[] handlers,
      IntVar costVariable) {

    /** A handler of the variable of a domain structure. */
    record Structure(
        IntVar variable, IntDomain[] domains, int[] arcs, DomainStructure.Behavior behavior) {}

    static Definition of(
        List<Node> nodes, List<Arc> arcs, List<VarHandler> handlers, IntVar costVariable) {
      Map<Node, Integer> nodeIndex = new IdentityHashMap<>();
      String[] names = new String[nodes.size()];
      int[] balances = new int[nodes.size()];
      for (int i = 0; i < names.length; i++) {
        Node node = nodes.get(i);
        nodeIndex.put(node, i);
        names[i] = node.name;
        balances[i] = node.initialBalance;
      }
      Map<Arc, Integer> arcIndex = new IdentityHashMap<>();
      int[][] arcData = new int[arcs.size()][];
      IntVar[] flows = new IntVar[arcs.size()];
      IntVar[] weights = new IntVar[arcs.size()];
      for (int i = 0; i < arcData.length; i++) {
        Arc arc = arcs.get(i);
        Integer tail = nodeIndex.get(arc.tail());
        Integer head = nodeIndex.get(arc.head);
        if (tail == null || head == null || !arc.forward) {
          return null;
        }
        arcIndex.put(arc, i);
        int lower = arc.companion == null ? 0 : arc.companion.flowOffset;
        arcData[i] = new int[] {tail, head, arc.cost, lower, lower + arc.capacity};
        if (arc.companion != null) {
          flows[i] = arc.companion.xVar;
          weights[i] = arc.companion.wVar;
        }
      }
      Object[] handlerData = new Object[handlers.size()];
      for (int i = 0; i < handlerData.length; i++) {
        VarHandler handler = handlers.get(i);
        if (handler instanceof ArcCompanion companion && arcIndex.containsKey(companion.arc)) {
          handlerData[i] = arcIndex.get(companion.arc);
        } else if (handler instanceof DomainStructure structure
            && structure.getClass() == DomainStructure.class) {
          int[] structureArcs = new int[structure.arcs.length];
          for (int k = 0; k < structureArcs.length; k++) {
            Integer index = arcIndex.get(structure.arcs[k]);
            if (index == null) {
              return null;
            }
            structureArcs[k] = index;
          }
          handlerData[i] =
              new Structure(
                  structure.variable, structure.domains.clone(), structureArcs, structure.behavior);
        } else {
          return null;
        }
      }
      return new Definition(names, balances, arcData, flows, weights, handlerData, costVariable);
    }

    NetworkBuilder build(VarMap map) {
      NetworkBuilder builder =
          new NetworkBuilder(costVariable == null ? null : map.get(costVariable));
      Node[] nodes = new Node[names.length];
      for (int i = 0; i < nodes.length; i++) {
        nodes[i] = builder.addNode(names[i], balances[i]);
      }
      Arc[] built = new Arc[arcs.length];
      for (int i = 0; i < built.length; i++) {
        int[] a = arcs[i];
        IntVar weight = weights[i] == null ? null : map.get(weights[i]);
        // the cost of an arc with a weight variable is the variable's minimum, as in the builder
        int cost = weight == null ? a[2] : weight.min();
        built[i] = new Arc(nodes[a[0]], nodes[a[1]], cost, a[3], a[4]);
        builder.arcList.add(built[i]);
        if (flows[i] != null || weights[i] != null) {
          if (built[i].companion == null) {
            built[i].companion = new ArcCompanion(built[i], 0);
          }
          built[i].companion.xVar = flows[i] == null ? null : map.get(flows[i]);
          built[i].companion.wVar = weight;
        }
      }
      for (Object handler : handlers) {
        if (handler instanceof Structure st) {
          Arc[] structureArcs = new Arc[st.arcs().length];
          for (int k = 0; k < structureArcs.length; k++) {
            structureArcs[k] = built[st.arcs()[k]];
          }
          builder.handlerList.add(
              new DomainStructure(
                  map.get(st.variable()), st.domains(), structureArcs, st.behavior()));
        } else {
          builder.handlerList.add(built[(Integer) handler].companion);
        }
      }
      return builder;
    }
  }

  /* Initialization */

  // It can handle duplicates of variables thanks to using MultiVarHandler that takes care of this.
  private NetworkFlow(
      List<Node> nodes, List<Arc> arcs, List<VarHandler> flowVariables, IntVar cost) {

    // the network of the caller, before separateRoles gives variables in two roles a copy
    this.definition = Definition.of(nodes, arcs, flowVariables, cost);
    this.network = new Pruning(nodes, arcs, statistics);
    this.map = Var.createEmptyPositioning();
    this.queue = new HashSet<>();
    this.costVariable = cost;
    // may replace costVariable by a copy
    separateRoles(flowVariables);
    IntVar costVariable = this.costVariable;

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
   * A variable that is the weight of an arc and also the flow or structure variable of another arc,
   * or the cost and also an arc variable, is pruned in one role during the sensitivity analysis
   * while the network still holds its old bounds in the other role (an arc cost no longer equal to
   * its weight's minimum, or a cost bound computed from stale flows). Such a weight and such a cost
   * get a copy of their own, kept equal to the original by an XeqY imposed with the network.
   */
  private void separateRoles(List<VarHandler> handlers) {
    Set<IntVar> arcVariables = Collections.newSetFromMap(new IdentityHashMap<>());
    for (VarHandler handler : handlers) {
      if (handler instanceof ArcCompanion companion) {
        if (companion.xVar != null) {
          arcVariables.add(companion.xVar);
        }
      } else {
        arcVariables.addAll(handler.listVariables());
      }
    }
    for (VarHandler handler : handlers) {
      if (handler instanceof ArcCompanion companion
          && companion.wVar != null
          && !companion.wVar.singleton()
          && (arcVariables.contains(companion.wVar) || companion.wVar == costVariable)) {
        companion.wVar = copyOf(companion.wVar);
      }
    }
    for (VarHandler handler : handlers) {
      arcVariables.addAll(handler.listVariables());
    }
    if (costVariable != null && arcVariables.contains(costVariable)) {
      costVariable = copyOf(costVariable);
    }
  }

  private IntVar copyOf(IntVar variable) {
    IntVar copy = new IntVar(variable.getStore(), variable.dom().cloneLight());
    copies.add(new IntVar[] {variable, copy});
    return copy;
  }

  /**
   * It constructs a network flow constraint from a network builder.
   *
   * @param builder the network builder containing nodes, arcs, handlers, and cost variable.
   */
  public NetworkFlow(NetworkBuilder builder) {

    this(builder.nodeList, builder.arcList, builder.handlerList, builder.costVariable);
  }

  /** The explanations for lazy clause generation, built on first use; null when there are none. */
  private NetworkFlowExplanation explanation;

  private boolean explanationBuilt;

  private NetworkFlowExplanation explanation() {
    if (!explanationBuilt) {
      explanationBuilt = true;
      if (definition != null && copies.isEmpty()) {
        boolean structures = false;
        for (Object handler : definition.handlers()) {
          structures |= !(handler instanceof Integer);
        }
        explanation =
            NetworkFlowExplanation.of(
                definition.balances(),
                definition.arcs(),
                definition.flows(),
                definition.weights(),
                structures,
                costVariable);
      }
    }
    return explanation;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    NetworkFlowExplanation e = explanation();
    return e != null && e.explain(trail, entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    NetworkFlowExplanation e = explanation();
    return e != null && e.explainFailure(trail, out);
  }

  @Override
  public NetworkFlow copy(VarMap map) {
    if (definition == null) {
      throw new UnsupportedOperationException("This network has handlers a copy cannot rebuild");
    }
    return new NetworkFlow(definition.build(map));
  }

  @Override
  public boolean canCopy() {
    return definition != null;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    return map.get(v).getPruningEvent(v);
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

    for (IntVar[] pair : copies) {
      store.impose(new XeqY(pair[0], pair[1]));
    }
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

  /**
   * Updates the network graph with queued variable changes.
   *
   * @return true if any variable change was processed.
   */
  private boolean updateGraph() {
    boolean changed = !queue.isEmpty();
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
    return changed;
  }

  /** Performs one simplex iteration: run simplex, check feasibility, prune cost min, analyze. */
  private void runOneSimplexIteration(Store store) {
    int result = network.networkSimplex(9999999);

    if (result == -2) {
      throw Store.failException;
    }

    long cost = network.cost(costVariable.max() + 1L);
    if (cost > costVariable.max()) {
      throw Store.failException;
    }
    if (cost > costVariable.min()) {
      costVariable.domain.inMin(store.level, costVariable, (int) cost);
    }

    // Slack between the optimal flow cost and the largest allowed cost. costVariable.min() can be
    // larger than the optimum, so it must not be used here or arcs of valid solutions get pruned.
    int costLimit = (int) Math.min(Integer.MAX_VALUE, costVariable.max() - cost);
    network.pruneNodesWithSmallDegree();
    network.analyze(costLimit);

    if (ASSERTS_ENABLED && !checkFlow(network)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !checkStructure(network)) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  /** Prunes cost minimum from current flow cost, then if all vars are ground, prunes cost max. */
  private void finishConsistencyCostPruning(Store store) {
    long cost = network.cost(costVariable.max() + 1L);
    if (cost > costVariable.max()) {
      throw Store.failException;
    }
    if (cost > costVariable.min()) {
      costVariable.domain.inMin(store.level, costVariable, (int) cost);
    }

    // the cost variable is in the map as well, but it is the one being fixed here
    boolean allVarsGround = true;
    for (IntVar v : map.keySet()) {
      if (v != costVariable && !v.singleton()) {
        allVarsGround = false;
        break;
      }
    }
    if (allVarsGround) {
      costVariable.domain.inMax(store.level, costVariable, (int) cost);
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

    int iteration = 0;
    // The pruning of one iteration (of flow variables such as counters) changes arc bounds, which
    // the next iteration must analyse again for the constraint to reach its fixpoint.
    boolean graphChanged = false;
    while (iteration == 0 || graphChanged || network.needsUpdate(costVariable.max())) {

      if (DO_INSTRUMENTATION) {
        statistics.consistencyIterations++;
      }

      iteration++;
      if (SHOW_LEVEL) {
        log.debug("--------- => Iteration {}", iteration);
      }

      runOneSimplexIteration(store);
      graphChanged = updateGraph();
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
      // an arc of constant cost and capacity has no companion
      ArcCompanion companion = network.allArcs.get(i).companion;
      if (companion == null || companion.wVar == null) {
        result.append(", ").append(network.allArcs.get(i).cost);
      } else {
        result.append(", ").append(companion.wVar);
      }
      result.append(", ").append(companion == null ? null : companion.xVar);
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
