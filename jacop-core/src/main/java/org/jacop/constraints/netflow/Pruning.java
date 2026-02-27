/*
 * Pruning.java
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
import java.util.List;
import java.util.PriorityQueue;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.netflow.DomainStructure.Behavior;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;

/**
 * Network extension that performs domain pruning for network flow constraints.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Pruning extends Network {

  // whether to count success rates, etc..
  private static final boolean DO_INSTRUMENTATION = false;

  // minimum number of pruned arcs of call
  private static final int MIN_NUM_PRUNING = 0;

  // percent of pruned arcs of call
  private static final double P_ATTEMPT_PRUNING = 1.0;

  // Increase in score upon successful pruning
  private static final int SUCCESS_SCORE = 5;

  // Decrease in score upon successful pruning
  private static final int FAIL_SCORE = 2;
  private final Statistics statistics;
  private final PriorityQueue<ArcCompanion> queue;
  private final PruningStrategy strategy;
  public int numActiveArcs;

  /**
   * Constructs a pruning network from the given nodes, arcs, and statistics tracker.
   *
   * @param nodes the list of nodes in the network.
   * @param arcs the list of arcs in the network.
   * @param statistics the statistics object for recording pruning instrumentation data.
   */
  public Pruning(List<Node> nodes, List<Arc> arcs, Statistics statistics) {

    super(nodes, arcs);

    this.queue = new PriorityQueue<>();
    this.strategy = new PercentStrategy(P_ATTEMPT_PRUNING, MIN_NUM_PRUNING);

    for (Arc arc : arcs) {
      if (arc.hasCompanion() && arc.index != DELETED_ARC) {
        queue.add(arc.getCompanion());
      }
    }
    this.numActiveArcs = queue.size();

    this.statistics = statistics;
  }

  private void xvarInMax(ArcCompanion companion, int maxFlow) {

    IntVar xVar = companion.xVar;
    int sizeBefore;
    if (DO_INSTRUMENTATION) {
      statistics.Xvars.arcsExamined++;
      sizeBefore = xVar.domain.getSize();
    }
    xVar.domain.inMax(store.level, xVar, maxFlow);
    if (DO_INSTRUMENTATION) {
      int sizeAfter = xVar.domain.getSize();
      if (sizeAfter < sizeBefore) {
        statistics.Xvars.arcsPruned++;
        statistics.Xvars.amountPruned += sizeBefore - sizeAfter;
        companion.pruningScore += SUCCESS_SCORE;
      } else {
        companion.pruningScore -= FAIL_SCORE;
      }
    }
  }

  private void xvarInMin(ArcCompanion companion, int minFlow) {

    IntVar xVar = companion.xVar;
    int sizeBefore;
    if (DO_INSTRUMENTATION) {
      statistics.Xvars.arcsExamined++;
      sizeBefore = xVar.domain.getSize();
    }
    xVar.domain.inMin(store.level, xVar, minFlow);
    if (DO_INSTRUMENTATION) {
      int sizeAfter = xVar.domain.getSize();
      if (sizeAfter < sizeBefore) {
        statistics.Xvars.arcsPruned++;
        statistics.Xvars.amountPruned += sizeBefore - sizeAfter;
        companion.pruningScore += SUCCESS_SCORE;
      } else {
        companion.pruningScore -= FAIL_SCORE;
      }
    }
  }

  private void nvarIn(ArcCompanion companion, int minFlow, int maxFlow) {
    IntVar nVar = companion.xVar;
    int sizeBefore;
    if (DO_INSTRUMENTATION) {
      statistics.Nvars.arcsExamined++;
      sizeBefore = nVar.domain.getSize();
    }
    nVar.domain.in(store.level, nVar, minFlow, maxFlow);
    if (DO_INSTRUMENTATION) {
      int sizeAfter = nVar.domain.getSize();
      if (sizeAfter < sizeBefore) {
        statistics.Nvars.arcsPruned++;
        statistics.Nvars.amountPruned += sizeBefore - sizeAfter;
        companion.pruningScore += SUCCESS_SCORE;
      } else {
        companion.pruningScore -= FAIL_SCORE;
      }
    }
  }

  private void nvarInShift(ArcCompanion companion, IntDomain domain, int shift) {
    IntVar nVar = companion.xVar;
    int sizeBefore;
    if (DO_INSTRUMENTATION) {
      statistics.Nvars.arcsExamined++;
      sizeBefore = nVar.domain.getSize();
    }
    nVar.domain.inShift(store.level, nVar, domain, shift);
    if (DO_INSTRUMENTATION) {
      int sizeAfter = nVar.domain.getSize();
      if (sizeAfter < sizeBefore) {
        statistics.Nvars.arcsPruned++;
        statistics.Nvars.amountPruned += sizeBefore - sizeAfter;
        companion.pruningScore += SUCCESS_SCORE;
      } else {
        companion.pruningScore -= FAIL_SCORE;
      }
    }
  }

  private void wvarIn(ArcCompanion companion, int maxCost) {
    IntVar wVar = companion.wVar;
    int sizeBefore;
    if (DO_INSTRUMENTATION) {
      statistics.Wvars.arcsExamined++;
      sizeBefore = wVar.domain.getSize();
    }
    wVar.domain.inMax(store.level, wVar, maxCost);

    if (DO_INSTRUMENTATION) {
      int sizeAfter = wVar.domain.getSize();
      if (sizeAfter < sizeBefore) {
        statistics.Wvars.arcsPruned++;
        statistics.Wvars.amountPruned += sizeBefore - sizeAfter;
        companion.pruningScore += SUCCESS_SCORE;
      } else {
        companion.pruningScore -= FAIL_SCORE;
      }
    }
  }

  private void svarInDom(ArcCompanion companion, Domain domain) {
    IntVar sVar = companion.structure.variable;
    int sizeBefore;
    if (DO_INSTRUMENTATION) {
      statistics.Svars.arcsExamined++;
      sizeBefore = sVar.domain.getSize();
    }
    sVar.domain.in(store.level, sVar, domain);
    if (DO_INSTRUMENTATION) {
      int sizeAfter = sVar.domain.getSize();
      if (sizeAfter < sizeBefore) {
        statistics.Svars.arcsPruned++;
        statistics.Svars.amountPruned += sizeBefore - sizeAfter;
        companion.pruningScore += SUCCESS_SCORE;
      } else {
        companion.pruningScore -= FAIL_SCORE;
      }
    }
  }

  void pruneNodesWithSmallDegree() {
    for (Node node : nodes) {
      if (node.degree == 1) {
        pruneDegree1Node(node);
      } else if (node.degree == 2) {
        pruneDegree2Node(node);
      }
    }
  }

  private void pruneDegree1Node(Node node) {
    Arc arc = node.adjacencyList[0];
    ArcCompanion companion = arc.companion;
    if (companion == null || companion.xVar == null) {
      return;
    }
    int flow = companion.flowOffset + arc.sister.capacity;
    if (arc.head == node) {
      if (ASSERTS_ENABLED && !(arc.sister.capacity == -node.balance)) {
        throw new IllegalStateException(String.valueOf("\n" + node + "\n" + arc));
      }
    } else {
      if (ASSERTS_ENABLED && !(arc.sister.capacity == node.balance)) {
        throw new IllegalStateException(String.valueOf("\n" + node + "\n" + arc));
      }
    }
    nvarIn(companion, flow, flow);
  }

  private void pruneDegree2Node(Node node) {
    Arc arc1 = node.adjacencyList[0];
    Arc arc2 = node.adjacencyList[1];
    ArcCompanion companion1 = arc1.companion;
    ArcCompanion companion2 = arc2.companion;
    if (companion1 == null
        || companion1.xVar == null
        || companion2 == null
        || companion2.xVar == null) {
      return;
    }

    boolean differentDir;
    int shift = -companion1.flowOffset;
    if (arc1.head == node) {
      differentDir = arc2.head != node;
      shift += node.balance;
    } else {
      differentDir = arc2.head == node;
      shift -= node.balance;
    }
    if (differentDir) {
      shift += companion2.flowOffset;
    } else {
      shift -= companion2.flowOffset;
    }

    IntVar xVar1 = companion1.xVar;
    IntVar xVar2 = companion2.xVar;
    if (differentDir) {
      nvarInShift(companion1, xVar2.domain, -shift);
      nvarInShift(companion2, xVar1.domain, shift);
    } else {
      pruneDegree2NodeSameDir(companion1, companion2, xVar1, xVar2, shift);
    }
  }

  private void pruneDegree2NodeSameDir(
      ArcCompanion companion1, ArcCompanion companion2, IntVar xVar1, IntVar xVar2, int shift) {
    IntDomain xDom = xVar1.dom();
    IntervalDomain yDomIn = new IntervalDomain(xDom.noIntervals() + 1);
    for (int i = xDom.noIntervals() - 1; i >= 0; i--) {
      yDomIn.unionAdapt(new Interval(-shift - xDom.rightElement(i), -shift - xDom.leftElement(i)));
    }
    nvarInShift(companion2, yDomIn, 0);

    IntDomain yDom = xVar2.domain;
    IntervalDomain xDomIn = new IntervalDomain(yDom.noIntervals() + 1);
    for (int i = yDom.noIntervals() - 1; i >= 0; i--) {
      xDomIn.unionAdapt(new Interval(-shift - yDom.rightElement(i), -shift - yDom.leftElement(i)));
    }
    nvarInShift(companion1, xDomIn, 0);
  }

  /**
   * Analyzes arcs in the network to perform domain pruning based on sensitivity analysis.
   *
   * @param costLimit the maximum cost increase allowed for pruning decisions.
   */
  public void analyze(int costLimit) {

    ArcCompanion prev = null;
    strategy.init();
    ArcCompanion companion = strategy.next();

    if (DO_INSTRUMENTATION && companion != null) {
      recordInstrumentationMax(companion);
    }

    while (companion != null) {
      analyzeCompanionArcs(companion, costLimit);

      if (companion.wVar != null && companion.flowOffset > 0) {
        int maxCost = companion.wVar.min() + (costLimit / companion.flowOffset);
        wvarIn(companion, maxCost);
      }

      prev = companion;
      companion = strategy.next();
    }
    if (DO_INSTRUMENTATION && prev != null) {
      recordInstrumentationMin(prev);
    }
    strategy.close();
  }

  private void recordInstrumentationMax(ArcCompanion companion) {
    statistics.Xvars.maxScoreSum += companion.pruningScore;
    statistics.Wvars.maxScoreSum += companion.pruningScore;
    statistics.Svars.maxScoreSum += companion.pruningScore;
  }

  private void recordInstrumentationMin(ArcCompanion prev) {
    statistics.Xvars.minScoreSum += prev.pruningScore;
    statistics.Wvars.minScoreSum += prev.pruningScore;
    statistics.Svars.minScoreSum += prev.pruningScore;
  }

  private void analyzeCompanionArcs(ArcCompanion companion, int costLimit) {
    Arc arc1 = companion.arc;
    Arc arc2 = arc1.sister;
    int residual1 = arc1.capacity;
    int residual2 = arc2.capacity;

    if (residual1 == 0) {
      analyzeArcHelper(arc2, costLimit);
    } else if (residual2 == 0) {
      analyzeArcHelper(arc1, costLimit);
    } else if (residual1 < residual2) {
      analyzeArcHelper(arc1, costLimit);
      analyzeArcHelper(arc2, costLimit);
    } else {
      analyzeArcHelper(arc2, costLimit);
      analyzeArcHelper(arc1, costLimit);
    }
  }

  private void analyzeArcHelper(Arc arc, int costLimit) {
    if (arc.capacity == 0) {
      return;
    }

    int capacity = arc.capacity;
    int flow = analyzeArc(arc, costLimit);
    if (ASSERTS_ENABLED && !(arc.capacity == capacity - flow)) {
      throw new IllegalStateException("Assertion failed");
    }

    final int _capacity = arc.capacity;
    final int _residual = arc.sister.capacity;
    final boolean _forward = arc.forward;
    final ArcCompanion _companion = arc.getCompanion();

    if (arc.index == DELETED_ARC) {
      addArcWithFlow(arc);
    }
    if (ASSERTS_ENABLED && !(checkFlow(this))) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(checkStructure(this))) {
      throw new IllegalStateException("Assertion failed");
    }

    if (DO_INSTRUMENTATION) {
      if (_companion.xVar != null) {
        statistics.Xvars.arcsExamined++;
      }
      if (_companion.wVar != null) {
        statistics.Wvars.arcsExamined++;
      }
      if (_companion.structure != null) {
        statistics.Svars.arcsExamined++;
      }
    }

    if (_capacity > 0) {
      pruneArc(_capacity, _residual, _forward, _companion);
    }

    // restore optimal flow
    networkSimplex(999999);

    long cost = cost(Long.MAX_VALUE);
    if (ASSERTS_ENABLED && !(cost(Long.MAX_VALUE) == cost)) {
      throw new IllegalStateException(String.valueOf(cost(Long.MAX_VALUE) + " != " + cost));
    }
  }

  private int analyzeArc(Arc arc, int costLimit) {
    if (ASSERTS_ENABLED && !(arc.capacity > 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    // Remove arc from graph
    if (arc.index == TREE_ARC && !dualPivot(arc.sister)) {
      // This is the last arc in the cut, prune all remaining capacity
      return 0;
    }
    removeArc(arc);

    // perform sensitivity analysis
    int flow = 0;
    int capacity = arc.capacity;
    Node source = arc.head;
    Node sink = arc.tail();

    int[] state = new int[] {flow, capacity, costLimit};
    analyzeArcLoop(arc, source, sink, state);
    flow = state[0];

    IntVar wVar = arc.getCompanion().wVar;

    if (arc.cost != -arc.sister.cost) {
      throw new AssertionError();
    }
    if (wVar != null) {
      if (arc.forward && wVar.min() != arc.cost) {
        throw new AssertionError();
      }
      if (!arc.forward && wVar.min() != -arc.cost) {
        throw new AssertionError();
      }
    }

    arc.addFlow(flow);

    return flow;
  }

  private void analyzeArcLoop(Arc arc, Node source, Node sink, int[] state) {
    while (state[1] > 0) {
      int unitCost = arc.reducedCost();
      if (ASSERTS_ENABLED && !(unitCost >= 0)) {
        throw new IllegalStateException("Assertion failed");
      }
      if (unitCost > 0) {
        int maxCapacity = state[2] / unitCost;
        if (state[1] > maxCapacity) {
          state[1] = maxCapacity;
          if (state[1] == 0) {
            break;
          }
        }
      }
      int delta = augmentFlow(source, sink, state[1]);
      state[0] += delta;
      state[1] -= delta;
      state[2] -= unitCost * delta;
      if (state[1] == 0 || !dualPivot(blocking)) {
        break;
      }
    }
  }

  private void pruneArcForward(int residual, ArcCompanion companion) {
    if (companion.xVar != null) {
      int maxFlow = companion.flowOffset + residual;
      xvarInMax(companion, maxFlow);
      companion.changeMaxCapacity(maxFlow);
      modified(companion);
    }
    DomainStructure structure = companion.structure;
    if (companion.structure != null && !structure.isGrounded(companion.arcId)) {
      int arcId = companion.arcId;
      if (structure.behavior != Behavior.PRUNE_INACTIVE) {
        Domain arcDomainC = structure.domains[arcId].complement();
        svarInDom(companion, arcDomainC);
      }
    }
  }

  private void pruneArcBackward(int capacity, ArcCompanion companion) {
    if (companion.xVar != null) {
      int minFlow = companion.flowOffset + capacity;
      xvarInMin(companion, minFlow);
      companion.changeMinCapacity(minFlow);
      modified(companion);
    }
    DomainStructure structure = companion.structure;
    if (companion.structure != null && !structure.isGrounded(companion.arcId)) {
      int arcId = companion.arcId;
      if (structure.behavior != Behavior.PRUNE_ACTIVE) {
        Domain arcDomain = structure.domains[arcId];
        svarInDom(companion, arcDomain);
      }
    }
  }

  private void pruneArc(int capacity, int residual, boolean forward, ArcCompanion companion) {
    if (ASSERTS_ENABLED && !(capacity > 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (forward) {
      pruneArcForward(residual, companion);
    } else {
      pruneArcBackward(capacity, companion);
    }
  }

  interface PruningStrategy {

    void init();

    ArcCompanion next();

    void close();
  }

  /** Percentage-based pruning strategy. */
  public class PercentStrategy implements PruningStrategy {

    final double percentage;
    final int minimum;
    final List<ArcCompanion> seen = new ArrayList<>();
    int i;
    int limit;

    PercentStrategy(double percentage, int minimum) {
      this.percentage = percentage;
      this.minimum = minimum;
    }

    /** Initializes the strategy by counting active arcs and computing the pruning limit. */
    @Override
    public void init() {
      int numActiveArcs = 0;
      for (ArcCompanion c : queue) {
        if (c.arc.index != DELETED_ARC) {
          numActiveArcs++;
        }
      }

      i = 0;
      limit =
          Math.max(Math.min(minimum, numActiveArcs), (int) Math.round(numActiveArcs * percentage));
    }

    /**
     * Returns the next arc companion to be pruned, or null if the limit has been reached.
     *
     * @return the next arc companion, or null if no more arcs should be examined.
     */
    @Override
    public ArcCompanion next() {
      if (i < limit) {
        ArcCompanion companion = queue.poll();
        seen.add(companion);
        if (companion.arc.index == DELETED_ARC) {
          return next();
        }
        i++;
        return companion;
      }
      return null;
    }

    /** Restores all examined arc companions back into the priority queue. */
    @Override
    public void close() {
      queue.addAll(seen);
      seen.clear();
    }
  }
}
