/*
 * CostRegular.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2026 Radoslaw Szymanek
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

package org.jacop.constraints.regular;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.In;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.table.Table;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * CostRegular constraint (Demassey, Pesant and Rousseau, "A cost-regular based hybrid column
 * generation approach", Constraints 11(4), 2006). The values of the variables in list must be a
 * word accepted by a deterministic finite automaton, and cost must equal the sum of the costs of
 * the transitions taken. The cost of a transition depends on its state and value and may also
 * depend on the position in the word.
 *
 * <p>The automaton is unfolded into a layered graph with one layer of edges per variable, each edge
 * weighted with the cost of its transition. Every consistency call computes, for each node, the
 * shortest and the longest path from the source and to the sink over the alive edges. An edge is
 * removed when the shortest path through it is above the maximum of cost or the longest path
 * through it is below the minimum of cost; the passes are repeated until no edge is removed. The
 * bounds of cost are set to the shortest and the longest path and a value of a variable is removed
 * when it labels no alive edge. With cost unconstrained this is the generalized arc consistency of
 * {@link Regular} and cost is narrowed to the cheapest and the most expensive accepted word. With
 * cost constrained the filtering is the one of Demassey et al. and of Choco's CostRegular: the
 * bounds of cost are path costs, which need not be in the domain of cost, and a value is kept when
 * some accepted word with it is not too expensive and some, possibly another, is not too cheap.
 *
 * <p>The alive edges of each layer are kept at the front of their part of the edge array, a sparse
 * set whose size is trailed, so a pass visits only alive edges and backtracking restores a layer in
 * constant time. Edges are stored with their source, target, value and cost next to each other. As
 * long as the search does not backtrack, the paths from the source are recomputed only from the
 * first layer that lost an edge, and a call returns at once when no edge was removed and cost did
 * not pass the bounds that can remove an edge. Fully incremental updates of the paths, which trail
 * them per layer as cost-MDD4R does (Perez and Regin, AAAI 2017), were slower on automata of a few
 * states: a change at one layer usually changes the paths of most other layers.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class CostRegular extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Copyable<CostRegular>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final long INF = Long.MAX_VALUE / 4;
  private static final long NEG_INF = -INF;

  /** The variables whose values form the word. */
  public final IntVar[] list;

  /** The total cost of the transitions. */
  public final IntVar cost;

  /** Successor of state q on value firstValue + j is transition[q][j], or -1 when there is none. */
  final int[][] transition;

  final int firstValue;

  final int initialState;

  final int[] finalStates;

  /**
   * Cost of the transition from state q on value firstValue + j at position i is costs[i][q][j].
   */
  final int[][][] costs;

  private List<Constraint> constraints;

  /** One-time work of the first consistency call. */
  private final InitOnce init = new InitOnce();

  /** Set while this constraint prunes domains, so its own changes are not queued again. */
  private boolean pruning;

  // Nodes of level l are levelNodeStart[l]..levelNodeStart[l+1]-1; node 0 is the source.
  private int[] levelNodeStart;

  // Edges of level l are at positions edgeStart[l]..edgeStart[l+1]-1, the alive[l] alive ones
  // first. Each edge takes four ints: source, target, slot and cost.
  private int[] edgeStart;
  private int[] edge;
  private int[] alive;

  /** The values labelling the edges of every level. */
  private LevelSlots slots;

  private long[] forwardMin;
  private long[] forwardMax;
  private long[] backwardMin;
  private long[] backwardMax;

  /** Stamp of the consistency call in which a slot lost its value. */
  private int[] slotRemoved;

  /** Stamp of the pass in which a slot was supported by an edge. */
  private int[] slotSupported;

  private int[] levelSupported;

  /**
   * True while the graph has not changed since the last pass, which then left every alive edge with
   * a shortest path through it of at most lastMaxShortest and a longest path through it of at least
   * lastMinLongest; until cost passes these bounds there is nothing to prune.
   */
  private boolean stable;

  private long lastMaxShortest;
  private long lastMinLongest;

  /** The numbers of alive edges per level, trailed. */
  private AliveCounts counts;

  /**
   * It constructs a cost regular constraint whose transition costs do not depend on the position.
   *
   * @param list the variables whose values form the word, without duplicates.
   * @param transition the successor of state q on value firstValue + j is transition[q][j], -1 if
   *     there is no transition; states are numbered from 0.
   * @param firstValue the value of the first column of transition and costs.
   * @param initialState the initial state.
   * @param finalStates the accepting states.
   * @param costs the cost of the transition from state q on value firstValue + j is costs[q][j].
   * @param cost the variable equal to the sum of the costs of the transitions taken.
   */
  public CostRegular(
      IntVar[] list,
      int[][] transition,
      int firstValue,
      int initialState,
      int[] finalStates,
      int[][] costs,
      IntVar cost) {
    this(list, transition, firstValue, initialState, finalStates, repeat(costs, list), cost);
  }

  /**
   * It constructs a cost regular constraint whose transition costs depend on the position.
   *
   * @param list the variables whose values form the word, without duplicates.
   * @param transition the successor of state q on value firstValue + j is transition[q][j], -1 if
   *     there is no transition; states are numbered from 0.
   * @param firstValue the value of the first column of transition and costs.
   * @param initialState the initial state.
   * @param finalStates the accepting states.
   * @param costs the cost of the transition from state q on value firstValue + j taken by the i-th
   *     variable is costs[i][q][j].
   * @param cost the variable equal to the sum of the costs of the transitions taken.
   */
  public CostRegular(
      IntVar[] list,
      int[][] transition,
      int firstValue,
      int initialState,
      int[] finalStates,
      int[][][] costs,
      IntVar cost) {

    checkInputForNullness(
        new String[] {"list", "transition", "finalStates", "costs", "cost"},
        new Object[][] {list, transition, {finalStates}, costs, {cost}});
    checkInputForDuplicationSkipSingletons("list", list);
    for (IntVar x : list) {
      if (x == cost && !cost.singleton()) {
        throw new IllegalArgumentException(
            "CostRegular: cost must not be one of the variables in list");
      }
    }

    CostAutomatonGraph.check(
        "CostRegular", list.length, transition, firstValue, initialState, finalStates, costs);

    this.queueIndex = 1;
    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.cost = cost;
    this.transition = transition;
    this.firstValue = firstValue;
    this.initialState = initialState;
    this.finalStates = Arrays.copyOf(finalStates, finalStates.length);
    this.costs = costs;

    setScope(Stream.concat(Arrays.stream(list), Stream.of(cost)));
  }

  /**
   * It constructs a cost constraint over a layered graph that a subclass gives in {@link
   * #buildGraph()} through {@link #installGraph(int[], int[], int[])}, instead of an automaton.
   *
   * @param list the variables, the i-th of them labels the edges of the i-th layer, without
   *     duplicates.
   * @param cost the variable equal to the sum of the costs of the edges of the path.
   */
  protected CostRegular(IntVar[] list, IntVar cost) {
    checkInputForNullness(new String[] {"list", "cost"}, new Object[][] {list, {cost}});
    checkInputForDuplicationSkipSingletons("list", list);
    for (IntVar x : list) {
      if (x == cost && !cost.singleton()) {
        throw new IllegalArgumentException(
            getClass().getSimpleName() + ": cost must not be one of the variables in list");
      }
    }
    this.queueIndex = 1;
    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.cost = cost;
    this.transition = null;
    this.firstValue = 0;
    this.initialState = -1;
    this.finalStates = null;
    this.costs = null;

    setScope(Stream.concat(Arrays.stream(list), Stream.of(cost)));
  }

  private static int[][][] repeat(int[][] costs, IntVar[] list) {
    if (list == null) {
      throw new IllegalArgumentException("CostRegular: list is null");
    }
    int[][][] result = new int[list.length][][];
    Arrays.fill(result, costs);
    return result;
  }

  /**
   * It unfolds the automaton into the layered graph and stores each edge with its source, target,
   * slot and cost next to each other. A subclass that describes its graph in another way overrides
   * it and calls {@link #installGraph(int[], int[], int[])}.
   */
  protected void buildGraph() {
    CostAutomatonGraph graph =
        new CostAutomatonGraph(list, transition, firstValue, initialState, finalStates);
    int levels = list.length;
    levelNodeStart = graph.levelNodeStart;
    edgeStart = graph.edgeStart;
    slots = new LevelSlots(list, graph.levelSlotStart, graph.slotValue, getClass());
    edge = new int[4 * graph.edges()];
    for (int level = 0; level < levels; level++) {
      int[][] costMatrix = costs[level];
      for (int e = edgeStart[level]; e < edgeStart[level + 1]; e++) {
        edge[4 * e] = graph.edgeSource[e];
        edge[4 * e + 1] = graph.edgeTarget[e];
        edge[4 * e + 2] = graph.edgeSlot[e];
        edge[4 * e + 3] = costMatrix[graph.edgeState[e]][graph.edgeSymbol[e]];
      }
    }
    allocate(graph.nodes());
  }

  /**
   * It installs a layered graph given by a subclass. Level 0 must hold only the source (node 0) or
   * no node at all, which makes the constraint fail, and every node of the last level is a sink.
   *
   * @param nodeStart the nodes of level l are nodeStart[l]..nodeStart[l+1]-1, for the levels 0 to
   *     list.length.
   * @param edgeStart the edges of level l, which go from a node of level l to a node of level l +
   *     1, are edgeStart[l]..edgeStart[l+1]-1, for the levels 0 to list.length - 1.
   * @param edges four ints per edge: its source, its target, its value (of the variable of its
   *     level) and its cost.
   */
  protected final void installGraph(int[] nodeStart, int[] edgeStart, int[] edges) {
    int levels = list.length;
    if (nodeStart.length != levels + 2 || edgeStart.length != levels + 1) {
      throw new IllegalArgumentException("CostRegular: graph without one layer per variable");
    }
    if (nodeStart[1] > 1) {
      throw new IllegalArgumentException("CostRegular: graph with more than one source");
    }
    this.levelNodeStart = Arrays.copyOf(nodeStart, nodeStart.length);
    this.edgeStart = Arrays.copyOf(edgeStart, edgeStart.length);
    this.edge = Arrays.copyOf(edges, 4 * edgeStart[levels]);
    int[] levelSlotStart = new int[levels + 1];
    // Slots of a level: its distinct values in increasing order.
    int[] slotValue = new int[16];
    int slotCount = 0;
    for (int level = 0; level < levels; level++) {
      levelSlotStart[level] = slotCount;
      int first = edgeStart[level];
      int count = edgeStart[level + 1] - first;
      int[] values = new int[count];
      for (int i = 0; i < count; i++) {
        values[i] = edge[4 * (first + i) + 2];
      }
      Arrays.sort(values);
      int distinct = 0;
      for (int i = 0; i < count; i++) {
        if (i == 0 || values[i] != values[i - 1]) {
          values[distinct++] = values[i];
        }
      }
      if (slotCount + distinct > slotValue.length) {
        slotValue = Arrays.copyOf(slotValue, Math.max(2 * slotValue.length, slotCount + distinct));
      }
      System.arraycopy(values, 0, slotValue, slotCount, distinct);
      for (int i = 0; i < count; i++) {
        int p = 4 * (first + i) + 2;
        edge[p] = slotCount + Arrays.binarySearch(values, 0, distinct, edge[p]);
      }
      slotCount += distinct;
    }
    levelSlotStart[levels] = slotCount;
    slots = new LevelSlots(list, levelSlotStart, Arrays.copyOf(slotValue, slotCount), getClass());
    allocate(nodeStart[levels + 1]);
  }

  private void allocate(int nodes) {
    int levels = list.length;
    int[] edgesPerLevel = new int[levels];
    for (int level = 0; level < levels; level++) {
      edgesPerLevel[level] = edgeStart[level + 1] - edgeStart[level];
    }
    counts = new AliveCounts(edgesPerLevel);
    alive = counts.alive;
    forwardMin = new long[nodes];
    forwardMax = new long[nodes];
    backwardMin = new long[nodes];
    backwardMax = new long[nodes];
    slotRemoved = slots.removed;
    slotSupported = slots.supported;
    levelSupported = slots.levelSupported;
  }

  @Override
  public void impose(Store store) {

    buildGraph();

    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var v) {

    if (!pruning) {
      slots.queue(v);
    }
  }

  @Override
  public void removeLevel(int level) {

    counts.removeLevel(level);
    stable = false;
    slots.clearQueue();
  }

  /** It moves the edge at position i to position j and the edge at position j to position i. */
  private void swap(int i, int j) {
    int[] e = edge;
    int a = 4 * i;
    int b = 4 * j;
    for (int k = 0; k < 4; k++) {
      int t = e[a + k];
      e[a + k] = e[b + k];
      e[b + k] = t;
    }
  }

  @Override
  public void consistency(Store store) {

    counts.begin(store.level);

    int levels = list.length;
    if (init.begin(store)) {
      pruning = true;
      try {
        slots.restrictToSlots(store);
      } finally {
        pruning = false;
      }
    }

    if (levelNodeStart[1] == 0) {
      throw Store.failException;
    }
    if (levels == 0) {
      cost.domain.in(store.level, cost, 0, 0);
      return;
    }

    if (stable
        && slots.queueEmpty()
        && cost.max() >= lastMaxShortest
        && cost.min() <= lastMinLongest) {
      return;
    }

    // Slots of the changed levels whose values were removed.
    // The paths from the source stay valid below the first level that lost an edge, unless the
    // search backtracked since they were computed.
    int removedStamp = slots.nextStamp();
    int from = slots.markRemoved(removedStamp);
    if (!stable) {
      from = 0;
    }

    do {
      forwardPass(removedStamp, from);
      from = backwardPass(store);
    } while (from >= 0);

    stable = true;

    pruning = true;
    try {
      slots.pruneUnsupported(store);
    } finally {
      pruning = false;
    }
  }

  /**
   * It computes the shortest and longest paths from the source to every node over the alive edges
   * and removes edges whose source is not reached or whose value was removed in the given stamp.
   */
  private void forwardPass(int removedStamp, int from) {
    final int[] e = edge;
    final long[] fMin = forwardMin;
    final long[] fMax = forwardMax;
    final int[] removed = slotRemoved;
    fMin[0] = 0;
    fMax[0] = 0;
    int levels = list.length;
    for (int level = from; level < levels; level++) {
      for (int v = levelNodeStart[level + 1]; v < levelNodeStart[level + 2]; v++) {
        fMin[v] = INF;
        fMax[v] = NEG_INF;
      }
      int start = edgeStart[level];
      int end = start + alive[level];
      int i = start;
      while (i < end) {
        int p = 4 * i;
        int u = e[p];
        long a = fMin[u];
        if (a == INF || removed[e[p + 2]] == removedStamp) {
          swap(i, --end);
          continue;
        }
        int v = e[p + 1];
        int c = e[p + 3];
        if (a + c < fMin[v]) {
          fMin[v] = a + c;
        }
        long b = fMax[u] + c;
        if (b > fMax[v]) {
          fMax[v] = b;
        }
        i++;
      }
      if (end == start) {
        throw Store.failException;
      }
      if (end - start != alive[level]) {
        counts.set(level, end - start);
      }
    }
  }

  /**
   * It computes the shortest and longest paths from every node to the sink, removes the edges that
   * lead to no path or to no path whose cost is within the bounds of cost, marks the values with an
   * alive edge and narrows cost to the shortest and longest path.
   *
   * @return the first level whose edges may change the paths from the source when another pass is
   *     needed because of removed edges or bounds of cost moved past an edge, otherwise -1.
   */
  private int backwardPass(Store store) {
    final int[] e = edge;
    final long[] fMin = forwardMin;
    final long[] fMax = forwardMax;
    final long[] bMin = backwardMin;
    final long[] bMax = backwardMax;
    final int[] supported = slotSupported;
    final int support = slots.nextStamp();
    final long costMin = cost.min();
    final long costMax = cost.max();
    long maxShortest = Long.MIN_VALUE;
    long minLongest = Long.MAX_VALUE;
    int levels = list.length;
    int forwardFrom = levels;
    for (int n = levelNodeStart[levels]; n < levelNodeStart[levels + 1]; n++) {
      bMin[n] = 0;
      bMax[n] = 0;
    }
    for (int level = levels - 1; level >= 0; level--) {
      for (int u = levelNodeStart[level]; u < levelNodeStart[level + 1]; u++) {
        bMin[u] = INF;
        bMax[u] = NEG_INF;
      }
      int start = edgeStart[level];
      int end = start + alive[level];
      int count = 0;
      int i = start;
      while (i < end) {
        int p = 4 * i;
        int v = e[p + 1];
        long toMin = bMin[v];
        if (toMin == INF) {
          swap(i, --end);
          continue;
        }
        int u = e[p];
        int c = e[p + 3];
        long shortest = fMin[u] + c + toMin;
        long longest = fMax[u] + c + bMax[v];
        if (shortest > costMax || longest < costMin) {
          if (fMin[u] + c == fMin[v] || fMax[u] + c == fMax[v]) {
            forwardFrom = level;
          }
          swap(i, --end);
          continue;
        }
        if (shortest > maxShortest) {
          maxShortest = shortest;
        }
        if (longest < minLongest) {
          minLongest = longest;
        }
        if (c + toMin < bMin[u]) {
          bMin[u] = c + toMin;
        }
        long b = c + bMax[v];
        if (b > bMax[u]) {
          bMax[u] = b;
        }
        int s = e[p + 2];
        if (supported[s] != support) {
          supported[s] = support;
          count++;
        }
        i++;
      }
      if (end == start) {
        throw Store.failException;
      }
      if (end - start != alive[level]) {
        counts.set(level, end - start);
      }
      levelSupported[level] = count;
    }

    long shortest = bMin[0];
    long longest = bMax[0];
    if (shortest > IntDomain.MAX_INT || longest < IntDomain.MIN_INT) {
      throw Store.failException;
    }
    if (shortest > costMin || longest < costMax) {
      pruning = true;
      try {
        cost.domain.in(
            store.level,
            cost,
            (int) Math.max(shortest, IntDomain.MIN_INT),
            (int) Math.min(longest, IntDomain.MAX_INT));
      } finally {
        pruning = false;
      }
    }
    lastMaxShortest = maxShortest;
    lastMinLongest = minLongest;
    if (forwardFrom < levels) {
      return forwardFrom;
    }
    return cost.min() > minLongest || cost.max() < maxShortest ? levels : -1;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    if (v == cost) {
      Integer event = getConsistencyPruningEventFromMap(v);
      return event != null ? event : IntDomain.BOUND;
    }
    return super.getConsistencyPruningEvent(v);
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton()) {
      return false;
    }
    for (IntVar x : list) {
      if (!x.singleton()) {
        return false;
      }
    }
    int q = initialState;
    long sum = 0;
    for (int i = 0; i < list.length; i++) {
      long j = (long) list[i].value() - firstValue;
      if (j < 0 || j >= transition[q].length || transition[q][(int) j] < 0) {
        return false;
      }
      sum += costs[i][q][(int) j];
      q = transition[q][(int) j];
    }
    for (int f : finalStates) {
      if (f == q) {
        return sum == cost.value();
      }
    }
    return false;
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }

  /**
   * It decomposes the constraint as MiniZinc does: a state variable per position, a table of the
   * transitions with their costs per variable and a sum of the transition costs.
   */
  @Override
  public List<Constraint> decompose(Store store) {

    int states = transition.length;
    int symbols = transition[0].length;
    List<Constraint> result = new ArrayList<>();

    IntVar[] q = new IntVar[list.length + 1];
    for (int i = 0; i < q.length; i++) {
      q[i] = new IntVar(store, "Q" + i, 0, states - 1);
    }
    IntVar[] w = new IntVar[list.length];
    for (int i = 0; i < list.length; i++) {
      List<int[]> tuples = new ArrayList<>();
      int lo = Integer.MAX_VALUE;
      int hi = Integer.MIN_VALUE;
      for (int s = 0; s < states; s++) {
        for (int j = 0; j < symbols; j++) {
          if (transition[s][j] >= 0) {
            int c = costs[i][s][j];
            tuples.add(new int[] {s, firstValue + j, transition[s][j], c});
            lo = Math.min(lo, c);
            hi = Math.max(hi, c);
          }
        }
      }
      if (tuples.isEmpty()) {
        lo = 0;
        hi = 0;
      }
      w[i] = new IntVar(store, "W" + i, lo, hi);
      result.add(
          new Table(new IntVar[] {q[i], list[i], q[i + 1], w[i]}, tuples.toArray(new int[0][])));
    }
    result.add(new XeqC(q[0], initialState));
    IntervalDomain accepting = new IntervalDomain();
    int[] sorted = finalStates.clone();
    Arrays.sort(sorted);
    for (int f : sorted) {
      accepting.unionAdapt(f, f);
    }
    result.add(new In(q[list.length], accepting));
    result.add(new SumInt(w, "==", cost));
    return result;
  }

  // explained by the costs of the paths, which are its whole semantics for itself and CostMdd
  private boolean explainedByPaths() {
    return (getClass() == CostRegular.class || getClass() == CostMdd.class) && edge != null;
  }

  private CostPathExplanation costPaths(AtomicTrail trail, int position) {
    int m = edgeStart[list.length];
    int[] source = new int[m];
    int[] target = new int[m];
    int[] label = new int[m];
    int[][] edgeCost = new int[1][m];
    for (int e = 0; e < m; e++) {
      source[e] = edge[4 * e];
      target[e] = edge[4 * e + 1];
      label[e] = slots.value(edge[4 * e + 2]);
      edgeCost[0][e] = edge[4 * e + 3];
    }
    return new CostPathExplanation(
        trail,
        position,
        list,
        levelNodeStart,
        edgeStart,
        source,
        target,
        label,
        edgeCost,
        new IntVar[] {cost});
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return explainedByPaths() && costPaths(trail, entry).explain(entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return explainedByPaths() && costPaths(trail, trail.size()).explainFailure(out);
  }

  @Override
  public String toString() {

    StringBuilder result =
        CostAutomatonGraph.describe(
            new StringBuilder(id()), list, transition, firstValue, initialState, finalStates);
    result.append(", cost=").append(cost.id()).append(")");
    return result.toString();
  }

  @Override
  public CostRegular copy(VarMap map) {
    return new CostRegular(
        map.get(list), transition, firstValue, initialState, finalStates, costs, map.get(cost));
  }
}
