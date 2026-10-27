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
import java.util.Map;
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
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Copyable<CostRegular> {

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

  private Map<IntVar, Integer> mapping;

  /** One-time work of the first consistency call. */
  private final InitOnce init = new InitOnce();

  /** Set while this constraint prunes domains, so its own changes are not queued again. */
  private boolean pruning;

  private int[] levelQueue;
  private int levelQueueSize;
  private boolean[] levelQueued;

  // Nodes of level l are levelNodeStart[l]..levelNodeStart[l+1]-1; node 0 is the source.
  private int[] levelNodeStart;

  // Edges of level l are at positions edgeStart[l]..edgeStart[l+1]-1, the alive[l] alive ones
  // first. Each edge takes four ints: source, target, slot and cost.
  private int[] edgeStart;
  private int[] edge;
  private int[] alive;

  // Slots: the values labelling edges of level l are
  // slotValue[levelSlotStart[l]..levelSlotStart[l+1]-1].
  private int[] levelSlotStart;
  private int[] slotValue;

  private long[] forwardMin;
  private long[] forwardMax;
  private long[] backwardMin;
  private long[] backwardMax;

  /** Stamp of the consistency call in which a slot lost its value. */
  private int[] slotRemoved;

  /** Stamp of the pass in which a slot was supported by an edge. */
  private int[] slotSupported;

  private int[] levelSupported;

  private int stamp;

  /**
   * True while the graph has not changed since the last pass, which then left every alive edge with
   * a shortest path through it of at most lastMaxShortest and a longest path through it of at least
   * lastMinLongest; until cost passes these bounds there is nothing to prune.
   */
  private boolean stable;

  private long lastMaxShortest;
  private long lastMinLongest;

  /** The size of the domain of cost at the last pass; a new hole may remove edges. */
  private int lastCostSize;

  private static boolean isInterval(IntVar v) {
    return v.max() - v.min() + 1 == v.getSize();
  }

  // Trail of alive counts: pairs of level and previous count, with a mark per store level.
  private int[] savedEpoch;
  private int epoch;
  private int epochLevel = -1;
  private int currentLevel;
  private int[] trail = new int[64];
  private int trailTop;
  private int[] markLevel = new int[16];
  private int[] markPosition = new int[16];
  private int markTop;

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

    int states = transition.length;
    int symbols = states == 0 ? 0 : transition[0].length;
    if (states == 0) {
      throw new IllegalArgumentException("CostRegular: the automaton has no states");
    }
    if (initialState < 0 || initialState >= states) {
      throw new IllegalArgumentException(
          "CostRegular: initial state " + initialState + " is not a state");
    }
    for (int q : finalStates) {
      if (q < 0 || q >= states) {
        throw new IllegalArgumentException("CostRegular: final state " + q + " is not a state");
      }
    }
    for (int[] row : transition) {
      if (row == null || row.length != symbols) {
        throw new IllegalArgumentException("CostRegular: transition rows must have equal lengths");
      }
      for (int t : row) {
        if (t < -1 || t >= states) {
          throw new IllegalArgumentException("CostRegular: transition to " + t + " is not a state");
        }
      }
    }
    if (costs.length != list.length) {
      throw new IllegalArgumentException("CostRegular: costs must have one matrix per variable");
    }
    for (int[][] matrix : costs) {
      if (matrix == null || matrix.length != states) {
        throw new IllegalArgumentException("CostRegular: costs must have a row per state");
      }
      for (int[] row : matrix) {
        if (row == null || row.length != symbols) {
          throw new IllegalArgumentException("CostRegular: costs must have a column per value");
        }
      }
    }
    if ((long) firstValue + symbols - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException("CostRegular: values out of range");
    }

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

  private static int[][][] repeat(int[][] costs, IntVar[] list) {
    if (list == null) {
      throw new IllegalArgumentException("CostRegular: list is null");
    }
    int[][][] result = new int[list.length][][];
    Arrays.fill(result, costs);
    return result;
  }

  /**
   * It unfolds the automaton into the layered graph. A forward pass collects the states reachable
   * at each level, a backward pass keeps the states from which a final state can be reached, and
   * the edges between kept states are created level by level.
   */
  private void buildGraph() {
    int levels = list.length;
    int states = transition.length;
    int symbols = transition[0].length;

    boolean[] accepting = new boolean[states];
    for (int q : finalStates) {
      accepting[q] = true;
    }

    // Values of each level that are in the domain and in the alphabet.
    int[][] values = new int[levels][];
    for (int level = 0; level < levels; level++) {
      IntDomain dom = list[level].dom();
      int[] buffer = new int[Math.max(0, Math.min(dom.getSize(), symbols))];
      int count = 0;
      for (var e = dom.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        if (v >= firstValue && (long) v - firstValue < symbols) {
          buffer[count++] = v - firstValue;
        }
      }
      values[level] = Arrays.copyOf(buffer, count);
    }

    // Forward pass: states reachable at each level.
    int[][] reachable = new int[levels + 1][];
    boolean[] marked = new boolean[states];
    int[] buffer = new int[states];
    reachable[0] = new int[] {initialState};
    for (int level = 0; level < levels; level++) {
      int count = 0;
      for (int q : reachable[level]) {
        for (int j : values[level]) {
          int t = transition[q][j];
          if (t >= 0 && !marked[t] && (level < levels - 1 || accepting[t])) {
            marked[t] = true;
            buffer[count++] = t;
          }
        }
      }
      reachable[level + 1] = Arrays.copyOf(buffer, count);
      for (int i = 0; i < count; i++) {
        marked[buffer[i]] = false;
      }
    }
    if (levels == 0 && !accepting[initialState]) {
      reachable[0] = new int[0];
    }

    // Backward pass: keep the states with a transition to a kept state of the next level.
    int[][] kept = new int[levels + 1][];
    kept[levels] = reachable[levels];
    int[] position = new int[states];
    Arrays.fill(position, -1);
    for (int level = levels - 1; level >= 0; level--) {
      for (int i = 0; i < kept[level + 1].length; i++) {
        position[kept[level + 1][i]] = i;
      }
      int count = 0;
      for (int q : reachable[level]) {
        for (int j : values[level]) {
          int t = transition[q][j];
          if (t >= 0 && position[t] >= 0) {
            buffer[count++] = q;
            break;
          }
        }
      }
      kept[level] = Arrays.copyOf(buffer, count);
      for (int t : kept[level + 1]) {
        position[t] = -1;
      }
    }

    levelNodeStart = new int[levels + 2];
    for (int level = 0; level <= levels; level++) {
      levelNodeStart[level + 1] = levelNodeStart[level] + kept[level].length;
    }
    int nodes = levelNodeStart[levels + 1];

    // Edges and slots, level by level.
    edgeStart = new int[levels + 1];
    levelSlotStart = new int[levels + 1];
    int[] edges = new int[64];
    int edgeCount = 0;
    int[] slots = new int[16];
    int slotCount = 0;
    int[] slotOf = new int[symbols];
    int[] sourcePosition = new int[states];
    Arrays.fill(sourcePosition, -1);
    for (int level = 0; level < levels; level++) {
      edgeStart[level] = edgeCount;
      levelSlotStart[level] = slotCount;
      for (int i = 0; i < kept[level + 1].length; i++) {
        position[kept[level + 1][i]] = i;
      }
      Arrays.fill(slotOf, -1);
      // Slots in increasing order of values.
      for (int j : values[level]) {
        boolean used = false;
        for (int q : kept[level]) {
          int t = transition[q][j];
          if (t >= 0 && position[t] >= 0) {
            used = true;
            break;
          }
        }
        if (used) {
          if (slotCount == slots.length) {
            slots = Arrays.copyOf(slots, 2 * slotCount);
          }
          slotOf[j] = slotCount;
          slots[slotCount++] = firstValue + j;
        }
      }
      int[][] costMatrix = costs[level];
      for (int i = 0; i < kept[level].length; i++) {
        int q = kept[level][i];
        int source = levelNodeStart[level] + i;
        for (int j : values[level]) {
          int t = transition[q][j];
          if (t < 0 || position[t] < 0) {
            continue;
          }
          if (4 * edgeCount + 4 > edges.length) {
            edges = Arrays.copyOf(edges, 2 * edges.length);
          }
          edges[4 * edgeCount] = source;
          edges[4 * edgeCount + 1] = levelNodeStart[level + 1] + position[t];
          edges[4 * edgeCount + 2] = slotOf[j];
          edges[4 * edgeCount + 3] = costMatrix[q][j];
          edgeCount++;
        }
      }
      for (int t : kept[level + 1]) {
        position[t] = -1;
      }
    }
    edgeStart[levels] = edgeCount;
    levelSlotStart[levels] = slotCount;

    edge = Arrays.copyOf(edges, 4 * edgeCount);
    slotValue = Arrays.copyOf(slots, slotCount);
    alive = new int[levels];
    for (int level = 0; level < levels; level++) {
      alive[level] = edgeStart[level + 1] - edgeStart[level];
    }
    savedEpoch = new int[levels];
    forwardMin = new long[nodes];
    forwardMax = new long[nodes];
    backwardMin = new long[nodes];
    backwardMax = new long[nodes];
    slotRemoved = new int[slotCount];
    slotSupported = new int[slotCount];
    levelSupported = new int[levels];
  }

  @Override
  public void impose(Store store) {

    buildGraph();

    mapping = Var.positionMapping(list, true, this.getClass());
    levelQueue = new int[list.length];
    levelQueued = new boolean[list.length];

    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var v) {

    if (pruning) {
      return;
    }
    Integer p = mapping.get(v);
    if (p != null && !levelQueued[p]) {
      levelQueued[p] = true;
      levelQueue[levelQueueSize++] = p;
    }
  }

  @Override
  public void removeLevel(int level) {

    while (markTop > 0 && markLevel[markTop - 1] >= level) {
      int start = markPosition[--markTop];
      while (trailTop > start) {
        trailTop -= 2;
        alive[trail[trailTop]] = trail[trailTop + 1];
      }
    }
    epochLevel = -1;
    stable = false;
    for (int i = 0; i < levelQueueSize; i++) {
      levelQueued[levelQueue[i]] = false;
    }
    levelQueueSize = 0;
  }

  /** It sets the number of alive edges of a level, trailing the previous number. */
  private void setAlive(int level, int count) {
    if (savedEpoch[level] != epoch) {
      savedEpoch[level] = epoch;
      if (markTop == 0 || markLevel[markTop - 1] != currentLevel) {
        if (markTop == markLevel.length) {
          markLevel = Arrays.copyOf(markLevel, 2 * markTop);
          markPosition = Arrays.copyOf(markPosition, 2 * markTop);
        }
        markLevel[markTop] = currentLevel;
        markPosition[markTop++] = trailTop;
      }
      if (trailTop + 2 > trail.length) {
        trail = Arrays.copyOf(trail, 2 * trail.length);
      }
      trail[trailTop] = level;
      trail[trailTop + 1] = alive[level];
      trailTop += 2;
    }
    alive[level] = count;
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

  private int nextStamp() {
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(slotRemoved, 0);
      Arrays.fill(slotSupported, 0);
      stamp = 1;
    }
    return stamp;
  }

  @Override
  public void consistency(Store store) {

    currentLevel = store.level;
    if (epochLevel != currentLevel) {
      if (++epoch == Integer.MAX_VALUE) {
        Arrays.fill(savedEpoch, 0);
        epoch = 1;
      }
      epochLevel = currentLevel;
    }

    int levels = list.length;
    if (init.begin(store)) {
      pruning = true;
      try {
        for (int level = 0; level < levels; level++) {
          IntervalDomain labels = new IntervalDomain();
          for (int s = levelSlotStart[level]; s < levelSlotStart[level + 1]; s++) {
            labels.unionAdapt(slotValue[s], slotValue[s]);
          }
          list[level].domain.in(store.level, list[level], labels);
        }
      } finally {
        pruning = false;
      }
      // the graph was built at impose; values removed since then (also before this call, while
      // the queue was not yet read) must be checked on every level
      for (int level = 0; level < levels; level++) {
        if (!levelQueued[level]) {
          levelQueued[level] = true;
          levelQueue[levelQueueSize++] = level;
        }
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
        && levelQueueSize == 0
        && cost.max() >= lastMaxShortest
        && cost.min() <= lastMinLongest
        && (cost.getSize() == lastCostSize || isInterval(cost))) {
      return;
    }

    // Slots of the changed levels whose values were removed.
    // The paths from the source stay valid below the first level that lost an edge, unless the
    // search backtracked since they were computed.
    int removedStamp = nextStamp();
    int from = levels;
    for (int i = 0; i < levelQueueSize; i++) {
      int level = levelQueue[i];
      levelQueued[level] = false;
      IntDomain dom = list[level].domain;
      for (int s = levelSlotStart[level]; s < levelSlotStart[level + 1]; s++) {
        if (!dom.contains(slotValue[s])) {
          slotRemoved[s] = removedStamp;
          from = Math.min(from, level);
        }
      }
    }
    levelQueueSize = 0;
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
      int supported = stamp;
      for (int level = 0; level < levels; level++) {
        IntVar x = list[level];
        if (levelSupported[level] == x.getSize()) {
          continue;
        }
        for (int s = levelSlotStart[level]; s < levelSlotStart[level + 1]; s++) {
          if (slotSupported[s] != supported && x.domain.contains(slotValue[s])) {
            x.domain.inComplement(store.level, x, slotValue[s]);
          }
        }
      }
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
        setAlive(level, end - start);
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
    final int support = nextStamp();
    final long costMin = cost.min();
    final long costMax = cost.max();
    final IntDomain holes = isInterval(cost) ? null : cost.dom();
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
        if (shortest > costMax
            || longest < costMin
            || (holes != null
                && !holes.isIntersecting(
                    (int) Math.max(shortest, costMin), (int) Math.min(longest, costMax)))) {
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
        setAlive(level, end - start);
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
    lastCostSize = cost.getSize();
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
      return event != null ? event : IntDomain.ANY;
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

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append("([");
    for (int i = 0; i < list.length; i++) {
      result.append(list[i].id()).append(i + 1 < list.length ? ", " : "");
    }
    result.append("], transition=").append(Arrays.deepToString(transition));
    result.append(", firstValue=").append(firstValue);
    result.append(", initialState=").append(initialState);
    result.append(", finalStates=").append(Arrays.toString(finalStates));
    result.append(", cost=").append(cost.id()).append(")");
    return result.toString();
  }

  @Override
  public CostRegular copy(VarMap map) {
    return new CostRegular(
        map.get(list), transition, firstValue, initialState, finalStates, costs, map.get(cost));
  }
}
