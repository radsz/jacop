/*
 * MultiCostRegular.java
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
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
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
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * MultiCostRegular constraint (Menana and Demassey, "Sequencing and counting with the
 * multicost-regular constraint", CPAIOR 2009). The values of the variables in list must be a word
 * accepted by a deterministic finite automaton and, for every resource r, cost[r] must equal the
 * sum of the costs of resource r over the transitions taken. A transition cost depends on its
 * state, its value and, optionally, the position in the word. It is the conjunction of one {@link
 * CostRegular} per resource over the same automaton, filtered together.
 *
 * <p>The automaton is unfolded once into a layered graph whose edges carry one cost per resource.
 * Each consistency call first does, for every resource at once, the filtering of {@link
 * CostRegular}: shortest and longest paths from the source and to the sink, removal of the edges
 * through which every path is too expensive or too cheap for some resource, and the bounds of every
 * cost set to its shortest and longest path. This is already stronger than separate constraints: an
 * edge removed for one resource is gone for the paths of all the others, while each separate
 * constraint keeps it in its own graph as long as its value stays in the domain.
 *
 * <p>Optionally ({@link #setLagrangian(boolean)}, off by default) it also reasons on the resources
 * together as the paper does: a path can be within the bounds of every resource taken alone and
 * still violate two of them at once. Finding a path within all bounds is a resource constrained
 * shortest path problem, NP-hard, so as in the paper the side resources are relaxed in a Lagrangian
 * way. To bound resource k from below, the graph is weighted with c_k + sum over r != k of
 * (lambda_r - mu_r) c_r, where lambda_r and mu_r are nonnegative multipliers of the upper and the
 * lower bound of resource r. For every path P within all bounds, c_k(P) is at least its weight plus
 * the constant sum of (mu_r min(cost[r]) - lambda_r max(cost[r])), so the shortest weighted path
 * bounds cost[k] from below and an edge whose shortest weighted path is above max(cost[k]) is
 * removed. The upper bound of cost[k] is the same with c_k negated. The multipliers are improved by
 * a few subgradient steps with the Polyak step towards max(cost[k]) + 1 and are kept between calls,
 * so the search usually starts close to good multipliers. A resource whose bounds every path
 * satisfies is left out of the relaxation, so the relaxation runs only when some pair of resources
 * can conflict. On nurse rostering models the relaxation removed few more edges, cut the search by
 * a few percent and made a node up to ten times as expensive, hence it is not used unless asked
 * for.
 *
 * <p>The alive edges of each layer are kept at the front of their part of an edge permutation, a
 * sparse set whose size is trailed, so backtracking restores a layer in constant time.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class MultiCostRegular extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Copyable<MultiCostRegular> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final long INF = Long.MAX_VALUE / 4;
  private static final long NEG_INF = -INF;

  /** Subgradient steps of one relaxation in one consistency call. */
  private static final int LAGRANGIAN_STEPS = 10;

  /** Steps without improvement of the bound after which the step factor is halved. */
  private static final int STALL_STEPS = 2;

  /** Tolerance of the comparisons of relaxed path weights, which are sums of doubles. */
  private static final double EPS = 1e-6;

  /** The variables whose values form the word. */
  public final IntVar[] list;

  /** The total cost of the transitions for each resource. */
  public final IntVar[] cost;

  /** Successor of state q on value firstValue + j is transition[q][j], or -1 when there is none. */
  final int[][] transition;

  final int firstValue;

  final int initialState;

  final int[] finalStates;

  /**
   * Cost of resource r for the transition from state q on value firstValue + j at position i is
   * costs[r][i][q][j].
   */
  final int[][][][] costs;

  /** The number of resources. */
  private final int resources;

  /** Whether the Lagrangian relaxation of the side resources is used. */
  private boolean lagrangian;

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

  // Edge e goes from edgeSource[e] to edgeTarget[e] with the value of slot edgeSlot[e]; its cost
  // for resource r is edgeCost[e * resources + r]. The edges of level l are
  // order[edgeStart[l]..edgeStart[l+1]-1], the alive[l] alive ones first.
  private int[] edgeSource;
  private int[] edgeTarget;
  private int[] edgeSlot;
  private int[] edgeCost;
  private int[] order;
  private int[] edgeStart;
  private int[] alive;

  // Slots: the values labelling edges of level l are
  // slotValue[levelSlotStart[l]..levelSlotStart[l+1]-1].
  private int[] levelSlotStart;
  private int[] slotValue;

  // Paths per node and resource, at node * resources + r.
  private long[] forwardMin;
  private long[] forwardMax;
  private long[] backwardMin;
  private long[] backwardMax;

  // Relaxed paths per node and the edge into a node on its shortest relaxed path.
  private double[] forwardWeight;
  private double[] backwardWeight;
  private int[] forwardEdge;
  private double[] weight;

  /**
   * Multipliers of the relaxation bounding resource k from below (direction 0) or from above
   * (direction 1): the multiplier of the upper bound of resource r is upperMultiplier[2 * k +
   * direction][r] and of its lower bound lowerMultiplier[2 * k + direction][r].
   */
  private double[][] upperMultiplier;

  private double[][] lowerMultiplier;

  private boolean[] upperActive;
  private boolean[] lowerActive;
  private long[] pathCost;

  /** Stamp of the consistency call in which a slot lost its value. */
  private int[] slotRemoved;

  /** Stamp of the pass in which a slot was supported by an edge. */
  private int[] slotSupported;

  private int[] levelSupported;

  private int stamp;

  /**
   * True while the graph has not changed since the last call, which then left the costs with the
   * bounds in lastMin and lastMax; while they keep them there is nothing to prune.
   */
  private boolean stable;

  private int[] lastMin;
  private int[] lastMax;

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
   * It constructs a multi-cost regular constraint whose transition costs do not depend on the
   * position.
   *
   * @param list the variables whose values form the word, without duplicates.
   * @param transition the successor of state q on value firstValue + j is transition[q][j], -1 if
   *     there is no transition; states are numbered from 0.
   * @param firstValue the value of the first column of transition and costs.
   * @param initialState the initial state.
   * @param finalStates the accepting states.
   * @param costs the cost of resource r for the transition from state q on value firstValue + j is
   *     costs[r][q][j].
   * @param cost the variables equal to the sums of the costs of each resource.
   */
  public MultiCostRegular(
      IntVar[] list,
      int[][] transition,
      int firstValue,
      int initialState,
      int[] finalStates,
      int[][][] costs,
      IntVar[] cost) {
    this(list, transition, firstValue, initialState, finalStates, repeat(costs, list), cost);
  }

  /**
   * It constructs a multi-cost regular constraint whose transition costs depend on the position.
   *
   * @param list the variables whose values form the word, without duplicates.
   * @param transition the successor of state q on value firstValue + j is transition[q][j], -1 if
   *     there is no transition; states are numbered from 0.
   * @param firstValue the value of the first column of transition and costs.
   * @param initialState the initial state.
   * @param finalStates the accepting states.
   * @param costs the cost of resource r for the transition from state q on value firstValue + j
   *     taken by the i-th variable is costs[r][i][q][j].
   * @param cost the variables equal to the sums of the costs of each resource.
   */
  public MultiCostRegular(
      IntVar[] list,
      int[][] transition,
      int firstValue,
      int initialState,
      int[] finalStates,
      int[][][][] costs,
      IntVar[] cost) {

    checkInputForNullness(
        new String[] {"list", "transition", "finalStates", "costs", "cost"},
        new Object[][] {list, transition, {finalStates}, costs, cost});
    checkInputForDuplicationSkipSingletons("list", list);
    for (IntVar c : cost) {
      for (IntVar x : list) {
        if (x == c && !c.singleton()) {
          throw new IllegalArgumentException(
              "MultiCostRegular: a cost must not be one of the variables in list");
        }
      }
    }
    if (cost.length == 0) {
      throw new IllegalArgumentException("MultiCostRegular: there must be at least one resource");
    }
    if (costs.length != cost.length) {
      throw new IllegalArgumentException(
          "MultiCostRegular: costs must have one entry per cost variable");
    }

    int states = transition.length;
    if (states == 0) {
      throw new IllegalArgumentException("MultiCostRegular: the automaton has no states");
    }
    int symbols = transition[0] == null ? 0 : transition[0].length;
    if (initialState < 0 || initialState >= states) {
      throw new IllegalArgumentException(
          "MultiCostRegular: initial state " + initialState + " is not a state");
    }
    for (int q : finalStates) {
      if (q < 0 || q >= states) {
        throw new IllegalArgumentException(
            "MultiCostRegular: final state " + q + " is not a state");
      }
    }
    for (int[] row : transition) {
      if (row == null || row.length != symbols) {
        throw new IllegalArgumentException(
            "MultiCostRegular: transition rows must have equal lengths");
      }
      for (int t : row) {
        if (t < -1 || t >= states) {
          throw new IllegalArgumentException(
              "MultiCostRegular: transition to " + t + " is not a state");
        }
      }
    }
    for (int[][][] resource : costs) {
      if (resource == null || resource.length != list.length) {
        throw new IllegalArgumentException(
            "MultiCostRegular: costs must have one matrix per variable for each resource");
      }
      for (int[][] matrix : resource) {
        if (matrix == null || matrix.length != states) {
          throw new IllegalArgumentException("MultiCostRegular: costs must have a row per state");
        }
        for (int[] row : matrix) {
          if (row == null || row.length != symbols) {
            throw new IllegalArgumentException(
                "MultiCostRegular: costs must have a column per value");
          }
        }
      }
    }
    if ((long) firstValue + symbols - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException("MultiCostRegular: values out of range");
    }

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.cost = Arrays.copyOf(cost, cost.length);
    this.resources = cost.length;
    this.transition = transition;
    this.firstValue = firstValue;
    this.initialState = initialState;
    this.finalStates = Arrays.copyOf(finalStates, finalStates.length);
    this.costs = costs;

    setScope(Stream.concat(Arrays.stream(list), Arrays.stream(cost)));
  }

  private static int[][][][] repeat(int[][][] costs, IntVar[] list) {
    if (list == null || costs == null) {
      throw new IllegalArgumentException("MultiCostRegular: list or costs is null");
    }
    int[][][][] result = new int[costs.length][list.length][][];
    for (int r = 0; r < costs.length; r++) {
      Arrays.fill(result[r], costs[r]);
    }
    return result;
  }

  /**
   * It replaces the cost regular constraints over the same variables and the same automaton by one
   * multi-cost regular constraint each, at the position of the first of them; the other constraints
   * keep their order.
   *
   * @param constraints the constraints to merge.
   * @return the constraints with each group of at least two cost regular constraints merged.
   */
  public static List<Constraint> merge(List<Constraint> constraints) {
    Map<List<Object>, List<CostRegular>> groups = new LinkedHashMap<>();
    for (Constraint c : constraints) {
      if (c instanceof CostRegular cr) {
        groups.computeIfAbsent(key(cr), k -> new ArrayList<>()).add(cr);
      }
    }
    Map<CostRegular, Constraint> first = new IdentityHashMap<>();
    for (List<CostRegular> group : groups.values()) {
      if (group.size() < 2) {
        continue;
      }
      CostRegular c = group.get(0);
      int[][][][] costs = new int[group.size()][][][];
      IntVar[] cost = new IntVar[group.size()];
      for (int r = 0; r < costs.length; r++) {
        costs[r] = group.get(r).costs;
        cost[r] = group.get(r).cost;
      }
      first.put(
          c,
          new MultiCostRegular(
              c.list, c.transition, c.firstValue, c.initialState, c.finalStates, costs, cost));
      for (int r = 1; r < group.size(); r++) {
        first.put(group.get(r), null);
      }
    }
    if (first.isEmpty()) {
      return constraints;
    }
    List<Constraint> result = new ArrayList<>(constraints.size());
    for (Constraint c : constraints) {
      if (!first.containsKey(c)) {
        result.add(c);
      } else if (first.get(c) != null) {
        result.add(first.get(c));
      }
    }
    return result;
  }

  private static List<Object> key(CostRegular c) {
    int[] finals = c.finalStates.clone();
    Arrays.sort(finals);
    List<Object> key = new ArrayList<>();
    key.add(c.firstValue);
    key.add(c.initialState);
    key.add(Arrays.stream(finals).boxed().toList());
    key.add(Arrays.stream(c.transition).map(row -> Arrays.stream(row).boxed().toList()).toList());
    key.add(Arrays.stream(c.list).map(IdentityKey::new).toList());
    return key;
  }

  /** A variable compared by identity. */
  private record IdentityKey(IntVar var) {
    @Override
    public boolean equals(Object o) {
      return o instanceof IdentityKey k && k.var == var;
    }

    @Override
    public int hashCode() {
      return System.identityHashCode(var);
    }
  }

  /**
   * It switches the Lagrangian relaxation of the side resources on or off (off by default). Without
   * it the constraint prunes as one {@link CostRegular} per resource on a single shared graph.
   *
   * @param lagrangian true to reason on the resources together.
   * @return this constraint.
   */
  public MultiCostRegular setLagrangian(boolean lagrangian) {
    this.lagrangian = lagrangian;
    return this;
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
    int[] sources = new int[16];
    int[] targets = new int[16];
    int[] edgeSlots = new int[16];
    int[] edgeCosts = new int[16 * resources];
    int edgeCount = 0;
    int[] slots = new int[16];
    int slotCount = 0;
    int[] slotOf = new int[symbols];
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
      for (int i = 0; i < kept[level].length; i++) {
        int q = kept[level][i];
        for (int j : values[level]) {
          int t = transition[q][j];
          if (t < 0 || position[t] < 0) {
            continue;
          }
          if (edgeCount == sources.length) {
            sources = Arrays.copyOf(sources, 2 * edgeCount);
            targets = Arrays.copyOf(targets, 2 * edgeCount);
            edgeSlots = Arrays.copyOf(edgeSlots, 2 * edgeCount);
            edgeCosts = Arrays.copyOf(edgeCosts, 2 * edgeCount * resources);
          }
          sources[edgeCount] = levelNodeStart[level] + i;
          targets[edgeCount] = levelNodeStart[level + 1] + position[t];
          edgeSlots[edgeCount] = slotOf[j];
          for (int r = 0; r < resources; r++) {
            edgeCosts[edgeCount * resources + r] = costs[r][level][q][j];
          }
          edgeCount++;
        }
      }
      for (int t : kept[level + 1]) {
        position[t] = -1;
      }
    }
    edgeStart[levels] = edgeCount;
    levelSlotStart[levels] = slotCount;

    edgeSource = Arrays.copyOf(sources, edgeCount);
    edgeTarget = Arrays.copyOf(targets, edgeCount);
    edgeSlot = Arrays.copyOf(edgeSlots, edgeCount);
    edgeCost = Arrays.copyOf(edgeCosts, edgeCount * resources);
    order = new int[edgeCount];
    for (int e = 0; e < edgeCount; e++) {
      order[e] = e;
    }
    slotValue = Arrays.copyOf(slots, slotCount);
    alive = new int[levels];
    for (int level = 0; level < levels; level++) {
      alive[level] = edgeStart[level + 1] - edgeStart[level];
    }
    savedEpoch = new int[levels];
    forwardMin = new long[nodes * resources];
    forwardMax = new long[nodes * resources];
    backwardMin = new long[nodes * resources];
    backwardMax = new long[nodes * resources];
    forwardWeight = new double[nodes];
    backwardWeight = new double[nodes];
    forwardEdge = new int[nodes];
    weight = new double[edgeCount];
    upperMultiplier = new double[2 * resources][resources];
    lowerMultiplier = new double[2 * resources][resources];
    upperActive = new boolean[resources];
    lowerActive = new boolean[resources];
    pathCost = new long[resources];
    lastMin = new int[resources];
    lastMax = new int[resources];
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

  private void swap(int i, int j) {
    int t = order[i];
    order[i] = order[j];
    order[j] = t;
  }

  private int nextStamp() {
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(slotRemoved, 0);
      Arrays.fill(slotSupported, 0);
      stamp = 1;
    }
    return stamp;
  }

  private boolean costsUnchanged() {
    for (int r = 0; r < resources; r++) {
      if (cost[r].min() != lastMin[r] || cost[r].max() != lastMax[r]) {
        return false;
      }
    }
    return true;
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
      // the graph was built at impose; values removed since then must be checked on every level
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
      for (IntVar c : cost) {
        c.domain.in(store.level, c, 0, 0);
      }
      return;
    }

    if (stable && levelQueueSize == 0 && costsUnchanged()) {
      return;
    }

    int removedStamp = nextStamp();
    for (int i = 0; i < levelQueueSize; i++) {
      int level = levelQueue[i];
      levelQueued[level] = false;
      IntDomain dom = list[level].domain;
      for (int s = levelSlotStart[level]; s < levelSlotStart[level + 1]; s++) {
        if (!dom.contains(slotValue[s])) {
          slotRemoved[s] = removedStamp;
        }
      }
    }
    levelQueueSize = 0;

    pruning = true;
    try {
      boolean changed = true;
      boolean first = true;
      int rounds = 0;
      while (changed) {
        do {
          forwardPass(first ? removedStamp : -1);
          first = false;
        } while (backwardPass(store));
        changed = lagrangian && resources > 1 && rounds++ < 3 && relax(store);
      }

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

    stable = true;
    for (int r = 0; r < resources; r++) {
      lastMin[r] = cost[r].min();
      lastMax[r] = cost[r].max();
    }
  }

  /**
   * It computes for every resource the shortest and longest paths from the source to every node
   * over the alive edges and removes edges whose source is not reached or whose value was removed
   * in the given stamp.
   */
  private void forwardPass(int removedStamp) {
    final int rs = resources;
    final long[] fMin = forwardMin;
    final long[] fMax = forwardMax;
    final int[] c = edgeCost;
    for (int r = 0; r < rs; r++) {
      fMin[r] = 0;
      fMax[r] = 0;
    }
    int levels = list.length;
    for (int level = 0; level < levels; level++) {
      Arrays.fill(fMin, levelNodeStart[level + 1] * rs, levelNodeStart[level + 2] * rs, INF);
      Arrays.fill(fMax, levelNodeStart[level + 1] * rs, levelNodeStart[level + 2] * rs, NEG_INF);
      int start = edgeStart[level];
      int end = start + alive[level];
      int i = start;
      while (i < end) {
        int e = order[i];
        int u = edgeSource[e] * rs;
        if (fMin[u] == INF || slotRemoved[edgeSlot[e]] == removedStamp) {
          swap(i, --end);
          continue;
        }
        int v = edgeTarget[e] * rs;
        int ce = e * rs;
        for (int r = 0; r < rs; r++) {
          long a = fMin[u + r] + c[ce + r];
          if (a < fMin[v + r]) {
            fMin[v + r] = a;
          }
          long b = fMax[u + r] + c[ce + r];
          if (b > fMax[v + r]) {
            fMax[v + r] = b;
          }
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
   * It computes for every resource the shortest and longest paths from every node to the sink,
   * removes the edges that lead to no path or through which every path is outside the bounds of
   * some cost, marks the values with an alive edge and narrows each cost to its shortest and
   * longest path.
   *
   * @return true if an edge was removed or a cost bound moved, so another pass may prune more.
   */
  private boolean backwardPass(Store store) {
    final int rs = resources;
    final long[] fMin = forwardMin;
    final long[] fMax = forwardMax;
    final long[] bMin = backwardMin;
    final long[] bMax = backwardMax;
    final int[] c = edgeCost;
    final int[] supported = slotSupported;
    final int support = nextStamp();
    final long[] costMin = new long[rs];
    final long[] costMax = new long[rs];
    for (int r = 0; r < rs; r++) {
      costMin[r] = cost[r].min();
      costMax[r] = cost[r].max();
    }
    boolean removed = false;
    int levels = list.length;
    Arrays.fill(bMin, levelNodeStart[levels] * rs, levelNodeStart[levels + 1] * rs, 0);
    Arrays.fill(bMax, levelNodeStart[levels] * rs, levelNodeStart[levels + 1] * rs, 0);
    for (int level = levels - 1; level >= 0; level--) {
      Arrays.fill(bMin, levelNodeStart[level] * rs, levelNodeStart[level + 1] * rs, INF);
      Arrays.fill(bMax, levelNodeStart[level] * rs, levelNodeStart[level + 1] * rs, NEG_INF);
      int start = edgeStart[level];
      int end = start + alive[level];
      int count = 0;
      int i = start;
      edges:
      while (i < end) {
        int e = order[i];
        int v = edgeTarget[e] * rs;
        if (bMin[v] == INF) {
          swap(i, --end);
          removed = true;
          continue;
        }
        int u = edgeSource[e] * rs;
        int ce = e * rs;
        for (int r = 0; r < rs; r++) {
          if (fMin[u + r] + c[ce + r] + bMin[v + r] > costMax[r]
              || fMax[u + r] + c[ce + r] + bMax[v + r] < costMin[r]) {
            swap(i, --end);
            removed = true;
            continue edges;
          }
        }
        for (int r = 0; r < rs; r++) {
          long a = c[ce + r] + bMin[v + r];
          if (a < bMin[u + r]) {
            bMin[u + r] = a;
          }
          long b = c[ce + r] + bMax[v + r];
          if (b > bMax[u + r]) {
            bMax[u + r] = b;
          }
        }
        int s = edgeSlot[e];
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

    boolean moved = false;
    for (int r = 0; r < rs; r++) {
      long shortest = bMin[r];
      long longest = bMax[r];
      if (shortest > IntDomain.MAX_INT || longest < IntDomain.MIN_INT) {
        throw Store.failException;
      }
      if (shortest > costMin[r] || longest < costMax[r]) {
        cost[r].domain.in(
            store.level,
            cost[r],
            (int) Math.max(shortest, IntDomain.MIN_INT),
            (int) Math.min(longest, IntDomain.MAX_INT));
        // the bounds may only have moved to path costs, which remove no edge, unless the domain
        // had holes at the path costs
        if (cost[r].min() > shortest || cost[r].max() < longest) {
          moved = true;
        }
      }
    }
    return removed || moved;
  }

  /**
   * It runs the Lagrangian relaxations of the side resources for the bounds of every resource.
   *
   * @return true if an edge was removed or a cost bound moved.
   */
  private boolean relax(Store store) {
    final int rs = resources;
    final int root = 0;
    // a side resource whose bound no path violates takes no part in the relaxation
    int active = 0;
    for (int r = 0; r < rs; r++) {
      upperActive[r] = backwardMax[root * rs + r] > cost[r].max();
      lowerActive[r] = backwardMin[root * rs + r] < cost[r].min();
      if (upperActive[r] || lowerActive[r]) {
        active++;
      }
    }
    if (active == 0) {
      return false;
    }
    boolean changed = false;
    for (int k = 0; k < rs; k++) {
      int sides = active - (upperActive[k] || lowerActive[k] ? 1 : 0);
      if (sides == 0) {
        continue;
      }
      changed |= relax(store, k, 1);
      changed |= relax(store, k, -1);
    }
    return changed;
  }

  /**
   * It bounds cost[k] from below (sign 1) or from above (sign -1) by the Lagrangian relaxation of
   * the bounds of the other resources and removes the edges through which no path within the bounds
   * of the other resources is within the bounds of cost[k].
   */
  private boolean relax(Store store, int k, int sign) {
    final int rs = resources;
    final int levels = list.length;
    final int[] c = edgeCost;
    final double[] up = upperMultiplier[2 * k + (sign > 0 ? 0 : 1)];
    final double[] low = lowerMultiplier[2 * k + (sign > 0 ? 0 : 1)];
    final double[] f = forwardWeight;
    final double[] b = backwardWeight;
    final double[] w = weight;
    boolean changed = false;
    double best = Double.NEGATIVE_INFINITY;
    double factor = 1.0;
    int stall = 0;
    for (int r = 0; r < rs; r++) {
      if (!upperActive[r] || r == k) {
        up[r] = 0;
      }
      if (!lowerActive[r] || r == k) {
        low[r] = 0;
      }
    }

    for (int step = 0; step < LAGRANGIAN_STEPS; step++) {
      // bounds of the objective sign * c_k
      double objectiveMax = sign > 0 ? cost[k].max() : -(double) cost[k].min();
      double objectiveMin = sign > 0 ? cost[k].min() : -(double) cost[k].max();
      double constant = 0;
      for (int r = 0; r < rs; r++) {
        constant += low[r] * cost[r].min() - up[r] * cost[r].max();
      }

      boolean weighted = false;
      for (int r = 0; r < rs; r++) {
        weighted |= up[r] != 0 || low[r] != 0;
      }

      // weights and the shortest weighted paths from the source
      f[0] = 0;
      for (int level = 0; level < levels; level++) {
        Arrays.fill(f, levelNodeStart[level + 1], levelNodeStart[level + 2], Double.MAX_VALUE);
        int end = edgeStart[level] + alive[level];
        for (int i = edgeStart[level]; i < end; i++) {
          int e = order[i];
          int ce = e * rs;
          double we = sign * c[ce + k];
          for (int r = 0; r < rs; r++) {
            double m = up[r] - low[r];
            if (m != 0) {
              we += m * c[ce + r];
            }
          }
          w[e] = we;
          double a = f[edgeSource[e]];
          if (a != Double.MAX_VALUE && a + we < f[edgeTarget[e]]) {
            f[edgeTarget[e]] = a + we;
            forwardEdge[edgeTarget[e]] = e;
          }
        }
      }
      int sink = -1;
      double shortest = Double.MAX_VALUE;
      for (int n = levelNodeStart[levels]; n < levelNodeStart[levels + 1]; n++) {
        if (f[n] < shortest) {
          shortest = f[n];
          sink = n;
        }
      }
      if (sink < 0) {
        throw Store.failException;
      }
      double bound = shortest + constant;
      if (bound > objectiveMax + tolerance(objectiveMax)) {
        throw Store.failException;
      }

      // the shortest weighted paths to the sink and the edges they make too expensive; without
      // multipliers these are the edges the paths of resource k already removed
      if (weighted) {
        Arrays.fill(b, levelNodeStart[levels], levelNodeStart[levels + 1], 0);
        double limit = objectiveMax - constant + tolerance(objectiveMax);
        for (int level = levels - 1; level >= 0; level--) {
          Arrays.fill(b, levelNodeStart[level], levelNodeStart[level + 1], Double.MAX_VALUE);
          int start = edgeStart[level];
          int end = start + alive[level];
          int i = start;
          while (i < end) {
            int e = order[i];
            double to = b[edgeTarget[e]];
            double from = f[edgeSource[e]];
            if (to == Double.MAX_VALUE || from == Double.MAX_VALUE) {
              // left for the next pass of the paths of the resources
              i++;
              continue;
            }
            if (from + w[e] + to > limit) {
              swap(i, --end);
              changed = true;
              continue;
            }
            if (w[e] + to < b[edgeSource[e]]) {
              b[edgeSource[e]] = w[e] + to;
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

      double rounded = Math.ceil(bound - tolerance(bound));
      if (rounded > objectiveMin) {
        if (sign > 0) {
          cost[k].domain.inMin(store.level, cost[k], (int) Math.min(rounded, IntDomain.MAX_INT));
        } else {
          cost[k].domain.inMax(store.level, cost[k], (int) Math.max(-rounded, IntDomain.MIN_INT));
        }
        changed = true;
      }

      // subgradient at the shortest path
      Arrays.fill(pathCost, 0);
      for (int n = sink; n != 0; ) {
        int e = forwardEdge[n];
        for (int r = 0; r < rs; r++) {
          pathCost[r] += c[e * rs + r];
        }
        n = edgeSource[e];
      }
      double norm = 0;
      boolean feasible = true;
      for (int r = 0; r < rs; r++) {
        if (r == k) {
          continue;
        }
        if (upperActive[r]) {
          double g = pathCost[r] - cost[r].max();
          if (g > 0) {
            feasible = false;
          }
          if (g > 0 || up[r] > 0) {
            norm += g * g;
          }
        }
        if (lowerActive[r]) {
          double g = cost[r].min() - pathCost[r];
          if (g > 0) {
            feasible = false;
          }
          if (g > 0 || low[r] > 0) {
            norm += g * g;
          }
        }
      }
      if (feasible && sign * pathCost[k] - bound < 1 - EPS) {
        // the best path within all bounds is found and proven
        break;
      }
      if (norm == 0) {
        break;
      }
      if (bound > best + EPS) {
        best = bound;
        stall = 0;
      } else if (++stall >= STALL_STEPS) {
        factor /= 2;
        stall = 0;
      }
      double gap = Math.max(objectiveMax + 1 - bound, 1);
      double size = factor * gap / norm;
      for (int r = 0; r < rs; r++) {
        if (r == k) {
          continue;
        }
        if (upperActive[r]) {
          up[r] = Math.max(0, up[r] + size * (pathCost[r] - cost[r].max()));
        }
        if (lowerActive[r]) {
          low[r] = Math.max(0, low[r] + size * (cost[r].min() - pathCost[r]));
        }
      }
    }
    return changed;
  }

  private static double tolerance(double value) {
    return EPS * Math.max(1, Math.abs(value));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    for (IntVar c : cost) {
      if (v == c) {
        Integer event = getConsistencyPruningEventFromMap(v);
        return event != null ? event : IntDomain.BOUND;
      }
    }
    return super.getConsistencyPruningEvent(v);
  }

  @Override
  public boolean satisfied() {
    for (IntVar c : cost) {
      if (!c.singleton()) {
        return false;
      }
    }
    for (IntVar x : list) {
      if (!x.singleton()) {
        return false;
      }
    }
    int q = initialState;
    long[] sum = new long[resources];
    for (int i = 0; i < list.length; i++) {
      long j = (long) list[i].value() - firstValue;
      if (j < 0 || j >= transition[q].length || transition[q][(int) j] < 0) {
        return false;
      }
      for (int r = 0; r < resources; r++) {
        sum[r] += costs[r][i][q][(int) j];
      }
      q = transition[q][(int) j];
    }
    for (int f : finalStates) {
      if (f == q) {
        for (int r = 0; r < resources; r++) {
          if (sum[r] != cost[r].value()) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  @Override
  public void imposeDecomposition(Store store) {
    for (Constraint c : decompose(store)) {
      store.impose(c, queueIndex);
    }
  }

  /** It decomposes the constraint into one {@link CostRegular} per resource. */
  @Override
  public List<Constraint> decompose(Store store) {
    List<Constraint> result = new ArrayList<>();
    for (int r = 0; r < resources; r++) {
      result.add(
          new CostRegular(
              list, transition, firstValue, initialState, finalStates, costs[r], cost[r]));
    }
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
    result.append(", cost=[");
    for (int r = 0; r < resources; r++) {
      result.append(cost[r].id()).append(r + 1 < resources ? ", " : "");
    }
    result.append("])");
    return result.toString();
  }

  @Override
  public MultiCostRegular copy(VarMap map) {
    return new MultiCostRegular(
            map.get(list), transition, firstValue, initialState, finalStates, costs, map.get(cost))
        .setLagrangian(lagrangian);
  }
}
