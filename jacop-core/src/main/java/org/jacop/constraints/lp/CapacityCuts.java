/*
 * CapacityCuts.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.jacop.api.VarMap;
import org.jacop.constraints.Routes;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * Rounded capacity cuts of a {@link Routes}: for a set S of nodes that every route must visit
 * (nodes other than the depot without a self loop that can be 1), the routes enter S at least
 * {@code k(S) = max(1, ceil(d(S) / Q))} times, where d(S) is the demand of S and Q the capacity of
 * a route. As each node of S has exactly one incoming arc, this is also {@code x(A(S)) <= |S| -
 * k(S)} over the arcs inside S; the shorter of the two forms is the cut. Without demands k(S) = 1,
 * the subtour elimination constraints.
 *
 * <p>The sets are found from the values of the arcs in an LP solution (Lysgaard, Letchford and
 * Eglese, CVRPSEP): the connected components of the support graph over the customers, and the sets
 * grown greedily from each customer by the customer with the largest flow to and from the set,
 * every set on the way being checked. Over the same sets it also separates the multistar cuts (N.
 * R. Araque, L. Hall and T. L. Magnanti, Capacitated trees, capacitated routing and associated
 * polyhedra, CORE discussion paper 9061, 1990; A. N. Letchford, R. W. Eglese and J. Lysgaard,
 * Multistars, partial multistars and the capacitated vehicle routing problem, Mathematical
 * Programming 94, 2002, 21-40), which weigh the arcs into and out of S by the demands of their ends
 * outside S, for the sets whose rounded capacity cut holds. The cuts use the demands, the capacity
 * and the bounds of the self loops at the first separation (the root), so they hold for the whole
 * search, also when separated later.
 *
 * <p>For routes without a capacity (a travelling salesman tour) it also separates blossom and comb
 * cuts over the same customers, see {@link CombCuts} (Padberg and Rao, Odd minimum cut-sets and
 * b-matchings, Mathematics of Operations Research 7, 1982; Grötschel and Padberg, Mathematical
 * Programming 16, 1979).
 *
 * <p>For routes with time windows ({@link Routes#setTimeWindows}) it separates infeasible path
 * cuts: a path of the support graph that no vehicle can follow within the windows cannot be part of
 * a solution, so a solution has at most p - 2 arcs of the tournament of a path of p nodes, the arcs
 * from each node of the path to every later one (N. Ascheuer, M. Fischetti and M. Grötschel,
 * Solving the asymmetric travelling salesman problem with time windows by branch-and-cut,
 * Mathematical Programming 90(3), 2001, 475-506).
 */
public final class CapacityCuts {

  // the least violation of a cut
  private static final double MIN_VIOLATION = 1e-4;

  // the multistar cuts, also separated over the sets of the capacity cuts
  private static final boolean MULTISTAR =
      !"false".equals(System.getProperty("org.jacop.lp.multistarCuts"));

  // the blossom and comb cuts of the customers (CombCuts): true or false for all Routes; by default
  // only for Routes without a capacity (travelling salesman tours), as on CVRP they were level
  private static final String COMBS = System.getProperty("org.jacop.lp.combCuts", "");

  // flows below this are taken as zero in the support graph
  private static final double EPSILON = 1e-6;

  private final int[] tails;
  private final int[] heads;
  private final IntVar[] literals;
  private final int[] demands;
  private final long capacity;
  private final int n;
  private boolean[] mandatory;

  // the infeasible path cuts of routes with time windows
  private static final boolean PATHS = !"false".equals(System.getProperty("org.jacop.lp.pathCuts"));

  // the most nodes of an infeasible path, and the most extensions tried in one separation
  private static final int MAX_PATH = 16;
  private static final int MAX_STEPS = 200_000;

  // the time windows of the nodes and the least travel time of the arcs, or null
  private long[] earliest;
  private long[] latest;
  private long[] travel;

  // the infeasible path cuts separated
  private int pathCuts;

  // the 2-path cuts of routes with time windows (Kohl et al. 1999): a set of at most MAX_TWO_PATH
  // customers that no route can visit in one stretch within the windows is entered twice
  private static final boolean TWO_PATH =
      !"false".equals(System.getProperty("org.jacop.lp.twoPathCuts"));
  private static final int MAX_TWO_PATH = Integer.getInteger("org.jacop.lp.twoPathSize", 12);
  private static final int TWO_PATH_STEPS = 200_000;

  // at most this many big-M arc-time rows, the strongest ones: thousands of them make the LP slow
  // enough to lose the cut rounds of a 100-customer instance
  private static final int ARC_TIME_MAX = Integer.getInteger("org.jacop.lp.arcTimeMax", 1000);

  // the arc of each pair of nodes, -1 for none, made at the first 2-path check
  private int[][] arcAt;
  // whether one route can visit each set checked so far in one stretch
  private final java.util.Map<BitSet, Boolean> oneStretch = new java.util.HashMap<>();
  // the steps left to the feasibility checks of the current separation
  private int twoPathSteps;

  // the 2-path cuts separated, and whether the last set needed two routes for its windows only
  private int twoPathCuts;
  private boolean twoPath;

  /**
   * A cut over arcs of the routes: {@code sum w[k] x[arcs[k]] >= bound} when entering, else {@code
   * sum w[k] x[arcs[k]] <= bound}.
   */
  public static final class Cut {
    private final int[] arcs;
    private final long[] weights;
    private final boolean entering;
    private final long bound;
    private final double efficacy;

    Cut(int[] arcs, long[] weights, boolean entering, long bound, double efficacy) {
      this.arcs = arcs;
      this.weights = weights;
      this.entering = entering;
      this.bound = bound;
      this.efficacy = efficacy;
    }

    /**
     * It returns the arcs of the cut.
     *
     * @return the indices of the arcs, a copy
     */
    public int[] arcs() {
      return arcs.clone();
    }

    /**
     * It returns the weights of the arcs of the cut.
     *
     * @return the weight of each arc of {@link #arcs()}, a copy
     */
    public long[] weights() {
      return weights.clone();
    }

    /**
     * It tells the sense of the cut.
     *
     * @return true for {@code sum w x >= bound} (the arcs into the set), false for {@code sum w x
     *     <= bound} (the arcs inside it)
     */
    public boolean entering() {
      return entering;
    }

    /**
     * It returns the side of the cut.
     *
     * @return the side
     */
    public long bound() {
      return bound;
    }

    /**
     * It returns the violation of the cut by the values it was separated from, over its norm.
     *
     * @return the efficacy
     */
    public double efficacy() {
      return efficacy;
    }

    @Override
    public String toString() {
      StringBuilder b = new StringBuilder();
      for (int k = 0; k < arcs.length; k++) {
        b.append(k == 0 ? "" : " + ").append(weights[k]).append("*x[").append(arcs[k]).append(']');
      }
      return b + (entering ? " >= " : " <= ") + bound;
    }
  }

  /**
   * The arc-time rows of routes with time windows and node times ({@link Routes#setTimes}): for an
   * arc a = (i, j) between two nodes other than the depot with a known travel time, {@code t[j] >=
   * t[i] + travel[a] - M (1 - x[a])}, written {@code t[j] - t[i] - M x[a] >= travel[a] - M}, with
   * {@code M = latest[i] + travel[a] - earliest[j]} from the windows, which hold in every solution,
   * so that the row holds in every solution too. Arcs with {@code M <= 0} need no literal and give
   * no row (the windows already order the two nodes). These are the big-M precedence rows of the
   * MIP formulations of the travelling salesman and vehicle routing problems with time windows (M.
   * Desrochers and G. Laporte, Improvements and extensions to the Miller-Tucker-Zemlin subtour
   * elimination constraints, Operations Research Letters 10(1), 1991, 27-36).
   *
   * @param routes the routes
   * @param global whether the current bounds of the times hold in every solution (level 0), so that
   *     they may narrow the windows
   * @return the rows, empty without windows or times
   */
  public static List<LinearForm> arcTimeRows(Routes routes, boolean global) {
    List<LinearForm> rows = new ArrayList<>();
    IntVar[] t = routes.times();
    long[] earliest = routes.earliest();
    long[] latest = routes.latest();
    long[] travel = routes.travel();
    if (t == null || earliest == null || latest == null || travel == null) {
      return rows;
    }
    List<double[]> strength = new ArrayList<>();
    for (int a = 0; a < routes.tails.length; a++) {
      int i = routes.tails[a];
      int j = routes.heads[a];
      if (i == 0 || j == 0 || i == j || t[i] == null || t[j] == null || t[i] == t[j]) {
        continue;
      }
      long d = travel[a];
      if (d == Long.MIN_VALUE || routes.literals[a].singleton()) {
        continue;
      }
      long hi = global ? Math.min(latest[i], t[i].max()) : latest[i];
      long lo = global ? Math.max(earliest[j], t[j].min()) : earliest[j];
      long big;
      try {
        big = Math.subtractExact(Math.addExact(hi, d), lo);
        if (big <= 0) {
          continue;
        }
        rows.add(
            new LinearForm(
                new IntVar[] {t[j], t[i], routes.literals[a]},
                new long[] {1, -1, -big},
                Math.subtractExact(d, big),
                LinearForm.GE));
        strength.add(new double[] {(double) d / big, rows.size() - 1});
      } catch (ArithmeticException _) {
        // a window too wide for a row
      }
    }
    if (rows.size() <= ARC_TIME_MAX) {
      return rows;
    }
    // A row binds only when its arc is nearly taken unless the travel time is a large part of M:
    // keep the rows whose travel time is the largest share of M.
    strength.sort((x, y) -> Double.compare(y[0], x[0]));
    List<LinearForm> kept = new ArrayList<>(ARC_TIME_MAX);
    for (int k = 0; k < ARC_TIME_MAX; k++) {
      kept.add(rows.get((int) strength.get(k)[1]));
    }
    return kept;
  }

  /**
   * It creates the separation of the cuts of a Routes.
   *
   * @param routes the routes
   */
  public CapacityCuts(Routes routes) {
    this(routes.tails, routes.heads, routes.literals, routes.demands, routes.capacity);
    if (PATHS && routes.earliest() != null) {
      this.earliest = routes.earliest();
      this.latest = routes.latest();
      this.travel = routes.travel();
    }
  }

  private CapacityCuts(int[] tails, int[] heads, IntVar[] literals, int[] demands, long capacity) {
    this.tails = tails;
    this.heads = heads;
    this.literals = literals;
    this.demands = demands;
    this.capacity = capacity;
    int max = 0;
    for (int k = 0; k < tails.length; k++) {
      max = Math.max(max, Math.max(tails[k], heads[k]));
    }
    this.n = max + 1;
  }

  /**
   * It returns the literals of the arcs.
   *
   * @return the literal of each arc
   */
  public IntVar[] literals() {
    return literals;
  }

  /**
   * It returns the copy over the variables of a copied store.
   *
   * @param map the variables of the copy
   * @return the copy
   */
  public CapacityCuts copy(VarMap map) {
    IntVar[] copied = new IntVar[literals.length];
    for (int k = 0; k < copied.length; k++) {
      copied[k] = map.get(literals[k]);
    }
    CapacityCuts c = new CapacityCuts(tails, heads, copied, demands, capacity);
    c.mandatory = mandatory;
    c.earliest = earliest;
    c.latest = latest;
    c.travel = travel;
    c.arcAt = arcAt;
    return c;
  }

  /**
   * It returns the cuts violated by values of the arcs, the most effective first.
   *
   * @param value the value of each arc in the LP solution
   * @param limit the most cuts returned
   * @return the cuts
   */
  public List<Cut> separate(double[] value, int limit) {
    return separate(value, limit, true);
  }

  /**
   * It returns the cuts violated by values of the arcs, the most effective first.
   *
   * @param value the value of each arc in the LP solution
   * @param limit the most cuts returned
   * @param combs whether blossom and comb cuts ({@link CombCuts}) fill the slots left
   * @return the cuts
   */
  public List<Cut> separate(double[] value, int limit, boolean combs) {
    // the nodes every route must visit: a self loop that is fixed to 0 or none, at the first
    // separation (the root), so that the cuts made later in the search hold everywhere too
    if (mandatory == null) {
      mandatory = new boolean[n];
      Arrays.fill(mandatory, 1, n, true);
      for (int k = 0; k < tails.length; k++) {
        if (tails[k] == heads[k] && literals[k].max() > 0) {
          mandatory[tails[k]] = false;
        }
      }
      mandatory[0] = false;
    }
    // the flow between each pair of nodes, either way, and the flow into each node
    double[][] flow = new double[n][n];
    double[] in = new double[n];
    for (int k = 0; k < tails.length; k++) {
      int t = tails[k];
      int h = heads[k];
      if (t != h) {
        double v = Math.max(0, value[k]);
        flow[t][h] += v;
        flow[h][t] += v;
        in[h] += v;
      }
    }
    twoPathSteps = TWO_PATH_STEPS;
    List<BitSet> sets = new ArrayList<>();
    components(mandatory, flow, sets);
    for (int seed = 1; seed < n; seed++) {
      if (mandatory[seed]) {
        grow(seed, mandatory, flow, in, sets);
      }
    }
    Set<BitSet> seen = new HashSet<>();
    List<Cut> cuts = new ArrayList<>();
    for (BitSet s : sets) {
      if (seen.add(s)) {
        twoPath = false;
        Cut c = cut(s, value);
        if (c != null) {
          cuts.add(c);
          twoPathCuts += twoPath ? 1 : 0;
        }
        // a multistar cut only where the capacity cut holds: at the root they took the slots of
        // the capacity cuts and the bound fell
        Cut m = MULTISTAR && c == null ? multistar(s, value) : null;
        if (m != null) {
          cuts.add(m);
        }
      }
    }
    if (earliest != null) {
      paths(value, cuts);
    }
    cuts.sort(Comparator.comparingDouble((Cut c) -> -c.efficacy()));
    if (cuts.size() >= limit) {
      return new ArrayList<>(cuts.subList(0, limit));
    }
    // blossoms and combs only take the slots the capacity cuts leave: competing for them by
    // efficacy, they lowered the root bound on CVRP (A-n37-k5 659 to 643)
    boolean uncapacitated = demands == null || capacity <= 0;
    if (combs && ("true".equals(COMBS) || uncapacitated && !"false".equals(COMBS))) {
      List<Cut> found = CombCuts.separate(tails, heads, value, mandatory, flow);
      found.sort(Comparator.comparingDouble((Cut c) -> -c.efficacy()));
      cuts.addAll(found.subList(0, Math.min(found.size(), limit - cuts.size())));
    }
    return cuts;
  }

  // the routes needed by a set: its demand over the capacity, rounded up, and at least one; two
  // when one route cannot visit the set in one stretch within the time windows
  private long needed(BitSet s) {
    long k = 1;
    if (demands != null && capacity > 0) {
      long d = 0;
      for (int v = s.nextSetBit(0); v >= 0; v = s.nextSetBit(v + 1)) {
        d += demands[v];
      }
      k = Math.max(1, Math.ceilDiv(d, capacity));
    }
    if (k == 1 && twoPaths() && s.cardinality() > 1 && s.cardinality() <= MAX_TWO_PATH) {
      Boolean one = oneStretch.get(s);
      if (one == null && twoPathSteps > 0) {
        one = stretch(s);
        if (one != null) {
          oneStretch.put((BitSet) s.clone(), one);
        }
      }
      if (Boolean.FALSE.equals(one)) {
        twoPath = true;
        return 2;
      }
    }
    return k;
  }

  private boolean twoPaths() {
    return TWO_PATH && earliest != null && n <= 2_000;
  }

  // whether some order visits all nodes of s one after the other within their windows, each at
  // the earliest time its predecessor in the order allows (the earliest time at the first): the
  // earliest arrival dominates, so the search is exact. Null when the check ran out of steps
  private Boolean stretch(BitSet s) {
    if (arcAt == null) {
      arcAt = new int[n][n];
      for (int[] row : arcAt) {
        Arrays.fill(row, -1);
      }
      for (int a = 0; a < tails.length; a++) {
        if (tails[a] != heads[a]) {
          arcAt[tails[a]][heads[a]] = a;
        }
      }
    }
    int[] nodes = s.stream().toArray();
    boolean[] used = new boolean[nodes.length];
    for (int f = 0; f < nodes.length; f++) {
      used[f] = true;
      Boolean found = extend(nodes, used, nodes[f], earliest[nodes[f]], 1);
      used[f] = false;
      if (found == null || found) {
        return found;
      }
    }
    return Boolean.FALSE;
  }

  private Boolean extend(int[] nodes, boolean[] used, int last, long time, int count) {
    if (count == nodes.length) {
      return Boolean.TRUE;
    }
    if (--twoPathSteps < 0) {
      return null;
    }
    for (int f = 0; f < nodes.length; f++) {
      if (used[f]) {
        continue;
      }
      int a = arcAt[last][nodes[f]];
      if (a < 0) {
        continue;
      }
      // an arc without a known travel time does not order the times: the next one may be as early
      // as its window opens
      long t =
          travel[a] == Long.MIN_VALUE
              ? earliest[nodes[f]]
              : Math.max(earliest[nodes[f]], time + travel[a]);
      if (t > latest[nodes[f]]) {
        continue;
      }
      used[f] = true;
      Boolean found = extend(nodes, used, nodes[f], t, count + 1);
      used[f] = false;
      if (found == null || found) {
        return found;
      }
    }
    return Boolean.FALSE;
  }

  // the connected components of the support graph over the mandatory nodes
  private void components(boolean[] mandatory, double[][] flow, List<BitSet> sets) {
    boolean[] done = new boolean[n];
    int[] stack = new int[n];
    for (int start = 1; start < n; start++) {
      if (!mandatory[start] || done[start]) {
        continue;
      }
      BitSet s = new BitSet(n);
      int top = 0;
      stack[top++] = start;
      done[start] = true;
      while (top > 0) {
        int v = stack[--top];
        s.set(v);
        for (int w = 1; w < n; w++) {
          if (mandatory[w] && !done[w] && flow[v][w] > EPSILON) {
            done[w] = true;
            stack[top++] = w;
          }
        }
      }
      sets.add(s);
    }
  }

  // the sets grown from seed, each time by the mandatory node with the largest flow to the set;
  // every violated set on the way is kept
  private void grow(
      int seed, boolean[] mandatory, double[][] flow, double[] in, List<BitSet> sets) {
    BitSet s = new BitSet(n);
    s.set(seed);
    double[] toSet = Arrays.copyOf(flow[seed], n);
    double into = in[seed];
    double inside = 0;
    long demand = demands == null ? 0 : demands[seed];
    while (true) {
      double entering = into - inside;
      long k = demands == null || capacity <= 0 ? 1 : Math.max(1, Math.ceilDiv(demand, capacity));
      if (k - entering > MIN_VIOLATION
          || k == 1
              && twoPaths()
              && 2 - entering > MIN_VIOLATION
              && s.cardinality() > 1
              && s.cardinality() <= MAX_TWO_PATH) {
        // a 2-path candidate: needed() decides whether one stretch can visit it
        sets.add((BitSet) s.clone());
      }
      int best = -1;
      for (int v = 1; v < n; v++) {
        if (mandatory[v] && !s.get(v) && (best < 0 || toSet[v] > toSet[best])) {
          best = v;
        }
      }
      // a node without flow to the set only adds its own entering flow
      if (best < 0 || toSet[best] <= EPSILON) {
        return;
      }
      s.set(best);
      inside += toSet[best];
      into += in[best];
      demand += demands == null ? 0 : demands[best];
      for (int v = 1; v < n; v++) {
        toSet[v] += flow[best][v];
      }
    }
  }

  // the cut of a set, or null when the solution does not violate it
  private Cut cut(BitSet s, double[] value) {
    long k = needed(s);
    int size = s.cardinality();
    List<Integer> enteringArcs = new ArrayList<>();
    List<Integer> insideArcs = new ArrayList<>();
    double entering = 0;
    double inside = 0;
    for (int a = 0; a < tails.length; a++) {
      int t = tails[a];
      int h = heads[a];
      if (t == h || !s.get(h)) {
        continue;
      }
      if (s.get(t)) {
        insideArcs.add(a);
        inside += value[a];
      } else {
        enteringArcs.add(a);
        entering += value[a];
      }
    }
    // the two forms agree where every node of S has one incoming arc, as in an LP solution that
    // keeps the degree rows: the shorter of the violated ones
    boolean enteringViolated = k - entering > MIN_VIOLATION && !enteringArcs.isEmpty();
    boolean insideViolated = inside - (size - k) > MIN_VIOLATION && !insideArcs.isEmpty();
    if (!enteringViolated && !insideViolated) {
      return null;
    }
    boolean byEntering =
        enteringViolated && (!insideViolated || enteringArcs.size() <= insideArcs.size());
    List<Integer> arcs = byEntering ? enteringArcs : insideArcs;
    double violation = byEntering ? k - entering : inside - (size - k);
    int[] a = arcs.stream().mapToInt(Integer::intValue).toArray();
    long[] w = new long[a.length];
    Arrays.fill(w, 1);
    return new Cut(a, w, byEntering, byEntering ? k : size - k, violation / Math.sqrt(a.length));
  }

  // the multistar cut of a set (Letchford, Eglese and Lysgaard), directed: each route that visits S
  // carries d(S) plus the demands of the customers just before it enters S and just after it
  // leaves S, so Q x(into S) >= d(S) + sum_j d_j (x(j into S) + x(S into j)) over the customers j
  // outside S, that is sum (Q - d_t) x(t, h) over the arcs into S minus sum d_h x(t, h) over the
  // arcs out of S is at least d(S). A route that enters S k >= 2 times counts a customer outside S
  // at most twice, and 2Q <= kQ. Null without demands, or when the values do not violate it.
  private Cut multistar(BitSet s, double[] value) {
    if (demands == null || capacity <= 0) {
      return null;
    }
    long d = 0;
    for (int v = s.nextSetBit(0); v >= 0; v = s.nextSetBit(v + 1)) {
      d += demands[v];
    }
    List<Integer> arcs = new ArrayList<>();
    List<Long> weights = new ArrayList<>();
    double lhs = 0;
    double norm = 0;
    for (int a = 0; a < tails.length; a++) {
      int t = tails[a];
      int h = heads[a];
      long w;
      if (t == h) {
        continue;
      } else if (s.get(h) && !s.get(t)) {
        w = capacity - (t == 0 ? 0 : demands[t]);
      } else if (s.get(t) && !s.get(h) && h != 0) {
        w = -demands[h];
      } else {
        continue;
      }
      if (w != 0) {
        arcs.add(a);
        weights.add(w);
        lhs += w * value[a];
        norm += (double) w * w;
      }
    }
    double violation = d - lhs;
    if (arcs.isEmpty() || violation <= MIN_VIOLATION * Math.max(1, capacity)) {
      return null;
    }
    return new Cut(
        arcs.stream().mapToInt(Integer::intValue).toArray(),
        weights.stream().mapToLong(Long::longValue).toArray(),
        true,
        d,
        violation / Math.sqrt(norm));
  }

  /**
   * It returns the number of infeasible path cuts separated so far.
   *
   * @return the number of cuts
   */
  public int pathCuts() {
    return pathCuts;
  }

  /**
   * It returns the number of 2-path cuts separated so far: sets of customers that one route cannot
   * visit in one stretch within the time windows, entered at least twice (N. Kohl, J. Desrosiers,
   * O. B. G. Madsen, M. M. Solomon and F. Soumis, 2-path cuts for the vehicle routing problem with
   * time windows, Transportation Science 33(1), 1999, 101-116).
   *
   * @return the number of cuts
   */
  public int twoPathCuts() {
    return twoPathCuts;
  }

  // the infeasible path cuts violated by the values (Ascheuer, Fischetti and Grötschel): a path
  // v1, ..., vp that no route can follow within the time windows has at most p - 2 of its arcs in
  // a solution, and so has its tournament, the arcs (va, vb) with a < b (the arcs out of the
  // depot only from v1 and into it only to vp, as the depot has many routes). The paths are
  // grown along the arcs of the support graph from every node while their arcs could still
  // violate the cut, each one checked by the earliest arrival times along it; a path that cannot
  // be followed is not grown further, so the cut is over a minimal one.
  private void paths(double[] value, List<Cut> cuts) {
    int[] outStart = new int[n + 1];
    for (int a = 0; a < tails.length; a++) {
      if (tails[a] != heads[a] && value[a] > EPSILON) {
        outStart[tails[a] + 1]++;
      }
    }
    for (int v = 0; v < n; v++) {
      outStart[v + 1] += outStart[v];
    }
    int[] out = new int[outStart[n]];
    int[] fill = Arrays.copyOf(outStart, n);
    for (int a = 0; a < tails.length; a++) {
      if (tails[a] != heads[a] && value[a] > EPSILON) {
        out[fill[tails[a]]++] = a;
      }
    }
    // the arc of each pair, for the tournaments
    java.util.Map<Long, Integer> arcOf = new java.util.HashMap<>();
    for (int a = 0; a < tails.length; a++) {
      if (tails[a] != heads[a]) {
        arcOf.put((long) tails[a] * n + heads[a], a);
      }
    }
    int[] path = new int[MAX_PATH];
    long[] time = new long[MAX_PATH];
    boolean[] on = new boolean[n];
    int[] steps = {0};
    Set<List<Integer>> seen = new HashSet<>();
    for (int v = 0; v < n; v++) {
      if (v != 0 && !mandatory[v]) {
        continue;
      }
      path[0] = v;
      time[0] = earliest[v];
      on[v] = true;
      grow(1, 0.0, path, time, on, out, outStart, value, arcOf, cuts, seen, steps);
      on[v] = false;
    }
  }

  private void grow(
      int size,
      double sum,
      int[] path,
      long[] time,
      boolean[] on,
      int[] out,
      int[] outStart,
      double[] value,
      java.util.Map<Long, Integer> arcOf,
      List<Cut> cuts,
      Set<List<Integer>> seen,
      int[] steps) {
    int last = path[size - 1];
    if (last == 0 && size > 1) {
      return;
    }
    for (int i = outStart[last]; i < outStart[last + 1]; i++) {
      if (++steps[0] > MAX_STEPS) {
        return;
      }
      int a = out[i];
      int h = heads[a];
      if (on[h] || h != 0 && !mandatory[h]) {
        continue;
      }
      double s = sum + value[a];
      // p nodes, p - 1 arcs at s: the cut p - 2 can be violated only while s > p - 2; each
      // further arc adds at most one to both sides
      if (s <= size - 1 + MIN_VIOLATION) {
        continue;
      }
      long t =
          travel[a] == Long.MIN_VALUE
              ? earliest[h]
              : Math.max(earliest[h], time[size - 1] + travel[a]);
      path[size] = h;
      if (t > latest[h]) {
        Cut c = pathCut(path, size + 1, value, arcOf, seen);
        if (c != null) {
          cuts.add(c);
          pathCuts++;
        }
        continue;
      }
      if (size + 1 < MAX_PATH && h != 0) {
        time[size] = t;
        on[h] = true;
        grow(size + 1, s, path, time, on, out, outStart, value, arcOf, cuts, seen, steps);
        on[h] = false;
      }
    }
  }

  // the tournament cut of the infeasible path, or null when the values do not violate it
  private Cut pathCut(
      int[] path,
      int p,
      double[] value,
      java.util.Map<Long, Integer> arcOf,
      Set<List<Integer>> seen) {
    List<Integer> key = new ArrayList<>(p);
    for (int i = 0; i < p; i++) {
      key.add(path[i]);
    }
    if (!seen.add(key)) {
      return null;
    }
    List<Integer> arcs = new ArrayList<>();
    double lhs = 0;
    for (int x = 0; x < p; x++) {
      for (int y = x + 1; y < p; y++) {
        // the depot: only its arc to the second node and from the one before last
        if (path[x] == 0 && y != 1 || path[y] == 0 && x != p - 2) {
          continue;
        }
        Integer a = arcOf.get((long) path[x] * n + path[y]);
        if (a != null) {
          arcs.add(a);
          lhs += value[a];
        }
      }
    }
    double violation = lhs - (p - 2);
    if (violation <= MIN_VIOLATION) {
      return null;
    }
    int[] as = arcs.stream().mapToInt(Integer::intValue).toArray();
    long[] w = new long[as.length];
    Arrays.fill(w, 1);
    return new Cut(as, w, false, p - 2L, violation / Math.sqrt(as.length));
  }
}
