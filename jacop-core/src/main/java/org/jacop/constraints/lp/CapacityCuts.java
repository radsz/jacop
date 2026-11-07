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
 */
public final class CapacityCuts {

  // the least violation of a cut
  private static final double MIN_VIOLATION = 1e-4;

  // the multistar cuts, also separated over the sets of the capacity cuts
  private static final boolean MULTISTAR =
      !"false".equals(System.getProperty("org.jacop.lp.multistarCuts"));

  // flows below this are taken as zero in the support graph
  private static final double EPSILON = 1e-6;

  private final int[] tails;
  private final int[] heads;
  private final IntVar[] literals;
  private final int[] demands;
  private final long capacity;
  private final int n;
  private boolean[] mandatory;

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
   * It creates the separation of the cuts of a Routes.
   *
   * @param routes the routes
   */
  public CapacityCuts(Routes routes) {
    this(routes.tails, routes.heads, routes.literals, routes.demands, routes.capacity);
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
        Cut c = cut(s, value);
        if (c != null) {
          cuts.add(c);
        }
        // a multistar cut only where the capacity cut holds: at the root they took the slots of
        // the capacity cuts and the bound fell
        Cut m = MULTISTAR && c == null ? multistar(s, value) : null;
        if (m != null) {
          cuts.add(m);
        }
      }
    }
    cuts.sort(Comparator.comparingDouble((Cut c) -> -c.efficacy()));
    return cuts.size() > limit ? new ArrayList<>(cuts.subList(0, limit)) : cuts;
  }

  // the routes needed by a set: its demand over the capacity, rounded up, and at least one
  private long needed(BitSet s) {
    if (demands == null || capacity <= 0) {
      return 1;
    }
    long d = 0;
    for (int v = s.nextSetBit(0); v >= 0; v = s.nextSetBit(v + 1)) {
      d += demands[v];
    }
    return Math.max(1, Math.ceilDiv(d, capacity));
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
      if (k - entering > MIN_VIOLATION) {
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
}
