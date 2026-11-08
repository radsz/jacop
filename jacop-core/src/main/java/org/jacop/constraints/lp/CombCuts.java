/*
 * CombCuts.java
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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Blossom and comb cuts of a {@link org.jacop.constraints.Routes}, separated over the undirected
 * flows {@code y(u, v) = x(u, v) + x(v, u)} between the customers that every route visits.
 *
 * <p>Each such customer has one arc in and one out, so {@code y(delta(v)) = 2}, and a set S of
 * customers (the depot left out) has at most {@code |S| - 1} arcs inside, as the routes start at
 * the depot. From these, for a handle H of mandatory customers and an odd number t &gt;= 3 of
 * pairwise disjoint teeth T_i of customers, each meeting H and leaving it, the comb inequality of
 * Chvatal and of Grötschel and Padberg
 *
 * <pre>
 *   x(A(H)) + sum_i x(A(T_i)) &lt;= |H| + sum_i (|T_i| - 1) - (t + 1) / 2
 * </pre>
 *
 * holds (V. Chvatal, Edmonds polytopes and weakly Hamiltonian graphs, Mathematical Programming 5,
 * 1973, 29-40; M. Grötschel and M. W. Padberg, On the symmetric travelling salesman problem I:
 * inequalities, Mathematical Programming 16, 1979, 265-280), where A(S) are the arcs inside S. With
 * teeth that are single edges {u, v} (u in H) it is the blossom (2-matching) inequality {@code
 * x(A(H)) + y(T) <= |H| + (|T| - 1) / 2} of Edmonds, which holds for any odd set T of such edges,
 * disjoint or not. The same derivation holds for the routes of a vehicle routing problem when the
 * handle and the teeth leave out the depot (G. Laporte and Y. Nobert, Comb inequalities for the
 * vehicle routing problem, Methods of Operations Research 51, 1984, 271-276).
 *
 * <p>Blossoms are separated as in M. W. Padberg and M. R. Rao, Odd minimum cut-sets and
 * b-matchings, Mathematics of Operations Research 7, 1982, 67-80, in the simple form of A. N.
 * Letchford, G. Reinelt and D. O. Theis, Odd minimum cut sets and b-matchings revisited, SIAM
 * Journal on Discrete Mathematics 22, 2008, 1480-1487: with the degree equations the blossom reads
 * {@code y(delta(H) \ T) + sum_{e in T} (1 - y_e) >= 1}, so the minimum cuts of a Gomory-Hu tree
 * (Gusfield's algorithm) on the weights {@code min(y_e, 1 - y_e)} give the handles, the edges at
 * more than 1/2 the teeth, and the parity is fixed by the edge cheapest to add or remove. The
 * connected components of the fractional edges are tried as handles too (M. W. Padberg and S. Hong,
 * On the symmetric travelling salesman problem: a computational study, Mathematical Programming
 * Study 12, 1980, 78-107). Edge teeth are then grown along paths of edges at 1 outside the handle,
 * when the teeth are disjoint, which keeps the violation and strengthens the cut.
 */
final class CombCuts {

  // the least violation of a cut
  private static final double MIN_VIOLATION = 1e-4;

  // flows below this are taken as zero, above 1 - EPSILON as one
  private static final double EPSILON = 1e-6;

  private CombCuts() {}

  /**
   * It returns the blossom and comb cuts violated by values of the arcs.
   *
   * @param tails the tail of each arc
   * @param heads the head of each arc
   * @param value the value of each arc
   * @param mandatory the nodes every route visits (not the depot)
   * @param flow the flow between each pair of nodes, either way
   * @return the cuts, in the form {@code sum w x <= bound}
   */
  static List<CapacityCuts.Cut> separate(
      int[] tails, int[] heads, double[] value, boolean[] mandatory, double[][] flow) {
    int n = mandatory.length;
    // node 0 of the graph stands for the depot and the optional nodes, 1.. for the customers
    int[] node = new int[n];
    int count = 1;
    for (int v = 0; v < n; v++) {
      node[v] = mandatory[v] ? count++ : 0;
    }
    List<CapacityCuts.Cut> cuts = new ArrayList<>();
    if (count < 5) {
      // a blossom needs a handle of two customers or more and three teeth to customers outside it
      return cuts;
    }
    int[] original = new int[count];
    for (int v = 0; v < n; v++) {
      if (mandatory[v]) {
        original[node[v]] = v;
      }
    }
    double[][] y = new double[count][count];
    for (int u = 0; u < n; u++) {
      for (int v = 0; v < n; v++) {
        if (u != v && node[u] != node[v]) {
          y[node[u]][node[v]] += flow[u][v];
        }
      }
    }
    Set<BitSet> handles = new HashSet<>();
    gomoryHu(y, count, handles);
    fractionalComponents(y, count, handles);
    Set<String> seen = new HashSet<>();
    for (BitSet h : handles) {
      CapacityCuts.Cut c = comb(h, y, count, original, tails, heads, value, mandatory);
      if (c != null && seen.add(c.toString())) {
        cuts.add(c);
      }
    }
    return cuts;
  }

  // the minimum cuts of Gusfield's Gomory-Hu tree on the weights min(y, 1 - y) between customers
  // and y to node 0; each cut below 1 gives its side without node 0 as a handle
  private static void gomoryHu(double[][] y, int count, Set<BitSet> handles) {
    double[][] w = new double[count][count];
    for (int u = 0; u < count; u++) {
      for (int v = 0; v < count; v++) {
        double f = y[u][v];
        w[u][v] = f <= EPSILON ? 0 : (u == 0 || v == 0 ? f : Math.min(f, Math.max(0, 1 - f)));
      }
    }
    int[] parent = new int[count];
    MaxFlow mf = new MaxFlow(w, count);
    for (int s = 1; s < count; s++) {
      int t = parent[s];
      double cut = mf.flow(s, t);
      boolean[] side = mf.sourceSide();
      for (int i = s + 1; i < count; i++) {
        if (side[i] && parent[i] == t) {
          parent[i] = s;
        }
      }
      if (cut < 1 - MIN_VIOLATION) {
        BitSet h = new BitSet(count);
        boolean zeroIn = side[0];
        for (int v = 1; v < count; v++) {
          if (side[v] != zeroIn) {
            h.set(v);
          }
        }
        if (h.cardinality() >= 2) {
          handles.add(h);
        }
      }
    }
  }

  // the connected components, over the customers, of the edges with fractional flow
  private static void fractionalComponents(double[][] y, int count, Set<BitSet> handles) {
    boolean[] done = new boolean[count];
    int[] stack = new int[count];
    for (int start = 1; start < count; start++) {
      if (done[start]) {
        continue;
      }
      BitSet h = new BitSet(count);
      int top = 0;
      stack[top++] = start;
      done[start] = true;
      while (top > 0) {
        int v = stack[--top];
        h.set(v);
        for (int u = 1; u < count; u++) {
          if (!done[u] && y[v][u] > EPSILON && y[v][u] < 1 - EPSILON) {
            done[u] = true;
            stack[top++] = u;
          }
        }
      }
      if (h.cardinality() >= 2) {
        handles.add(h);
      }
    }
  }

  // the blossom of a handle, with the teeth grown along paths at 1, or null when not violated
  private static CapacityCuts.Cut comb(
      BitSet h,
      double[][] y,
      int count,
      int[] original,
      int[] tails,
      int[] heads,
      double[] value,
      boolean[] mandatory) {
    // the edges between H and the customers outside it; teeth are those above 1/2
    List<int[]> edges = new ArrayList<>();
    List<int[]> teeth = new ArrayList<>();
    for (int u = h.nextSetBit(0); u >= 0; u = h.nextSetBit(u + 1)) {
      for (int v = 1; v < count; v++) {
        if (!h.get(v) && y[u][v] > EPSILON) {
          edges.add(new int[] {u, v});
          if (y[u][v] > 0.5) {
            teeth.add(new int[] {u, v});
          }
        }
      }
    }
    if (teeth.size() % 2 == 0) {
      // the parity: add or remove the edge whose change costs least
      int[] best = null;
      for (int[] e : edges) {
        if (best == null
            || Math.abs(1 - 2 * y[e[0]][e[1]]) < Math.abs(1 - 2 * y[best[0]][best[1]])) {
          best = e;
        }
      }
      if (best == null) {
        return null;
      }
      if (y[best[0]][best[1]] > 0.5) {
        teeth.remove(best);
      } else {
        teeth.add(best);
      }
    }
    if (teeth.size() < 3) {
      return null;
    }
    double inside = 0;
    for (int u = h.nextSetBit(0); u >= 0; u = h.nextSetBit(u + 1)) {
      for (int v = h.nextSetBit(u + 1); v >= 0; v = h.nextSetBit(v + 1)) {
        inside += y[u][v];
      }
    }
    double lhs = inside;
    for (int[] e : teeth) {
      lhs += y[e[0]][e[1]];
    }
    int t = teeth.size();
    if (lhs - (h.cardinality() + (t - 1) / 2) <= MIN_VIOLATION) {
      return null;
    }
    List<BitSet> sets = grow(h, teeth, y, count);
    // back to the nodes of the routes
    BitSet hand = new BitSet(original.length);
    for (int v = h.nextSetBit(0); v >= 0; v = h.nextSetBit(v + 1)) {
      hand.set(original[v]);
    }
    List<BitSet> toothSets = new ArrayList<>();
    long bound = hand.cardinality() - (t + 1) / 2;
    for (BitSet s : sets) {
      BitSet o = new BitSet(original.length);
      for (int v = s.nextSetBit(0); v >= 0; v = s.nextSetBit(v + 1)) {
        o.set(original[v]);
      }
      toothSets.add(o);
      bound += o.cardinality() - 1;
    }
    List<Integer> arcs = new ArrayList<>();
    List<Long> weights = new ArrayList<>();
    double act = 0;
    double norm = 0;
    for (int a = 0; a < tails.length; a++) {
      int tl = tails[a];
      int hd = heads[a];
      if (tl == hd || !mandatory[tl] || !mandatory[hd]) {
        continue;
      }
      long wt = hand.get(tl) && hand.get(hd) ? 1 : 0;
      for (BitSet s : toothSets) {
        if (s.get(tl) && s.get(hd)) {
          wt++;
        }
      }
      if (wt > 0) {
        arcs.add(a);
        weights.add(wt);
        act += wt * Math.max(0, value[a]);
        norm += (double) wt * wt;
      }
    }
    double violation = act - bound;
    if (violation <= MIN_VIOLATION) {
      return null;
    }
    return new CapacityCuts.Cut(
        arcs.stream().mapToInt(Integer::intValue).toArray(),
        weights.stream().mapToLong(Long::longValue).toArray(),
        false,
        bound,
        violation / Math.sqrt(norm));
  }

  // the teeth as sets: the edge teeth, grown along paths of edges at 1 outside H when they are
  // pairwise disjoint; otherwise the edges as they are (a blossom needs no disjoint teeth)
  private static List<BitSet> grow(BitSet h, List<int[]> teeth, double[][] y, int count) {
    List<BitSet> sets = new ArrayList<>();
    BitSet used = new BitSet(count);
    boolean disjoint = true;
    for (int[] e : teeth) {
      BitSet s = new BitSet(count);
      s.set(e[0]);
      s.set(e[1]);
      if (used.intersects(s)) {
        disjoint = false;
      }
      used.or(s);
      sets.add(s);
    }
    if (!disjoint) {
      return sets;
    }
    for (int i = 0; i < teeth.size(); i++) {
      BitSet s = sets.get(i);
      int end = teeth.get(i)[1];
      int[] from = {teeth.get(i)[0]};
      while (true) {
        int next = -1;
        for (int v = 1; v < count; v++) {
          if (v != from[0] && !h.get(v) && !used.get(v) && y[end][v] >= 1 - EPSILON) {
            next = v;
            break;
          }
        }
        if (next < 0) {
          break;
        }
        s.set(next);
        used.set(next);
        from[0] = end;
        end = next;
      }
    }
    return sets;
  }

  /** Maximum flow (Dinic) on an undirected graph given by a symmetric matrix of capacities. */
  private static final class MaxFlow {
    private final int n;
    private final int[][] adj;
    private final double[][] cap;
    private double[][] residual;
    private final int[] level;
    private final int[] it;
    private int source;

    MaxFlow(double[][] w, int n) {
      this.n = n;
      this.cap = w;
      this.adj = new int[n][];
      for (int u = 0; u < n; u++) {
        int k = 0;
        for (int v = 0; v < n; v++) {
          if (v != u && w[u][v] > 0) {
            k++;
          }
        }
        adj[u] = new int[k];
        k = 0;
        for (int v = 0; v < n; v++) {
          if (v != u && w[u][v] > 0) {
            adj[u][k++] = v;
          }
        }
      }
      this.level = new int[n];
      this.it = new int[n];
    }

    double flow(int s, int t) {
      source = s;
      residual = new double[n][];
      for (int u = 0; u < n; u++) {
        residual[u] = cap[u].clone();
      }
      double total = 0;
      while (bfs(s, t)) {
        Arrays.fill(it, 0);
        double f;
        while ((f = dfs(s, t, Double.MAX_VALUE)) > EPSILON) {
          total += f;
        }
      }
      return total;
    }

    // the nodes reachable from the source in the residual graph of the last flow
    boolean[] sourceSide() {
      boolean[] side = new boolean[n];
      int[] queue = new int[n];
      int head = 0;
      int tail = 0;
      queue[tail++] = source;
      side[source] = true;
      while (head < tail) {
        int u = queue[head++];
        for (int v : adj[u]) {
          if (!side[v] && residual[u][v] > EPSILON) {
            side[v] = true;
            queue[tail++] = v;
          }
        }
      }
      return side;
    }

    private boolean bfs(int s, int t) {
      Arrays.fill(level, -1);
      int[] queue = new int[n];
      int head = 0;
      int tail = 0;
      queue[tail++] = s;
      level[s] = 0;
      while (head < tail) {
        int u = queue[head++];
        for (int v : adj[u]) {
          if (level[v] < 0 && residual[u][v] > EPSILON) {
            level[v] = level[u] + 1;
            queue[tail++] = v;
          }
        }
      }
      return level[t] >= 0;
    }

    private double dfs(int u, int t, double f) {
      if (u == t) {
        return f;
      }
      for (; it[u] < adj[u].length; it[u]++) {
        int v = adj[u][it[u]];
        if (level[v] == level[u] + 1 && residual[u][v] > EPSILON) {
          double d = dfs(v, t, Math.min(f, residual[u][v]));
          if (d > EPSILON) {
            residual[u][v] -= d;
            residual[v][u] += d;
            return d;
          }
        }
      }
      return 0;
    }
  }
}
