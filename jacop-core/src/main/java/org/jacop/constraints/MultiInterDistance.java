/*
 * MultiInterDistance.java
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * MultiInterDistance constraint: for every v at most m of the variables x take a value in v..v + p
 * - 1. It models n tasks of the same length p on m identical machines, x[i] being the start of task
 * i; it is a cumulative with durations p, resource use 1 and capacity m. With m = 1 it is {@link
 * InterDistance}, which has a faster propagator.
 *
 * <p>The propagator is bounds(Z) consistent. It implements the algorithm of A. Ouellet and C.-G.
 * Quimper, "The multi-inter-distance constraint", IJCAI 2011. Feasibility is the absence of a
 * negative cycle in the scheduling graph, a system of difference constraints on S(v), the number of
 * tasks that start before v: at most m starts in any window of p, at least as many starts in l..u -
 * 1 as there are tasks whose start interval lies in it, S non-decreasing and at most n starts in
 * all. Only the bounds of the intervals are nodes: a path between two of them that uses only window
 * and non-decreasing edges costs m * ceil((b - a) / p) to the right and nothing to the left. The
 * variables are processed by increasing maximum. The minimum of x[i] is checked by restricting x[i]
 * to its minimum up to the next maximum of any variable: a negative cycle makes that region
 * forbidden for x[i] and every later variable, otherwise the shortest distances from the minimum
 * give the new minimum, the last value at distance 0. Maximums are pruned on the mirrored problem.
 *
 * <p>The paper finds the shortest paths in O(n^2 min(1, p/m)) time; here Bellman-Ford on the dense
 * graph of at most 2n nodes costs O(n^2) per round, and a pass makes at most 3n searches for each
 * direction.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class MultiInterDistance extends Constraint
    implements SatisfiedPresent, Copyable<MultiInterDistance> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final long INF = Long.MAX_VALUE / 4;

  /** The start times. */
  final IntVar[] x;

  /** The number of machines: at most m start times in any window of p values. */
  final int m;

  /** The length of every task. */
  final int p;

  final int n;

  /** True when a variable occurs more than m times, which fails for p &gt; 0. */
  private final boolean overRepeated;

  // the start intervals lo[i]..up[i] - 1 of one pass
  private final long[] lo;
  private final long[] up;
  private final int[] byUp;

  // the tasks by minimum, the cluster of every task and the number of tasks of every cluster
  private final int[] byLo;
  private final int[] cluster;
  private final int[] clusterSize;

  // the starts of the witness schedule, sorted, and the start of every task in it
  private final long[] starts;
  private int placed;
  private final long[] startOf;
  private final boolean[] supported;

  // forbidden regions fa[k]..fb[k] - 1 found in the pass
  private long[] fa;
  private long[] fb;
  private int nf;

  // the graph of one search: nodes, interval counts, distances and the shortest path tree
  private final long[] node;
  private int nv;
  private final int[][] inside;
  private final long[] dist;
  private final int[] parent;
  private final int[] walk;

  /**
   * It constructs multi_inter_distance(x, m, p): at most m of x in any window v..v + p - 1.
   *
   * @param x the start times.
   * @param m the number of machines, at least 1.
   * @param p the length of the tasks, at least 0.
   */
  public MultiInterDistance(IntVar[] x, int m, int p) {

    checkInputForNullness("x", x);
    if (m < 1) {
      throw new IllegalArgumentException("MultiInterDistance: m must be at least 1, not " + m);
    }
    if (p < 0) {
      throw new IllegalArgumentException("MultiInterDistance: p must be at least 0, not " + p);
    }

    this.numberId = idNumber.incrementAndGet();
    this.n = x.length;
    this.x = Arrays.copyOf(x, n);
    this.m = m;
    this.p = p;
    Map<IntVar, Integer> occurrences = new HashMap<>();
    boolean over = false;
    for (IntVar v : x) {
      over |= occurrences.merge(v, 1, Integer::sum) > m;
    }
    this.overRepeated = over;

    lo = new long[n];
    up = new long[n];
    byUp = new int[n];
    for (int i = 0; i < n; i++) {
      byUp[i] = i;
    }
    byLo = new int[n];
    for (int i = 0; i < n; i++) {
      byLo[i] = i;
    }
    cluster = new int[n];
    clusterSize = new int[n];
    starts = new long[n];
    startOf = new long[n];
    supported = new boolean[n];
    fa = new long[n + 1];
    fb = new long[n + 1];
    node = new long[2 * n];
    inside = new int[2 * n + 1][2 * n + 1];
    dist = new long[2 * n];
    parent = new int[2 * n];
    walk = new int[2 * n];

    this.queueIndex = 3;

    setScope(this.x);
  }

  /**
   * It constructs multi_inter_distance(x, m, p): at most m of x in any window v..v + p - 1.
   *
   * @param x the start times.
   * @param m the number of machines, at least 1.
   * @param p the length of the tasks, at least 0.
   */
  public MultiInterDistance(List<? extends IntVar> x, int m, int p) {
    this(x.toArray(new IntVar[0]), m, p);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {
    if (p == 0 || n <= m) {
      return;
    }
    if (overRepeated) {
      throw Store.failException;
    }
    boolean again;
    do {
      again = false;
      for (int i = 0; i < n; i++) {
        lo[i] = x[i].min();
        up[i] = (long) x[i].max() + 1;
      }
      if (!lower()) {
        throw Store.failException;
      }
      for (int i = 0; i < n; i++) {
        x[i].domain.inMin(store.level, x[i], (int) lo[i]);
        again |= x[i].min() != lo[i];
      }
      // the mirrored problem: x' = -x
      for (int i = 0; i < n; i++) {
        lo[i] = -(long) x[i].max();
        up[i] = -(long) x[i].min() + 1;
      }
      if (!lower()) {
        throw Store.failException;
      }
      for (int i = 0; i < n; i++) {
        x[i].domain.inMax(store.level, x[i], (int) -lo[i]);
        again |= x[i].max() != -lo[i];
      }
    } while (again);
  }

  /**
   * It raises every lo[i] to its smallest supported value (Ouellet and Quimper, algorithm 1).
   *
   * @return false if no schedule exists.
   */
  private boolean lower() {
    for (int k = 1; k < n; k++) {
      int i = byUp[k];
      int j = k - 1;
      while (j >= 0 && up[byUp[j]] > up[i]) {
        byUp[j + 1] = byUp[j];
        j--;
      }
      byUp[j + 1] = i;
    }
    clusters();
    nf = 0;
    Arrays.fill(supported, false);
    for (int k = 0; k < n; k++) {
      int i = byUp[k];
      long ui = up[i];
      // a witness is a solution, so its values stay supported while other minimums rise
      while (!supported[i]) {
        lo[i] = skipForbidden(lo[i]);
        if (lo[i] >= ui) {
          return false;
        }
        if (witness(i, lo[i])) {
          for (int j = 0; j < n; j++) {
            supported[j] |= cluster[j] == cluster[i] && startOf[j] == lo[j];
          }
          break;
        }
        // the next maximum of any variable of the cluster after lo[i]
        long next = ui;
        for (int j = 0; j < n; j++) {
          if (cluster[j] == cluster[i] && up[j] > lo[i] && up[j] < next) {
            next = up[j];
          }
        }
        up[i] = next;
        boolean feasible = shortestPaths(cluster[i], lo[i]);
        up[i] = ui;
        if (!feasible) {
          addForbidden(lo[i], next);
          continue;
        }
        long t = lo[i];
        for (int a = 0; a < nv; a++) {
          if (dist[a] <= 0) {
            t = Math.max(t, node[a] + p * (-dist[a] / m));
          }
        }
        lo[i] = t;
        break;
      }
    }
    return true;
  }

  /**
   * It splits the tasks into clusters that cannot interact: sorted by minimum, a task starts a new
   * cluster when no earlier task can start within p of it. The clusters are independent
   * subproblems; minimums only rise during a pass, so the clusters stay valid.
   */
  private void clusters() {
    for (int k = 1; k < n; k++) {
      int i = byLo[k];
      int j = k - 1;
      while (j >= 0 && lo[byLo[j]] > lo[i]) {
        byLo[j + 1] = byLo[j];
        j--;
      }
      byLo[j + 1] = i;
    }
    int c = -1;
    long reach = -INF;
    for (int k = 0; k < n; k++) {
      int i = byLo[k];
      if (lo[i] >= reach) {
        c++;
        clusterSize[c] = 0;
      }
      cluster[i] = c;
      clusterSize[c]++;
      reach = Math.max(reach, up[i] - 1 + p);
    }
  }

  /**
   * It looks for a schedule with x[i] = v cheaply: x[i] at v and the fixed tasks first, then the
   * other tasks by increasing maximum, each at its earliest start that keeps at most m starts in
   * every window of p. A schedule proves v supported; without one the scheduling graph decides.
   *
   * @return true if every task got a start in its interval.
   */
  private boolean witness(int i, long v) {
    // byUp is sorted by lower()
    placed = 0;
    if (!place(v)) {
      return false;
    }
    startOf[i] = v;
    for (int j = 0; j < n; j++) {
      if (j != i && cluster[j] == cluster[i] && up[j] - lo[j] == 1) {
        if (!place(lo[j])) {
          return false;
        }
        startOf[j] = lo[j];
      }
    }
    for (int k = 0; k < n; k++) {
      int j = byUp[k];
      if (j == i || cluster[j] != cluster[i] || up[j] - lo[j] == 1) {
        continue;
      }
      long s = lo[j];
      while (!place(s)) {
        // the next start that frees a window: the end of a task overlapping s
        long next = INF;
        for (int a = 0; a < placed; a++) {
          if (starts[a] + p > s && starts[a] + p < next) {
            next = starts[a] + p;
          }
        }
        if (next >= up[j]) {
          return false;
        }
        s = next;
      }
      startOf[j] = s;
    }
    return true;
  }

  /**
   * It adds a start at s if every window of p containing s then holds at most m starts.
   *
   * @return true if s was added.
   */
  private boolean place(long s) {
    // the placed starts within p - 1 of s are starts[from..to - 1]
    int to = 0;
    while (to < placed && starts[to] < s + p) {
      to++;
    }
    int from = to;
    while (from > 0 && starts[from - 1] > s - p) {
      from--;
    }
    // the windows containing s that can hold the most starts begin at a start in (s - p, s] or at s
    int end = from;
    for (int a = from; ; a++) {
      long left = a < to && starts[a] <= s ? starts[a] : s;
      while (end < to && starts[end] < left + p) {
        end++;
      }
      int first = a;
      if (left == s) {
        while (first < to && starts[first] < s) {
          first++;
        }
      }
      if (end - first + 1 > m) {
        return false;
      }
      if (left == s) {
        break;
      }
    }
    int at = from;
    while (at < placed && starts[at] < s) {
      at++;
    }
    System.arraycopy(starts, at, starts, at + 1, placed - at);
    starts[at] = s;
    placed++;
    return true;
  }

  private long skipForbidden(long v) {
    boolean moved = true;
    while (moved) {
      moved = false;
      for (int f = 0; f < nf; f++) {
        if (fa[f] <= v && v < fb[f]) {
          v = fb[f];
          moved = true;
        }
      }
    }
    return v;
  }

  private void addForbidden(long a, long b) {
    if (nf == fa.length) {
      fa = Arrays.copyOf(fa, 2 * nf);
      fb = Arrays.copyOf(fb, 2 * nf);
    }
    fa[nf] = a;
    fb[nf] = b;
    nf++;
  }

  /**
   * The shortest distances from the node of value source in the scheduling graph of lo and up.
   *
   * @param c the cluster whose tasks make the graph.
   * @param source the value the distances are measured from, one of lo.
   * @return false if the graph has a negative cycle.
   */
  private boolean shortestPaths(int c, long source) {
    int size = clusterSize[c];
    nv = 0;
    for (int i = 0; i < n; i++) {
      if (cluster[i] == c) {
        node[nv++] = lo[i];
        node[nv++] = up[i];
      }
    }
    Arrays.sort(node, 0, nv);
    int u = 0;
    for (int k = 0; k < nv; k++) {
      if (u == 0 || node[u - 1] != node[k]) {
        node[u++] = node[k];
      }
    }
    nv = u;
    // inside[a][b]: the tasks whose interval lies in node[a]..node[b] - 1, by suffix and prefix
    // sums
    for (int a = 0; a <= nv; a++) {
      Arrays.fill(inside[a], 0, nv + 1, 0);
    }
    for (int i = 0; i < n; i++) {
      if (cluster[i] == c) {
        inside[Arrays.binarySearch(node, 0, nv, lo[i])][Arrays.binarySearch(node, 0, nv, up[i])]++;
      }
    }
    for (int a = nv - 1; a >= 0; a--) {
      for (int b = 0; b < nv; b++) {
        inside[a][b] += inside[a + 1][b] + (b > 0 ? inside[a][b - 1] - inside[a + 1][b - 1] : 0);
      }
    }
    Arrays.fill(dist, 0, nv, INF);
    Arrays.fill(parent, 0, nv, -1);
    dist[Arrays.binarySearch(node, 0, nv, source)] = 0;
    for (int round = 0; round <= nv; round++) {
      boolean changed = false;
      // window edges to the right, then the non-decreasing edges to the left
      for (int b = 1; b < nv; b++) {
        long best = dist[b];
        int from = -1;
        for (int a = 0; a < b; a++) {
          if (dist[a] < INF) {
            long w = dist[a] + m * ((node[b] - node[a] + p - 1) / p);
            if (w < best) {
              best = w;
              from = a;
            }
          }
        }
        if (from >= 0) {
          dist[b] = best;
          parent[b] = from;
          changed = true;
        }
      }
      // the closing edge: at most size starts in all
      if (dist[0] < INF && dist[0] + size < dist[nv - 1]) {
        dist[nv - 1] = dist[0] + size;
        parent[nv - 1] = 0;
        changed = true;
      }
      for (int a = nv - 2; a >= 0; a--) {
        if (dist[a + 1] < dist[a]) {
          dist[a] = dist[a + 1];
          parent[a] = a + 1;
          changed = true;
        }
      }
      // interval edges from b back to a
      for (int a = 0; a < nv; a++) {
        long best = dist[a];
        int from = -1;
        for (int b = a + 1; b < nv; b++) {
          int count = inside[a][b];
          if (count > 0 && dist[b] < INF && dist[b] - count < best) {
            best = dist[b] - count;
            from = b;
          }
        }
        if (from >= 0) {
          dist[a] = best;
          parent[a] = from;
          changed = true;
          // a feasible system has every distance at least -n
          if (best < -size) {
            return false;
          }
        }
      }
      if (!changed) {
        return true;
      }
      if (parentCycle()) {
        return false;
      }
    }
    return false;
  }

  /**
   * It tells if the parent links of the shortest paths close a cycle, which is then negative.
   *
   * @return true if there is a negative cycle.
   */
  private boolean parentCycle() {
    Arrays.fill(walk, 0, nv, 0);
    for (int v = 0; v < nv; v++) {
      int w = v;
      while (w >= 0 && walk[w] == 0) {
        walk[w] = v + 1;
        w = parent[w];
      }
      if (w >= 0 && walk[w] == v + 1) {
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean satisfied() {
    if (p == 0 || n <= m) {
      return true;
    }
    int[] v = new int[n];
    for (int i = 0; i < n; i++) {
      if (!x[i].singleton()) {
        return false;
      }
      v[i] = x[i].value();
    }
    Arrays.sort(v);
    // m + 1 consecutive values in the order within p - 1 of each other
    for (int i = m; i < n; i++) {
      if ((long) v[i] - v[i - m] < p) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : MultiInterDistance([");
    for (int i = 0; i < n; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(x[i]);
    }
    result.append("], ").append(m).append(", ").append(p).append(")");
    return result.toString();
  }

  @Override
  public MultiInterDistance copy(VarMap map) {
    return new MultiInterDistance(map.get(x), m, p);
  }
}
