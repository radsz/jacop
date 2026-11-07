/*
 * SteinerCycleBound.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * The Steiner cycle relaxation of Vismara and Briot (A Circuit Constraint for Multiple Tours
 * Problems, CP 2018) for one cycle that must pass through the required nodes R and may pass through
 * the optional nodes O; the other nodes are not on it.
 *
 * <p>Each optional node o is charged m(o), a lower bound of what it contributes to the cost whether
 * it is on the cycle or not, and an arc from o then costs c(o, j) - m(o) &gt;= 0. So the cost is at
 * least the charges plus the costs of the paths that link each required node to the next one
 * through optional nodes. The cheapest such path from i to j, d(i, j), is found by Dijkstra's
 * algorithm, and the minimum assignment of R on d bounds the cost: without self-loops when |R|
 * &gt;= 2, since all required nodes are on the cycle, and d(i, i), the cheapest cycle through i,
 * when |R| = 1. This is the assignment problem on the extended graph G* of the paper.
 *
 * <p>An arc a to b forced into the cycle lies on the path from some required node i to some
 * required node j, so the assignment costs at least its dual bound plus F(a) + c'(a, b) + G(b),
 * where F(a) = min over i of (cheapest path from i to a) - u(i) and G(b) = min over j of (cheapest
 * path from b to j) - v(j), with F = -u and G = -v on the required nodes themselves. A node o
 * forced onto the cycle costs at least F(o) + G(o) more. Both are computed by one multi-source
 * Dijkstra each.
 */
final class SteinerCycleBound {

  static final long INF = Long.MAX_VALUE / 8;

  static final byte OUT = 0;
  static final byte REQUIRED = 1;
  static final byte OPTIONAL = 2;

  private final int n;
  private final IntVar[] list;
  private final int[][] costs;
  private final int offset;

  /** The kind of each node, set by the caller before {@link #solve()}. */
  final byte[] kind;

  /** The charge of each optional node, set by the caller before {@link #solve()}. */
  final long[] charge;

  // the required nodes, and the position of each in that list
  private final int[] required;
  private final int[] position;
  private int r;
  private final long[] dist;
  private final boolean[] done;
  private final long[] forward;
  private final long[] backward;
  private long[][] weight = new long[0][];

  // the Hungarian method on the required nodes (1-based arrays)
  private long[] u = new long[1];
  private long[] v = new long[1];
  private int[] mate = new int[1];
  private int[] way = new int[1];
  private long[] minv = new long[1];
  private boolean[] used = new boolean[1];

  SteinerCycleBound(IntVar[] list, int[][] costs, int offset) {
    this.n = list.length;
    this.list = list;
    this.costs = costs;
    this.offset = offset;
    kind = new byte[n];
    charge = new long[n];
    required = new int[n];
    position = new int[n];
    dist = new long[n];
    done = new boolean[n];
    forward = new long[n];
    backward = new long[n];
  }

  /**
   * It computes the assignment bound of the paths between the required nodes and the potentials
   * used by {@link #arc(int, int)} and {@link #node(int)}. There must be at least one required
   * node.
   *
   * @return the bound, without the charges of the optional nodes.
   */
  long solve() {
    r = 0;
    for (int i = 0; i < n; i++) {
      if (kind[i] == REQUIRED) {
        position[i] = r;
        required[r++] = i;
      }
    }
    if (weight.length < r) {
      weight = new long[r][r];
      u = new long[r + 1];
      v = new long[r + 1];
      mate = new int[r + 1];
      way = new int[r + 1];
      minv = new long[r + 1];
      used = new boolean[r + 1];
    }
    for (int k = 0; k < r; k++) {
      paths(required[k], weight[k]);
    }

    long bound;
    if (r == 1) {
      bound = weight[0][0];
      if (bound >= INF) {
        throw Store.failException;
      }
      u[1] = bound;
      v[1] = 0;
    } else {
      for (int k = 0; k < r; k++) {
        weight[k][k] = INF;
      }
      bound = hungarian();
    }
    forwardPaths();
    backwardPaths();
    return bound;
  }

  /**
   * It bounds how much forcing the arc a to b into the cycle adds to the bound.
   *
   * @return the increase, or at least INF when no cycle through the required nodes uses the arc.
   */
  long arc(int a, int b) {
    long fa = kind[a] == REQUIRED ? -u[position[a] + 1] : forward[a];
    long gb = kind[b] == REQUIRED ? -v[position[b] + 1] : backward[b];
    if (fa >= INF || gb >= INF) {
      return INF;
    }
    return fa + costs[a][b] - (kind[a] == REQUIRED ? 0 : charge[a]) + gb;
  }

  /**
   * It bounds how much forcing the optional node o onto the cycle adds to the bound.
   *
   * @return the increase, or at least INF when no cycle through the required nodes reaches o.
   */
  long node(int o) {
    if (forward[o] >= INF || backward[o] >= INF) {
      return INF;
    }
    return forward[o] + backward[o];
  }

  // the cheapest paths from the required node s through optional nodes to every required node
  private void paths(int s, long[] out) {
    Arrays.fill(out, 0, r, INF);
    Arrays.fill(dist, INF);
    Arrays.fill(done, false);
    relax(s, 0, 0, out);
    while (true) {
      int best = -1;
      long bestDist = INF;
      for (int o = 0; o < n; o++) {
        if (kind[o] == OPTIONAL && !done[o] && dist[o] < bestDist) {
          bestDist = dist[o];
          best = o;
        }
      }
      if (best < 0) {
        return;
      }
      done[best] = true;
      relax(best, bestDist, charge[best], out);
    }
  }

  // the arcs leaving node a, reached at distance d, with the charge of a taken off
  private void relax(int a, long d, long chargeA, long[] out) {
    IntVar x = list[a];
    int[] row = costs[a];
    int last = x.max();
    for (int val = x.min(); ; val = x.domain.nextValue(val)) {
      int b = val - offset;
      if (b != a) {
        long nd = d + row[b] - chargeA;
        if (kind[b] == REQUIRED) {
          int p = position[b];
          if (nd < out[p]) {
            out[p] = nd;
          }
        } else if (kind[b] == OPTIONAL && !done[b] && nd < dist[b]) {
          dist[b] = nd;
        }
      }
      if (val >= last) {
        break;
      }
    }
  }

  // forward[o] = min over required i of (cheapest path from i to the optional node o) - u(i)
  private void forwardPaths() {
    Arrays.fill(forward, INF);
    Arrays.fill(done, false);
    for (int k = 0; k < r; k++) {
      int i = required[k];
      long ui = u[k + 1];
      IntVar x = list[i];
      int[] row = costs[i];
      int last = x.max();
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int b = val - offset;
        if (kind[b] == OPTIONAL) {
          long d = row[b] - ui;
          if (d < forward[b]) {
            forward[b] = d;
          }
        }
        if (val >= last) {
          break;
        }
      }
    }
    while (true) {
      int best = -1;
      long bestDist = INF;
      for (int o = 0; o < n; o++) {
        if (kind[o] == OPTIONAL && !done[o] && forward[o] < bestDist) {
          bestDist = forward[o];
          best = o;
        }
      }
      if (best < 0) {
        return;
      }
      done[best] = true;
      IntVar x = list[best];
      int[] row = costs[best];
      long c = charge[best];
      int last = x.max();
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int b = val - offset;
        if (b != best && kind[b] == OPTIONAL && !done[b]) {
          long d = bestDist + row[b] - c;
          if (d < forward[b]) {
            forward[b] = d;
          }
        }
        if (val >= last) {
          break;
        }
      }
    }
  }

  // backward[o] = min over required j of (cheapest path from the optional node o to j) - v(j)
  private void backwardPaths() {
    Arrays.fill(backward, INF);
    Arrays.fill(done, false);
    for (int o = 0; o < n; o++) {
      if (kind[o] != OPTIONAL) {
        continue;
      }
      IntVar x = list[o];
      int[] row = costs[o];
      long c = charge[o];
      int last = x.max();
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int b = val - offset;
        if (kind[b] == REQUIRED) {
          long d = row[b] - c - v[position[b] + 1];
          if (d < backward[o]) {
            backward[o] = d;
          }
        }
        if (val >= last) {
          break;
        }
      }
    }
    while (true) {
      int best = -1;
      long bestDist = INF;
      for (int o = 0; o < n; o++) {
        if (kind[o] == OPTIONAL && !done[o] && backward[o] < bestDist) {
          bestDist = backward[o];
          best = o;
        }
      }
      if (best < 0) {
        return;
      }
      done[best] = true;
      int val = offset + best;
      for (int a = 0; a < n; a++) {
        if (a != best && kind[a] == OPTIONAL && !done[a] && list[a].domain.contains(val)) {
          long d = bestDist + costs[a][best] - charge[a];
          if (d < backward[a]) {
            backward[a] = d;
          }
        }
      }
    }
  }

  /*
   * The minimum assignment of the r required nodes on weight, by the Hungarian method with
   * shortest augmenting paths; u and v get its duals. Infinite weights are replaced by a weight
   * larger than any assignment of finite ones, so an assignment that needs one means that the
   * required nodes cannot be linked into a cycle.
   */
  private long hungarian() {
    long big = 1;
    for (int i = 0; i < r; i++) {
      long rowMax = 0;
      for (int j = 0; j < r; j++) {
        if (weight[i][j] < INF) {
          rowMax = Math.max(rowMax, Math.abs(weight[i][j]));
        }
      }
      big += 2 * rowMax;
    }
    for (int i = 0; i < r; i++) {
      for (int j = 0; j < r; j++) {
        if (weight[i][j] >= INF) {
          weight[i][j] = big;
        }
      }
    }
    Arrays.fill(u, 0, r + 1, 0);
    Arrays.fill(v, 0, r + 1, 0);
    Arrays.fill(mate, 0, r + 1, 0);
    for (int i = 1; i <= r; i++) {
      mate[0] = i;
      int j0 = 0;
      Arrays.fill(minv, 0, r + 1, Long.MAX_VALUE);
      Arrays.fill(used, 0, r + 1, false);
      do {
        used[j0] = true;
        int i0 = mate[j0];
        long delta = Long.MAX_VALUE;
        int j1 = 0;
        long[] w = weight[i0 - 1];
        for (int j = 1; j <= r; j++) {
          if (!used[j]) {
            long cur = w[j - 1] - u[i0] - v[j];
            if (cur < minv[j]) {
              minv[j] = cur;
              way[j] = j0;
            }
            if (minv[j] < delta) {
              delta = minv[j];
              j1 = j;
            }
          }
        }
        for (int j = 0; j <= r; j++) {
          if (used[j]) {
            u[mate[j]] += delta;
            v[j] -= delta;
          } else {
            minv[j] -= delta;
          }
        }
        j0 = j1;
      } while (mate[j0] != 0);
      do {
        int j1 = way[j0];
        mate[j0] = mate[j1];
        j0 = j1;
      } while (j0 != 0);
    }
    long sum = 0;
    for (int j = 1; j <= r; j++) {
      long w = weight[mate[j] - 1][j - 1];
      if (w == big) {
        throw Store.failException;
      }
      sum += w;
    }
    return sum;
  }
}
