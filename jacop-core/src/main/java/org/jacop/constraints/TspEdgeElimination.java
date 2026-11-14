/*
 * TspEdgeElimination.java
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

/**
 * Edge elimination for the symmetric travelling salesman problem: it proves, from the distances
 * alone, that some edges are in no optimal tour, so that a solver can drop them before search.
 *
 * <p>Every rule shows that each tour through the edge pq can be shortened by a valid k-opt move,
 * which no optimal tour allows. The rules use strict improvements, so every optimal tour within the
 * given edge set stays; only tours that are not optimal are lost. None of them needs the triangle
 * inequality. With E the edges not yet eliminated (it must hold every optimal tour, for example the
 * arcs left in the successor domains of a circuit):
 *
 * <ul>
 *   <li>Two edges of an optimal tour are compatible (Jonker and Volgenant): max(d(p,x) + d(q,y),
 *       d(p,y) + d(q,x)) &ge; d(p,q) + d(x,y), else a 2-opt move shortens the tour. So the
 *       neighbours of a point r in an optimal tour through pq lie in R = {x : rx in E, rx
 *       compatible with pq}.
 *   <li>Close point elimination (Hougardy and Schroeder, Theorem 2): a pair x, y of neighbours of r
 *       is refuted when d(x,y) + d(p,r) + d(q,r) &lt; d(p,q) + d(x,r) + d(y,r), as the 3-opt move
 *       to xy, pr and qr shortens the tour. If every pair of R is refuted, pq is in no optimal
 *       tour.
 *   <li>Main edge elimination (Hougardy and Schroeder, Theorem 1): R is covered by R1 (points
 *       nearer p) and R2 (nearer q) such that each pair of R that is not refuted has one point in
 *       R1 and one in R2 (a point of an unrefuted pair inside one side goes to both sides). With
 *       A(r) = min over x in R1 of d(r,x) - d(p,x) and B(r) = min over y in R2 of d(r,y) - d(q,y),
 *       two such points r, s that cannot be adjacent (s not in R of r, or r not in R of s)
 *       eliminate pq when d(p,q) - d(r,s) + A(r) + B(s) &gt; 0 and d(p,q) - d(r,s) + A(s) + B(r)
 *       &gt; 0: one of the two 3-opt moves (pq, rx, sw to px, rs, qw, or pq, ry, sz to pz, rs, qy)
 *       is valid in every tour, and both shorten it.
 * </ul>
 *
 * <p>The points r are taken in increasing d(p,r) + d(q,r), at most {@link #CANDIDATES} of them per
 * edge, as in step 1 of Hougardy and Schroeder, but with the covering checked on the distances
 * instead of the Euclidean geometry, so it applies to any symmetric distance matrix. Rounds repeat
 * while edges go, since a smaller E gives smaller sets R.
 *
 * <p>References: R. Jonker and T. Volgenant, Nonoptimal edges for the symmetric traveling salesman
 * problem, Operations Research 32(4), 1984; S. Hougardy and R. T. Schroeder, Edge elimination in
 * TSP instances, WG 2014, LNCS 8747 (arXiv 1402.7301); W. Cook, K. Helsgaun, S. Hougardy and R. T.
 * Schroeder, Local elimination in the traveling salesman problem, Mathematical Programming
 * Computation, 2024 (arXiv 2307.07054).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class TspEdgeElimination {

  /** The most points r tried for one edge. */
  public static final int CANDIDATES = 10;

  /** The most rounds over all edges. */
  public static final int ROUNDS = 5;

  private static final long INF = Long.MAX_VALUE / 4;

  private final long[][] d;
  private final boolean[][] edge;
  private final int n;

  // scratch: 0 not in R, 1 in R1, 2 in R2, 3 in both
  private final int[] side;
  private final int[] members;
  private final int[] chosen = new int[CANDIDATES];
  private final long[] keyOf = new long[CANDIDATES];
  private final long[] a = new long[CANDIDATES];
  private final long[] b = new long[CANDIDATES];
  private final int[][] sides;

  private TspEdgeElimination(long[][] d, boolean[][] edge) {
    this.d = d;
    this.edge = edge;
    this.n = d.length;
    this.side = new int[n];
    this.members = new int[n];
    this.sides = new int[CANDIDATES][n];
  }

  /**
   * It removes from a symmetric edge set the edges that are in no optimal tour.
   *
   * @param d the symmetric distances, d[i][j] == d[j][i].
   * @param edge the edges, symmetric, edge[i][i] false; it must hold every optimal tour. The
   *     eliminated edges are set to false in both directions.
   * @param deadline the System.nanoTime() after which no more edges are tried.
   * @return the number of eliminated edges.
   */
  public static int eliminate(long[][] d, boolean[][] edge, long deadline) {
    int n = d.length;
    if (n < 5) {
      return 0;
    }
    for (int i = 0; i < n; i++) {
      if (d[i].length != n || edge[i].length != n) {
        throw new IllegalArgumentException("Distances and edges must be square of the same size");
      }
      for (int j = 0; j < n; j++) {
        if (d[i][j] != d[j][i] || edge[i][j] != edge[j][i]) {
          throw new IllegalArgumentException("Distances and edges must be symmetric");
        }
        if (Math.abs(d[i][j]) > (1L << 40)) {
          throw new IllegalArgumentException("Distances must be at most 2^40 in absolute value");
        }
      }
    }
    TspEdgeElimination e = new TspEdgeElimination(d, edge);
    int total = 0;
    for (int round = 0; round < ROUNDS; round++) {
      int count = 0;
      for (int p = 0; p < n; p++) {
        if (System.nanoTime() > deadline) {
          return total + count;
        }
        for (int q = p + 1; q < n; q++) {
          if (edge[p][q] && e.useless(p, q)) {
            edge[p][q] = false;
            edge[q][p] = false;
            count++;
          }
        }
      }
      total += count;
      if (count == 0) {
        break;
      }
    }
    return total;
  }

  // true when pq is in no optimal tour
  private boolean useless(int p, int q) {
    long l = d[p][q];
    // the CANDIDATES points r nearest to the edge, by d(p,r) + d(q,r)
    int m = 0;
    for (int r = 0; r < n; r++) {
      if (r == p || r == q) {
        continue;
      }
      long key = d[p][r] + d[q][r];
      if (m < CANDIDATES) {
        m++;
      } else if (key >= keyOf[m - 1]) {
        continue;
      }
      int k = m - 1;
      while (k > 0 && keyOf[k - 1] > key) {
        keyOf[k] = keyOf[k - 1];
        chosen[k] = chosen[k - 1];
        k--;
      }
      keyOf[k] = key;
      chosen[k] = r;
    }
    for (int c = 0; c < m; c++) {
      int r = chosen[c];
      int size = cover(p, q, r);
      if (size < 0) {
        return true;
      }
      long ar = INF;
      long br = INF;
      for (int i = 0; i < size; i++) {
        int x = members[i];
        if ((side[x] & 1) != 0) {
          ar = Math.min(ar, d[r][x] - d[p][x]);
        }
        if ((side[x] & 2) != 0) {
          br = Math.min(br, d[r][x] - d[q][x]);
        }
      }
      for (int t = 0; t < c; t++) {
        int s = chosen[t];
        if (side[s] != 0 && sides[t][r] != 0) {
          // r and s may be adjacent
          continue;
        }
        long base = l - d[r][s];
        if (base + ar + b[t] > 0 && base + a[t] + br > 0) {
          return true;
        }
      }
      a[c] = ar;
      b[c] = br;
      System.arraycopy(side, 0, sides[c], 0, n);
    }
    return false;
  }

  // the covering R1, R2 of the possible neighbours of r in an optimal tour through pq, in side and
  // members; -1 when no pair of neighbours is possible
  private int cover(int p, int q, int r) {
    long l = d[p][q];
    Arrays.fill(side, 0);
    int size = 0;
    for (int x = 0; x < n; x++) {
      if (x == r || !edge[r][x]) {
        continue;
      }
      if (x != p && x != q && Math.max(d[p][r] + d[q][x], d[p][x] + d[q][r]) < l + d[r][x]) {
        // rx and pq are not compatible
        continue;
      }
      members[size++] = x;
      side[x] = d[p][x] <= d[q][x] ? 1 : 2;
    }
    long k = d[p][r] + d[q][r] - l;
    boolean possible = false;
    for (int i = 0; i < size; i++) {
      int x = members[i];
      for (int j = i + 1; j < size; j++) {
        int y = members[j];
        if ((x == p && y == q) || (x == q && y == p) || d[x][r] + d[y][r] - d[x][y] > k) {
          // a triangle p, q, r, or refuted by the 3-opt move to xy, pr, qr
          continue;
        }
        possible = true;
        if (side[x] == side[y] && side[x] != 3) {
          side[y] = 3;
        }
      }
    }
    return possible ? size : -1;
  }
}
