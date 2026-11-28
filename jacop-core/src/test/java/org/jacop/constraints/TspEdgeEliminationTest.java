/*
 * TspEdgeEliminationTest.java
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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link TspEdgeElimination} against enumeration: on small random symmetric instances
 * (Euclidean, random with many ties, negative lengths, missing edges) no edge of an optimal tour
 * may be eliminated, and enough edges must go for the check to mean something.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class TspEdgeEliminationTest {

  private static final int TRIALS = Integer.getInteger("tsp.elimination.trials", 3000);

  private long best;
  private final List<int[]> optima = new ArrayList<>();

  @Test
  void optimalToursStay() {
    Random random = new Random(5);
    long eliminated = 0;
    long edges = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      int n = 5 + random.nextInt(5);
      long[][] d = new long[n][n];
      boolean[][] e = new boolean[n][n];
      int kind = trial % 4;
      int[] x = new int[n];
      int[] y = new int[n];
      for (int i = 0; i < n; i++) {
        x[i] = random.nextInt(100);
        y[i] = random.nextInt(100);
      }
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          long v =
              switch (kind) {
                case 0 -> Math.round(Math.hypot(x[i] - x[j], y[i] - y[j]));
                case 1 -> random.nextInt(20);
                case 2 -> random.nextInt(200) - 100;
                default -> random.nextInt(1000);
              };
          d[i][j] = v;
          d[j][i] = v;
          // missing edges get a length above any tour, as the FlatZinc front end does
          boolean present = kind != 3 || random.nextInt(5) > 0;
          e[i][j] = present;
          e[j][i] = present;
        }
      }
      if (kind == 3) {
        for (int i = 0; i < n; i++) {
          for (int j = 0; j < n; j++) {
            if (i != j && !e[i][j]) {
              d[i][j] = 2L * n * 1000 + 1;
            }
          }
        }
      }
      boolean[][] before = new boolean[n][];
      for (int i = 0; i < n; i++) {
        before[i] = e[i].clone();
      }
      int removed = TspEdgeElimination.eliminate(d, e, Long.MAX_VALUE);
      eliminated += removed;
      edges += (long) n * (n - 1) / 2;
      best = Long.MAX_VALUE;
      optima.clear();
      int[] tour = new int[n];
      for (int i = 0; i < n; i++) {
        tour[i] = i;
      }
      enumerate(d, before, tour, 1);
      for (int[] t : optima) {
        for (int i = 0; i < n; i++) {
          int u = t[i];
          int v = t[(i + 1) % n];
          assertTrue(
              e[u][v] && e[v][u],
              "trial " + trial + ": optimal edge " + u + "-" + v + " eliminated");
        }
      }
    }
    assertTrue(eliminated * 5 > edges, "too few eliminations: " + eliminated + " of " + edges);
  }

  @Test
  void asymmetricDistancesAreRejected() {
    long[][] d = new long[5][5];
    boolean[][] e = new boolean[5][5];
    d[0][1] = 1;
    assertThrows(
        IllegalArgumentException.class, () -> TspEdgeElimination.eliminate(d, e, Long.MAX_VALUE));
    assertFalse(e[0][1]);
  }

  // all tours over the edges, starting at 0, keeping the optimal ones
  private void enumerate(long[][] d, boolean[][] e, int[] p, int k) {
    int n = p.length;
    if (k == n) {
      if (!e[p[n - 1]][p[0]]) {
        return;
      }
      long c = 0;
      for (int i = 0; i < n; i++) {
        c += d[p[i]][p[(i + 1) % n]];
      }
      if (c < best) {
        best = c;
        optima.clear();
      }
      if (c == best) {
        optima.add(p.clone());
      }
      return;
    }
    for (int i = k; i < n; i++) {
      int t = p[k];
      p[k] = p[i];
      p[i] = t;
      if (e[p[k - 1]][p[k]]) {
        enumerate(d, e, p, k + 1);
      }
      t = p[k];
      p[k] = p[i];
      p[i] = t;
    }
  }
}
