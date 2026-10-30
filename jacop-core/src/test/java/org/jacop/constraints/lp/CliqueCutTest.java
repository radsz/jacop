/*
 * CliqueCutTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests clique cuts: the cut of three pairwise conflicts, and on random rows over 0/1 and small
 * integer columns, every point within the bounds that meets all the rows must meet every cut.
 */
class CliqueCutTest {

  @Test
  void threePairwiseConflictsGiveOneCliqueCut() {
    // x + y <= 1, y + z <= 1, x + z <= 1 at x = y = z = 1/2: no row is broken, x + y + z <= 1 is
    int[][] cs = {{0, 1}, {1, 2}, {0, 2}};
    long[][] ws = {{1, 1}, {1, 1}, {1, 1}};
    CliqueCut g =
        CliqueCut.of(
            cs,
            ws,
            new long[3],
            new long[] {1, 1, 1},
            new boolean[3],
            new boolean[] {true, true, true},
            new long[3],
            new long[] {1, 1, 1});
    List<MirCut> found = new ArrayList<>();
    g.separate(new double[] {0.5, 0.5, 0.5}, found);
    assertThat(found).hasSize(1);
    assertThat(found.get(0).columns).containsExactly(0, 1, 2);
    assertThat(found.get(0).weights).containsExactly(1, 1, 1);
    assertThat(found.get(0).rhs).isEqualTo(1);
  }

  @Test
  void complementedLiteralsComeFromNegativeWeights() {
    // y <= x (x = 0 and y = 1 conflict), 3 z + 3 y <= 4 (y and z conflict), x + z >= 1 (x = 0 and
    // z = 0 conflict): the literals 1 - x, y, ... at the LP point x = 0.5, y = 0.5, z = 0.5 give
    // (1 - x) + y <= 1 and so on; every cut must hold at each 0/1 point that meets the rows
    int[][] cs = {{0, 1}, {1, 2}, {0, 2}};
    long[][] ws = {{-1, 1}, {3, 3}, {1, 1}};
    long[] rowLo = {0, 0, 1};
    long[] rowHi = {0, 4, 0};
    boolean[] hasLo = {false, false, true};
    boolean[] hasHi = {true, true, false};
    long[] lo = new long[3];
    long[] hi = {1, 1, 1};
    CliqueCut g = CliqueCut.of(cs, ws, rowLo, rowHi, hasLo, hasHi, lo, hi);
    List<MirCut> found = new ArrayList<>();
    g.separate(new double[] {0.4, 0.6, 0.6}, found);
    assertThat(found).isNotEmpty();
    for (MirCut c : found) {
      assertHolds(c, cs, ws, rowLo, rowHi, hasLo, hasHi, lo, hi);
    }
  }

  @Test
  void cutsKeepEveryPointOfTheRows() {
    Random rnd = new Random(5);
    int made = 0;
    for (int run = 0; run < 3000; run++) {
      int n = 3 + rnd.nextInt(4);
      long[] lo = new long[n];
      long[] hi = new long[n];
      for (int j = 0; j < n; j++) {
        if (rnd.nextInt(4) == 0) {
          lo[j] = rnd.nextInt(3) - 1L;
          hi[j] = lo[j] + 1 + rnd.nextInt(2);
        } else {
          hi[j] = 1;
        }
      }
      int m = 1 + rnd.nextInt(5);
      int[][] cs = new int[m][];
      long[][] ws = new long[m][];
      long[] rowLo = new long[m];
      long[] rowHi = new long[m];
      boolean[] hasLo = new boolean[m];
      boolean[] hasHi = new boolean[m];
      for (int i = 0; i < m; i++) {
        int k = 2 + rnd.nextInt(n - 1);
        cs[i] = rnd.ints(0, n).distinct().limit(k).sorted().toArray();
        ws[i] = new long[cs[i].length];
        for (int q = 0; q < cs[i].length; q++) {
          ws[i][q] = rnd.nextInt(11) - 5L;
        }
        hasLo[i] = rnd.nextBoolean();
        hasHi[i] = !hasLo[i] || rnd.nextBoolean();
        rowLo[i] = rnd.nextInt(7) - 5L;
        rowHi[i] = rowLo[i] + rnd.nextInt(6);
      }
      CliqueCut g = CliqueCut.of(cs, ws, rowLo, rowHi, hasLo, hasHi, lo, hi);
      if (g == null) {
        continue;
      }
      double[] value = new double[n];
      for (int j = 0; j < n; j++) {
        value[j] = lo[j] + rnd.nextDouble() * ((double) hi[j] - lo[j]);
      }
      List<MirCut> found = new ArrayList<>();
      g.separate(value, found);
      for (MirCut c : found) {
        made++;
        assertHolds(c, cs, ws, rowLo, rowHi, hasLo, hasHi, lo, hi);
      }
    }
    assertThat(made).isGreaterThan(100);
  }

  // every integer point within the bounds that meets the rows meets the cut
  private static void assertHolds(
      MirCut c,
      int[][] cs,
      long[][] ws,
      long[] rowLo,
      long[] rowHi,
      boolean[] hasLo,
      boolean[] hasHi,
      long[] lo,
      long[] hi) {
    int n = lo.length;
    long[] p = lo.clone();
    while (true) {
      boolean meets = true;
      for (int i = 0; i < cs.length && meets; i++) {
        long a = 0;
        for (int q = 0; q < cs[i].length; q++) {
          a += ws[i][q] * p[cs[i][q]];
        }
        meets = (!hasLo[i] || a >= rowLo[i]) && (!hasHi[i] || a <= rowHi[i]);
      }
      if (meets) {
        long a = 0;
        for (int q = 0; q < c.columns.length; q++) {
          a += c.weights[q] * p[c.columns[q]];
        }
        assertThat(a).as("cut at %s", java.util.Arrays.toString(p)).isLessThanOrEqualTo(c.rhs);
      }
      int j = 0;
      while (j < n && p[j] == hi[j]) {
        p[j] = lo[j];
        j++;
      }
      if (j == n) {
        return;
      }
      p[j]++;
    }
  }
}
