/*
 * DualFeasibleFunctionsTest.java
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

package org.jacop.util;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Random;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks the dual feasible functions against their definition on every set of sizes of a small
 * capacity, and the packing test against an exhaustive search for a packing.
 */
class DualFeasibleFunctionsTest {

  private static final int MAX_CAPACITY = 14;

  private static final int PACKING_TRIALS = 3000;

  @Test
  void functionsAreDualFeasible() {
    for (int c = 1; c <= MAX_CAPACITY; c++) {
      final int cap = c;
      for (int k = 1; k <= 4; k++) {
        final int kk = k;
        check(c, x -> DualFeasibleFunctions.fs1(x, cap, kk), "u^(" + k + ")");
      }
      for (int p = 1; p <= c / 2; p++) {
        final int pp = p;
        check(c, x -> DualFeasibleFunctions.fs2(x, cap, pp), "U^(" + p + ")");
        check(c, x -> DualFeasibleFunctions.ccm1(x, cap, pp), "f_CCM1(" + p + ")");
      }
    }
  }

  private interface Mapping {
    long map(int x);
  }

  // every multiset of sizes 1..c with sum at most c keeps a sum at most f(c), and f is monotone
  private static void check(int c, Mapping f, String name) {
    long fc = f.map(c);
    long[] best = new long[c + 1];
    // best[s] = the largest sum of f over a multiset of sum s (unbounded knapsack)
    for (int s = 1; s <= c; s++) {
      for (int x = 1; x <= s; x++) {
        best[s] = Math.max(best[s], best[s - x] + f.map(x));
      }
    }
    for (int s = 0; s <= c; s++) {
      assertThat(best[s]).as("%s, capacity %d, sum %d", name, c, s).isLessThanOrEqualTo(fc);
    }
    assertThat(f.map(0)).isZero();
  }

  @Test
  void packingTestKeepsPackableSets() {
    Random random = new Random(7);
    DualFeasibleFunctions dff = new DualFeasibleFunctions();
    int beyondArea = 0;
    for (int t = 0; t < PACKING_TRIALS; t++) {
      int width = 2 + random.nextInt(6);
      int height = 2 + random.nextInt(6);
      int n = 1 + random.nextInt(5);
      int[] w = new int[n];
      int[] h = new int[n];
      long area = 0;
      for (int i = 0; i < n; i++) {
        w[i] = 1 + random.nextInt(width);
        h[i] = 1 + random.nextInt(height);
        area += (long) w[i] * h[i];
      }
      boolean fails = dff.packingFails(width, height, w, h, n);
      boolean packable = pack(new boolean[width][height], w, h, 0);
      if (packable) {
        assertThat(fails).as("trial %d", t).isFalse();
      } else if (fails && area <= (long) width * height) {
        beyondArea++;
      }
    }
    // the functions find unpackable sets that the area test misses
    assertThat(beyondArea).isPositive();
  }

  @Test
  void twoSquaresBeyondHalfDoNotFit() {
    DualFeasibleFunctions dff = new DualFeasibleFunctions();
    // area 18 of 25, but neither side fits two 3s
    assertThat(dff.packingFails(5, 5, new int[] {3, 3}, new int[] {3, 3}, 2)).isTrue();
    assertThat(dff.packingFails(6, 5, new int[] {3, 3}, new int[] {3, 3}, 2)).isFalse();
  }

  @Test
  void diffnFailsOnTwoSquaresBeyondHalf() {
    Store store = new Store();
    IntVar[][] r = new IntVar[2][];
    for (int i = 0; i < 2; i++) {
      r[i] =
          new IntVar[] {
            new IntVar(store, 0, 2),
            new IntVar(store, 0, 2),
            new IntVar(store, 3, 3),
            new IntVar(store, 3, 3)
          };
    }
    store.impose(new Diffn(r));
    assertThat(store.consistency()).isFalse();
  }

  // exhaustive search: rectangle i at every position where it fits
  private static boolean pack(boolean[][] used, int[] w, int[] h, int i) {
    if (i == w.length) {
      return true;
    }
    int width = used.length;
    int height = used[0].length;
    for (int x = 0; x + w[i] <= width; x++) {
      for (int y = 0; y + h[i] <= height; y++) {
        if (free(used, x, y, w[i], h[i])) {
          fill(used, x, y, w[i], h[i], true);
          boolean ok = pack(used, w, h, i + 1);
          fill(used, x, y, w[i], h[i], false);
          if (ok) {
            return true;
          }
        }
      }
    }
    return false;
  }

  private static boolean free(boolean[][] used, int x, int y, int w, int h) {
    for (int a = x; a < x + w; a++) {
      for (int b = y; b < y + h; b++) {
        if (used[a][b]) {
          return false;
        }
      }
    }
    return true;
  }

  private static void fill(boolean[][] used, int x, int y, int w, int h, boolean v) {
    for (int a = x; a < x + w; a++) {
      for (int b = y; b < y + h; b++) {
        used[a][b] = v;
      }
    }
  }
}
