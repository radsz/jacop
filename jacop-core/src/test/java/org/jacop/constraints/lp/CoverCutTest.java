/*
 * CoverCutTest.java
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

import java.util.Arrays;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests lifted cover cuts against enumeration: on random rows over 0/1 columns (with weights of
 * both signs) and a few small integer columns, every integer point within the bounds that meets the
 * row must meet the cut, and the cut must cut off the LP point by its efficacy.
 */
class CoverCutTest {

  @Test
  void cutsKeepEveryIntegerPointOfTheRow() {
    Random rnd = new Random(5);
    int made = 0;
    int lifted = 0;
    for (int run = 0; run < 40000; run++) {
      int n = 3 + rnd.nextInt(6);
      int[] columns = new int[n];
      long[] c = new long[n];
      long[] lo = new long[n];
      long[] hi = new long[n];
      double[] value = new double[n];
      for (int j = 0; j < n; j++) {
        columns[j] = j;
        boolean binary = rnd.nextInt(6) != 0;
        if (rnd.nextInt(8) == 0) {
          c[j] = 0;
        } else {
          c[j] = rnd.nextInt(5) == 0 ? -1L - rnd.nextInt(15) : 1L + rnd.nextInt(30);
        }
        lo[j] = binary ? 0 : rnd.nextInt(5) - 2L;
        hi[j] = binary ? 1 : lo[j] + rnd.nextInt(3);
        value[j] = lo[j] + rnd.nextDouble() * ((double) hi[j] - lo[j]);
        if (binary && rnd.nextInt(4) == 0) {
          value[j] = rnd.nextBoolean() ? 1 : 0;
        }
      }
      long b = rnd.nextInt(60) - 5L;
      MirCut cut = CoverCut.of(columns, c, b, value, lo, hi);
      if (cut == null) {
        continue;
      }
      made++;
      int positives = 0;
      double activity = 0;
      double norm = 0;
      for (int k = 0; k < cut.columns.length; k++) {
        activity += cut.weights[k] * value[cut.columns[k]];
        norm += (double) cut.weights[k] * cut.weights[k];
        positives += cut.weights[k] != 0 ? 1 : 0;
      }
      assertThat((activity - cut.rhs) / Math.sqrt(norm))
          .as("run %d efficacy", run)
          .isGreaterThan(MirCut.MIN_EFFICACY);
      if (Arrays.stream(cut.weights).map(Math::abs).distinct().count() > 1) {
        lifted++;
      }
      assertThat(positives).isGreaterThanOrEqualTo(2);
      long[] p = lo.clone();
      while (p != null) {
        long row = 0;
        for (int j = 0; j < n; j++) {
          row += c[j] * p[j];
        }
        if (row <= b) {
          long lhs = 0;
          for (int k = 0; k < cut.columns.length; k++) {
            lhs += cut.weights[k] * p[cut.columns[k]];
          }
          assertThat(lhs)
              .as(
                  "run %d row %s <= %d cut %s at %s",
                  run, Arrays.toString(c), b, cut, Arrays.toString(p))
              .isLessThanOrEqualTo(cut.rhs);
        }
        p = next(p, lo, hi);
      }
    }
    assertThat(made).isGreaterThan(2000);
    assertThat(lifted).isGreaterThan(200);
  }

  @Test
  void liftsTheItemsOutsideTheCover() {
    // 5 y1 + 5 y2 + 5 y3 + 9 y4 <= 12: cover {1, 2, 3} (lambda 3), and y4 alone uses 9 of 12
    int[] columns = {0, 1, 2, 3};
    long[] c = {5, 5, 5, 9};
    double[] value = {0.9, 0.9, 0.6, 0};
    long[] lo = {0, 0, 0, 0};
    long[] hi = {1, 1, 1, 1};
    MirCut cut = CoverCut.of(columns, c, 12, value, lo, hi);
    assertThat(cut).isNotNull();
    // mu = 5, 10, 15 and rho_1 = rho_2 = 3: 9 lies in (mu_2 - lambda, mu_2 - lambda + rho_2], so
    // g(9) = 2 - (10 - 3 + 3 - 9) / 3 = 5 / 3 (the exact lifting gives 2)
    assertThat(cut.weights).containsExactly(3L, 3L, 3L, 5L);
    assertThat(cut.rhs).isEqualTo(6);
  }

  @Test
  void complementsNegativeWeights() {
    // 4 x0 + 4 x1 - 4 x2 <= 3 is the knapsack 4 x0 + 4 x1 + 4 (1 - x2) <= 7 with the cover {x0,
    // x1};
    // 1 - x2 is lifted with weight 1, so x0 + x1 + (1 - x2) <= 1
    int[] columns = {0, 1, 2};
    long[] c = {4, 4, -4};
    double[] value = {1, 0.75, 1};
    long[] lo = {0, 0, 0};
    long[] hi = {1, 1, 1};
    MirCut cut = CoverCut.of(columns, c, 3, value, lo, hi);
    assertThat(cut).isNotNull();
    assertThat(cut.columns).containsExactly(0, 1, 2);
    long d = cut.weights[0];
    assertThat(cut.weights).containsExactly(d, d, -d);
    assertThat(cut.rhs).isEqualTo(0);
  }

  private static long[] next(long[] p, long[] lo, long[] hi) {
    for (int j = 0; j < p.length; j++) {
      if (p[j] < hi[j]) {
        p[j]++;
        return p;
      }
      p[j] = lo[j];
    }
    return null;
  }
}
