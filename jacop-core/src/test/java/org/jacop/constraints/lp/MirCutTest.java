/*
 * MirCutTest.java
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

import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests MIR cuts against enumeration: on random integer rows with small bounds and random LP
 * points, every integer point within the bounds that meets the row must meet the cut, and the cut
 * must cut off the LP point by its efficacy.
 */
class MirCutTest {

  @Test
  void cutsKeepEveryIntegerPointOfTheRow() {
    Random rnd = new Random(11);
    int made = 0;
    for (int run = 0; run < 20000; run++) {
      int n = 2 + rnd.nextInt(3);
      long[] c = new long[n];
      long[] lo = new long[n];
      long[] hi = new long[n];
      double[] value = new double[n];
      for (int j = 0; j < n; j++) {
        c[j] = rnd.nextInt(4) == 0 ? 0 : rnd.nextInt(41) - 20L;
        lo[j] = rnd.nextInt(7) - 3L;
        hi[j] = lo[j] + rnd.nextInt(5);
        value[j] = lo[j] + rnd.nextDouble() * ((double) hi[j] - lo[j]);
      }
      long b = rnd.nextInt(61) - 30L;
      MirCut cut = MirCut.of(c, b, value, lo, hi);
      if (cut == null) {
        continue;
      }
      made++;
      double activity = 0;
      double norm = 0;
      for (int k = 0; k < cut.columns.length; k++) {
        activity += (double) cut.weights[k] * value[cut.columns[k]];
        norm += (double) cut.weights[k] * cut.weights[k];
      }
      assertThat((activity - cut.rhs) / Math.sqrt(norm))
          .as("run %d efficacy", run)
          .isGreaterThan(MirCut.MIN_EFFICACY);
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
              .as("run %d cut %s at %s", run, cut, java.util.Arrays.toString(p))
              .isLessThanOrEqualTo(cut.rhs);
        }
        p = next(p, lo, hi);
      }
    }
    assertThat(made).isGreaterThan(1000);
  }

  @Test
  void sparseRowGivesTheCutOfTheCompactRow() {
    Random rnd = new Random(5);
    int wide = 1 << 20;
    double[] value = new double[wide];
    long[] lo = new long[wide];
    long[] hi = new long[wide];
    int made = 0;
    for (int run = 0; run < 2000; run++) {
      int n = 2 + rnd.nextInt(4);
      long[] c = new long[n];
      long[] clo = new long[n];
      long[] chi = new long[n];
      double[] cvalue = new double[n];
      int[] columns = new int[n];
      for (int j = 0; j < n; j++) {
        c[j] = rnd.nextInt(41) - 20L;
        clo[j] = rnd.nextInt(7) - 3L;
        chi[j] = clo[j] + rnd.nextInt(5);
        cvalue[j] = clo[j] + rnd.nextDouble() * ((double) chi[j] - clo[j]);
        // ascending, spread over the wide range of columns
        columns[j] = j * (wide / n) + rnd.nextInt(wide / n);
        lo[columns[j]] = clo[j];
        hi[columns[j]] = chi[j];
        value[columns[j]] = cvalue[j];
      }
      long b = rnd.nextInt(61) - 30L;
      MirCut compact = MirCut.of(c, b, cvalue, clo, chi);
      MirCut sparse = MirCut.of(columns, c, b, value, lo, hi);
      if (compact == null) {
        assertThat(sparse).as("run %d", run).isNull();
        continue;
      }
      made++;
      assertThat(sparse).as("run %d", run).isNotNull();
      int[] mapped = new int[compact.columns.length];
      for (int k = 0; k < mapped.length; k++) {
        mapped[k] = columns[compact.columns[k]];
      }
      assertThat(sparse.columns).as("run %d", run).containsExactly(mapped);
      assertThat(sparse.weights).as("run %d", run).containsExactly(compact.weights);
      assertThat(sparse.rhs).as("run %d", run).isEqualTo(compact.rhs);
    }
    assertThat(made).isGreaterThan(100);
  }

  @Test
  void reducedCutKeepsEveryIntegerPointOfTheCut() {
    Random rnd = new Random(23);
    int reduced = 0;
    for (int run = 0; run < 20000; run++) {
      int n = 2 + rnd.nextInt(3);
      int[] columns = new int[n];
      long[] w = new long[n];
      long[] lo = new long[n];
      long[] hi = new long[n];
      double[] value = new double[n];
      for (int j = 0; j < n; j++) {
        columns[j] = j;
        // weights far apart and large, as in a Gomory cut over slacks
        w[j] =
            (rnd.nextBoolean() ? 1 : -1)
                * (long) Math.pow(10, rnd.nextInt(7))
                * (1 + rnd.nextInt(9));
        lo[j] = rnd.nextInt(7) - 3L;
        hi[j] = lo[j] + rnd.nextInt(5);
        value[j] = rnd.nextBoolean() ? lo[j] : hi[j];
      }
      long rhs = 0;
      for (int j = 0; j < n; j++) {
        rhs += w[j] * (rnd.nextBoolean() ? lo[j] : hi[j]);
      }
      long[] q = w.clone();
      long divisor = 1L << (1 + rnd.nextInt(20));
      long right = MirCut.reduce(columns, q, rhs, divisor, rnd.nextInt(1000), value, lo, hi);
      reduced++;
      long[] p = lo.clone();
      while (p != null) {
        long full = 0;
        long small = 0;
        for (int j = 0; j < n; j++) {
          full += w[j] * p[j];
          small += q[j] * p[j];
        }
        if (full <= rhs) {
          assertThat(small)
              .as(
                  "run %d %s / %d at %s",
                  run, java.util.Arrays.toString(w), divisor, java.util.Arrays.toString(p))
              .isLessThanOrEqualTo(right);
        }
        p = next(p, lo, hi);
      }
    }
    assertThat(reduced).isEqualTo(20000);
  }

  @Test
  void finishScalesLargeWeightsDown() {
    // 100000003 x0 + 7 x1 - 99999999 x2 <= 5 over [0, 3]: weights too large and too far apart
    int[] columns = {0, 1, 2};
    long[] g = {100000003, 7, -99999999};
    long[] lo = {0, 0, 0};
    long[] hi = {3, 3, 3};
    double[] value = {1.5, 0, 1};
    assertThat(MirCut.finish(columns, g, 5, value, lo, hi, false)).isNull();
    MirCut c = MirCut.finish(columns, g, 5, value, lo, hi, true);
    assertThat(c).isNotNull();
    long largest = 0;
    for (long w : c.weights) {
      largest = Math.max(largest, Math.abs(w));
    }
    assertThat(largest).isLessThanOrEqualTo(1L << 24);
    assertThat(c.columns).containsExactly(0, 2);
    assertThat(c.efficacy).isGreaterThan(MirCut.MIN_EFFICACY);
  }

  // the next point of the box in lexicographic order, or null
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
