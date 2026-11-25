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
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
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

  /**
   * MIR cuts with variable bounds substituted ({@link MirCut#ofVariableBounds}) hold at every
   * integer point that meets the row, the variable bounds and the column bounds; the factors of the
   * variable bounds may be larger than the upper bound of their column.
   */
  @Test
  void variableBoundCutsKeepEveryIntegerPointOfTheRowAndBounds() {
    Random rnd = new Random(17);
    int made = 0;
    for (int run = 0; run < 100000; run++) {
      int general = 1 + rnd.nextInt(3);
      int binary = 1 + rnd.nextInt(2);
      int n = general + binary;
      long[] c = new long[n];
      long[] lo = new long[n];
      long[] hi = new long[n];
      double[] value = new double[n];
      for (int j = 0; j < n; j++) {
        c[j] = rnd.nextInt(5) == 0 ? 0 : rnd.nextInt(41) - 20L;
        lo[j] = j < general ? rnd.nextInt(2) : 0;
        hi[j] = j < general ? lo[j] + 2 + rnd.nextInt(5) : 1;
        value[j] = lo[j] + rnd.nextDouble() * ((double) hi[j] - lo[j]);
      }
      // variable bounds x_j <= a u (rows x - a u <= 0) and x_j >= a u (rows x - a u >= 0)
      java.util.List<int[]> rows = new java.util.ArrayList<>();
      java.util.List<long[]> weights = new java.util.ArrayList<>();
      java.util.List<Long> upper = new java.util.ArrayList<>();
      java.util.List<Long> lower = new java.util.ArrayList<>();
      int bounds = 1 + rnd.nextInt(3);
      for (int k = 0; k < bounds; k++) {
        int x = rnd.nextInt(general);
        int u = general + rnd.nextInt(binary);
        long a = 1 + rnd.nextInt((int) hi[x] + 4);
        boolean flip = rnd.nextBoolean();
        rows.add(flip ? new int[] {u, x} : new int[] {x, u});
        weights.add(flip ? new long[] {a, -1} : new long[] {1, -a});
        boolean up = rnd.nextBoolean();
        // flipped, the row is -x + a u, whose sides are the negated sides of x - a u
        upper.add(up != flip ? 0L : null);
        lower.add(up != flip ? null : 0L);
        if (rnd.nextBoolean()) {
          // an LP point near the variable bound, where it is substituted
          double near = a * value[u] + (up ? -1 : 1) * 0.3 * rnd.nextDouble();
          value[x] = Math.clamp(near, (double) lo[x], (double) hi[x]);
        }
      }
      MirCut.VariableBounds vb = MirCut.VariableBounds.of(n, rows, weights, upper, lower, lo, hi);
      if (vb == null) {
        continue;
      }
      long b = rnd.nextInt(81) - 40L;
      int[] columns = new int[n];
      for (int j = 0; j < n; j++) {
        columns[j] = j;
      }
      MirCut cut = MirCut.ofVariableBounds(columns, c, b, value, lo, hi, vb);
      if (cut == null) {
        continue;
      }
      made++;
      long[] p = lo.clone();
      while (p != null) {
        boolean feasible = true;
        long row = 0;
        for (int j = 0; j < n; j++) {
          row += c[j] * p[j];
        }
        feasible = row <= b;
        for (int k = 0; k < rows.size() && feasible; k++) {
          long r = weights.get(k)[0] * p[rows.get(k)[0]] + weights.get(k)[1] * p[rows.get(k)[1]];
          feasible =
              (upper.get(k) == null || r <= upper.get(k))
                  && (lower.get(k) == null || r >= lower.get(k));
        }
        if (feasible) {
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
    assertThat(made).isGreaterThan(500);
  }

  /**
   * A cut scaled down to a smaller largest weight ({@link MirCut#capped}, the cuts made in search)
   * still holds at every integer point of the row and keeps its weights within the cap.
   */
  @Test
  void cappedCutsKeepEveryIntegerPointOfTheRow() {
    Random rnd = new Random(13);
    int scaled = 0;
    for (int run = 0; run < 20000; run++) {
      int n = 2 + rnd.nextInt(3);
      long[] c = new long[n];
      long[] lo = new long[n];
      long[] hi = new long[n];
      double[] value = new double[n];
      for (int j = 0; j < n; j++) {
        c[j] = rnd.nextInt(4) == 0 ? 0 : rnd.nextInt(2001) - 1000L;
        lo[j] = rnd.nextInt(7) - 3L;
        hi[j] = lo[j] + rnd.nextInt(5);
        value[j] = lo[j] + rnd.nextDouble() * ((double) hi[j] - lo[j]);
      }
      long b = rnd.nextInt(3001) - 1500L;
      MirCut full = MirCut.of(c, b, value, lo, hi);
      if (full == null) {
        continue;
      }
      long cap = 1L << (2 + rnd.nextInt(6));
      MirCut cut = MirCut.capped(full, cap, value, lo, hi);
      if (cut == null || cut == full) {
        continue;
      }
      scaled++;
      for (long w : cut.weights) {
        assertThat(Math.abs(w)).as("run %d", run).isLessThanOrEqualTo(cap);
      }
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
    assertThat(scaled).isGreaterThan(100);
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

  /**
   * Fixed-charge models (x_k <= cap_k u_k, demand rows, cost f u + c x) keep their optimum with the
   * MIR cuts with variable bounds of the rows and of the Gomory rows of the root, and their root
   * bounds stay below it.
   */
  @Test
  void variableBoundCutsOfRowsAndGomoryRowsKeepTheOptimum() {
    Random rnd = new Random(5);
    boolean wasMir = LinearRelaxation.vbMirOn;
    boolean wasGomory = LinearRelaxation.vbGomoryOn;
    LinearRelaxation.vbMirOn = true;
    LinearRelaxation.vbGomoryOn = true;
    long vbCuts = 0;
    try {
      for (int run = 0; run < 60; run++) {
        int n = 3 + rnd.nextInt(4);
        int[] cap = new int[n];
        int[] fixed = new int[n];
        int[] unit = new int[n];
        int total = 0;
        for (int k = 0; k < n; k++) {
          cap[k] = 3 + rnd.nextInt(12);
          fixed[k] = 5 + rnd.nextInt(40);
          unit[k] = 1 + rnd.nextInt(6);
          total += cap[k];
        }
        int demand = 1 + rnd.nextInt(Math.max(1, total * 2 / 3));
        int second = rnd.nextBoolean() ? 1 + rnd.nextInt(Math.max(1, total / 2)) : 0;
        long expected = new FixedCharge(cap, fixed, unit, demand, second).optimum();
        FixedCharge m = new FixedCharge(cap, fixed, unit, demand, second);
        LinearRelaxation r = LinearRelaxation.of(m.store, m.cost, false);
        assertThat(r).as("run %d", run).isNotNull();
        m.store.impose(r);
        assertThat(m.optimum()).as("run %d", run).isEqualTo(expected);
        if (expected != Long.MIN_VALUE) {
          assertThat(r.rootBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
          if (!Double.isNaN(r.cutBound)) {
            assertThat(r.cutBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
          }
        }
        vbCuts += r.vbCuts;
      }
    } finally {
      LinearRelaxation.vbMirOn = wasMir;
      LinearRelaxation.vbGomoryOn = wasGomory;
    }
    assertThat(vbCuts).isPositive();
  }

  // min sum f u + c x, x_k <= cap_k u_k, sum x >= demand, and x_0 + x_1 >= second
  private static final class FixedCharge {
    final Store store = new Store();
    final IntVar[] vars;
    final IntVar cost;

    FixedCharge(int[] cap, int[] fixed, int[] unit, int demand, int second) {
      int n = cap.length;
      IntVar[] x = new IntVar[n];
      IntVar[] u = new IntVar[n];
      int most = 0;
      for (int k = 0; k < n; k++) {
        x[k] = new IntVar(store, "x" + k, 0, cap[k]);
        u[k] = new IntVar(store, "u" + k, 0, 1);
        store.impose(new LinearInt(new IntVar[] {x[k], u[k]}, new int[] {1, -cap[k]}, "<=", 0));
        most += fixed[k] + unit[k] * cap[k];
      }
      int[] ones = new int[n];
      java.util.Arrays.fill(ones, 1);
      store.impose(new LinearInt(x, ones, ">=", demand));
      if (second > 0) {
        store.impose(new LinearInt(new IntVar[] {x[0], x[1]}, new int[] {1, 1}, ">=", second));
      }
      cost = new IntVar(store, "cost", 0, most);
      IntVar[] all = new IntVar[2 * n + 1];
      int[] ws = new int[2 * n + 1];
      for (int k = 0; k < n; k++) {
        all[k] = u[k];
        ws[k] = fixed[k];
        all[n + k] = x[k];
        ws[n + k] = unit[k];
      }
      all[2 * n] = cost;
      ws[2 * n] = -1;
      store.impose(new LinearInt(all, ws, "==", 0));
      vars = new IntVar[2 * n];
      System.arraycopy(u, 0, vars, 0, n);
      System.arraycopy(x, 0, vars, n, n);
    }

    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(store, new InputOrderSelect<>(store, vars, new IndomainMin<>()), cost);
      return found ? search.getCostValue() : Long.MIN_VALUE;
    }
  }
}
