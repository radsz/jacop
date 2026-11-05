/*
 * HighsLpTest.java
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

package org.jacop.jalp;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.util.Arrays;
import java.util.Random;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

/**
 * Tests {@link HighsLp} against {@link RevisedDualSimplex} on random bounded LPs: the same status
 * and objective, duals with the signs of JaLP's (checked by complementary slackness), Farkas rays
 * that prove infeasibility over the bounds, rows of the basis inverse with coefficient one on their
 * basic column and zero on the others, and warm solves after bound changes, added and removed rows
 * and copies that agree with fresh ones. Skipped when the HiGHS library is not available.
 */
class HighsLpTest {

  private static final double INF = Double.POSITIVE_INFINITY;
  private static final double TOL = 1e-6;

  @BeforeAll
  static void library() {
    assumeTrue(HighsLp.available(), "HiGHS library not available: " + HighsLp.loadError());
  }

  // a random LP with bounded columns, by rows
  private static final class Lp {
    final int n;
    int[][] cols;
    double[][] vals;
    double[] rowLo;
    double[] rowHi;
    final double[] cost;
    final double[] lo;
    final double[] hi;

    Lp(Random rnd, int m, int n, double density) {
      this.n = n;
      cols = new int[m][];
      vals = new double[m][];
      rowLo = new double[m];
      rowHi = new double[m];
      for (int i = 0; i < m; i++) {
        int[] c = new int[n];
        double[] v = new double[n];
        int k = 0;
        for (int j = 0; j < n; j++) {
          int a = rnd.nextInt(11) - 5;
          if (rnd.nextDouble() < density && a != 0) {
            c[k] = j;
            v[k++] = a;
          }
        }
        cols[i] = Arrays.copyOf(c, k);
        vals[i] = Arrays.copyOf(v, k);
        int kind = rnd.nextInt(3);
        double b = rnd.nextInt(21) - 10.0;
        rowLo[i] = kind == 0 ? -INF : b;
        rowHi[i] = kind == 1 ? INF : b + rnd.nextInt(3);
      }
      cost = new double[n];
      lo = new double[n];
      hi = new double[n];
      for (int j = 0; j < n; j++) {
        cost[j] = rnd.nextInt(7) - 3.0;
        lo[j] = rnd.nextInt(7) - 3.0;
        hi[j] = lo[j] + rnd.nextInt(5);
      }
    }

    RevisedDualSimplex jalp() {
      RevisedDualSimplex lp = new RevisedDualSimplex(cols, vals, rowLo, rowHi, cost, true);
      lp.setExact(true);
      for (int j = 0; j < n; j++) {
        lp.setBounds(j, lo[j], hi[j]);
      }
      return lp;
    }

    HighsLp highs() {
      HighsLp lp = new HighsLp(cols, vals, rowLo, rowHi, cost);
      for (int j = 0; j < n; j++) {
        lp.setBounds(j, lo[j], hi[j]);
      }
      return lp;
    }

    double activity(int i, HighsLp lp) {
      double s = 0;
      for (int e = 0; e < cols[i].length; e++) {
        s += vals[i][e] * lp.value(cols[i][e]);
      }
      return s;
    }

    // the coefficient of column p in y [A -I]
    double coefficient(double[] y, int p) {
      if (p >= n) {
        return -y[p - n];
      }
      double s = 0;
      for (int i = 0; i < cols.length; i++) {
        for (int e = 0; e < cols[i].length; e++) {
          if (cols[i][e] == p) {
            s += y[i] * vals[i][e];
          }
        }
      }
      return s;
    }
  }

  // checks an optimum of HiGHS: feasible values, and duals whose signs fit the active sides
  private static void checkOptimal(Lp p, HighsLp lp) {
    int m = p.cols.length;
    double[] y = lp.duals();
    double z = 0;
    for (int j = 0; j < p.n; j++) {
      double v = lp.value(j);
      assertThat(v).isBetween(p.lo[j] - TOL, p.hi[j] + TOL);
      z += p.cost[j] * v;
      double d = p.cost[j] - p.coefficient(y, j);
      if (d > TOL) {
        assertThat(v).isCloseTo(p.lo[j], org.assertj.core.data.Offset.offset(TOL));
      } else if (d < -TOL) {
        assertThat(v).isCloseTo(p.hi[j], org.assertj.core.data.Offset.offset(TOL));
      }
    }
    for (int i = 0; i < m; i++) {
      double a = p.activity(i, lp);
      assertThat(lp.value(p.n + i)).isCloseTo(a, org.assertj.core.data.Offset.offset(TOL));
      assertThat(a).isBetween(p.rowLo[i] - TOL, p.rowHi[i] + TOL);
      // the slack column -e_i has reduced cost y_i: positive at the lower side, negative at the
      // upper
      if (y[i] > TOL) {
        assertThat(a).isCloseTo(p.rowLo[i], org.assertj.core.data.Offset.offset(TOL));
      } else if (y[i] < -TOL) {
        assertThat(a).isCloseTo(p.rowHi[i], org.assertj.core.data.Offset.offset(TOL));
      }
    }
    assertThat(lp.objective()).isCloseTo(z, org.assertj.core.data.Offset.offset(1e-5));
  }

  // checks that y [A -I] (x, s) = 0 has no solution within the bounds
  private static void checkFarkas(Lp p, double[] y) {
    double min = 0;
    double max = 0;
    for (int j = 0; j < p.n; j++) {
      double c = p.coefficient(y, j);
      min += c > 0 ? c * p.lo[j] : c * p.hi[j];
      max += c > 0 ? c * p.hi[j] : c * p.lo[j];
    }
    for (int i = 0; i < y.length; i++) {
      double c = -y[i];
      if (c != 0) {
        min += c > 0 ? c * p.rowLo[i] : c * p.rowHi[i];
        max += c > 0 ? c * p.rowHi[i] : c * p.rowLo[i];
      }
    }
    assertThat(min > 1e-7 || max < -1e-7)
        .as(
            "Farkas interval [%s, %s] y %s rows %s %s %s lo %s hi %s",
            min,
            max,
            Arrays.toString(y),
            Arrays.deepToString(p.vals),
            Arrays.toString(p.rowLo),
            Arrays.toString(p.rowHi),
            Arrays.toString(p.lo),
            Arrays.toString(p.hi))
        .isTrue();
  }

  private static void checkInverse(Lp p, HighsLp lp) {
    int m = p.cols.length;
    System.err.println(
        "DBG m "
            + m
            + " n "
            + p.n
            + " rows "
            + Arrays.deepToString(p.vals)
            + " "
            + Arrays.toString(p.rowLo)
            + Arrays.toString(p.rowHi)
            + Arrays.toString(p.lo)
            + Arrays.toString(p.hi)
            + Arrays.toString(p.cost)
            + " "
            + Arrays.deepToString(p.cols));
    for (int r = 0; r < m; r++) {
      double[] y = lp.inverseRow(r);
      for (int j = 0; j < p.n + m; j++) {
        int row = lp.basicRow(j);
        if (row >= 0) {
          double c = p.coefficient(y, j);
          assertThat(c).isCloseTo(row == r ? 1 : 0, org.assertj.core.data.Offset.offset(1e-7));
        }
      }
    }
  }

  private static void compare(Lp p, HighsLp lp, int status) {
    RevisedDualSimplex ref = p.jalp();
    int expected = ref.solve(100_000);
    assertThat(status).isEqualTo(expected);
    if (status == HighsLp.OPTIMAL) {
      assertThat(lp.objective())
          .isCloseTo(ref.objective(), org.assertj.core.data.Offset.offset(1e-5));
      checkOptimal(p, lp);
      checkInverse(p, lp);
    } else if (status == HighsLp.INFEASIBLE) {
      checkFarkas(p, lp.farkas());
    }
  }

  @Test
  void agreesWithJalp() {
    Random rnd = new Random(1);
    int[] seen = new int[4];
    for (int t = 0; t < 300; t++) {
      Lp p = new Lp(rnd, 2 + rnd.nextInt(12), 2 + rnd.nextInt(12), 0.5);
      HighsLp lp = p.highs();
      int status = lp.solve(100_000);
      seen[status]++;
      compare(p, lp, status);
      // warm solves after bound changes
      for (int round = 0; round < 3; round++) {
        int j = rnd.nextInt(p.n);
        if (rnd.nextBoolean()) {
          p.lo[j] = Math.min(p.hi[j], p.lo[j] + 1);
        } else {
          p.hi[j] = Math.max(p.lo[j], p.hi[j] - 1);
        }
        lp.setBounds(j, p.lo[j], p.hi[j]);
        compare(p, lp, lp.solve(100_000));
      }
    }
    assertThat(seen[HighsLp.OPTIMAL]).isPositive();
    assertThat(seen[HighsLp.INFEASIBLE]).isPositive();
  }

  @Test
  void rowsAddedRemovedAndCopies() {
    Random rnd = new Random(2);
    for (int t = 0; t < 100; t++) {
      Lp p = new Lp(rnd, 3 + rnd.nextInt(8), 3 + rnd.nextInt(8), 0.5);
      HighsLp lp = p.highs();
      lp.solve(100_000);
      Lp extra = new Lp(rnd, 1 + rnd.nextInt(3), p.n, 0.5);
      lp.addRows(extra.cols, extra.vals, extra.rowLo, extra.rowHi);
      int m = p.cols.length;
      p.cols = concat(p.cols, extra.cols);
      p.vals = concat(p.vals, extra.vals);
      p.rowLo = concat(p.rowLo, extra.rowLo);
      p.rowHi = concat(p.rowHi, extra.rowHi);
      assertThat(lp.rows()).isEqualTo(p.cols.length);
      HighsLp copy = lp.copy();
      compare(p, lp, lp.solve(100_000));
      compare(p, copy, copy.solve(100_000));
      int[] all = new int[p.cols.length];
      for (int i = 0; i < all.length; i++) {
        all[i] = i;
      }
      int[] old = lp.removeRows(all);
      if (old != null) {
        assertThat(old.length).isEqualTo(lp.rows()).isLessThan(all.length);
        Lp q = p;
        q.cols = Arrays.stream(old).mapToObj(i -> p.cols[i]).toArray(int[][]::new);
        q.vals = Arrays.stream(old).mapToObj(i -> p.vals[i]).toArray(double[][]::new);
        q.rowLo = Arrays.stream(old).mapToDouble(i -> p.rowLo[i]).toArray();
        q.rowHi = Arrays.stream(old).mapToDouble(i -> p.rowHi[i]).toArray();
        compare(q, lp, lp.solve(100_000));
      }
      assertThat(m).isPositive();
    }
  }

  @Test
  void iterationLimitPerSolve() {
    Random rnd = new Random(3);
    Lp p = new Lp(rnd, 40, 40, 0.5);
    HighsLp lp = p.highs();
    int status = lp.solve(1);
    assertThat(lp.pivots()).isLessThanOrEqualTo(1);
    long before = lp.pivots();
    if (status == HighsLp.LIMIT) {
      lp.solve(100_000);
      assertThat(lp.pivots()).isGreaterThan(before);
    }
  }

  private static <T> T[] concat(T[] a, T[] b) {
    T[] c = Arrays.copyOf(a, a.length + b.length);
    System.arraycopy(b, 0, c, a.length, b.length);
    return c;
  }

  private static double[] concat(double[] a, double[] b) {
    double[] c = Arrays.copyOf(a, a.length + b.length);
    System.arraycopy(b, 0, c, a.length, b.length);
    return c;
  }
}
