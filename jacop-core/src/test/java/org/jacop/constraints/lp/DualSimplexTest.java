/*
 * DualSimplexTest.java
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
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests the dual simplex on random bounded LPs with certificates it must give: at an optimal basis
 * the solution is within every bound and the dual values give a matching bound; at an infeasible
 * row the row of the basis inverse combines the rows into one that cannot be met within the bounds.
 * Re-solves with tightened bounds check the warm start.
 */
class DualSimplexTest {

  private static final double TOL = 1e-6;

  /**
   * A Farkas ray from the simplex carries rounding noise: here 1e-11 on the row x &lt;= 5, whose
   * lower side is infinite. x &gt;= 2 alone proves x in [0, 1] infeasible, so the check must accept
   * the ray, and still reject one whose second multiplier is not noise.
   */
  @Test
  void farkasCheckIgnoresRoundingNoise() {
    double inf = Double.POSITIVE_INFINITY;
    double[][] a = {{1}, {1}};
    double[] rowLo = {2, -inf};
    double[] rowHi = {inf, 5};
    double[] lo = {0};
    double[] hi = {1};
    checkFarkas(new double[] {1, 1e-11}, a, rowLo, rowHi, lo, hi, 0);
    assertThatThrownBy(() -> checkFarkas(new double[] {1, 0.5}, a, rowLo, rowHi, lo, hi, 0))
        .isInstanceOf(AssertionError.class);
  }

  @Test
  void randomLpsGiveCertificates() {
    Random rnd = new Random(3);
    int optimal = 0;
    int infeasible = 0;
    for (int run = 0; run < 3000; run++) {
      int m = 1 + rnd.nextInt(6);
      int n = 2 + rnd.nextInt(7);
      double[][] a = new double[m][n];
      double[] rowLo = new double[m];
      double[] rowHi = new double[m];
      for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
          a[i][j] = rnd.nextInt(3) == 0 ? 0 : rnd.nextInt(11) - 5;
        }
        int kind = rnd.nextInt(3);
        int c = rnd.nextInt(21) - 10;
        rowLo[i] = kind == 0 ? Double.NEGATIVE_INFINITY : c;
        rowHi[i] = kind == 1 ? Double.POSITIVE_INFINITY : c + (kind == 2 ? rnd.nextInt(3) : 0);
      }
      double[] cost = new double[n];
      if (rnd.nextBoolean()) {
        for (int j = 0; j < n; j++) {
          cost[j] = rnd.nextInt(5) - 2;
        }
      }
      double[] lo = new double[n];
      double[] hi = new double[n];
      for (int j = 0; j < n; j++) {
        lo[j] = rnd.nextInt(5) - 3;
        hi[j] = lo[j] + rnd.nextInt(5);
      }
      DualSimplex lp = new DualSimplex(a, rowLo, rowHi, cost);
      for (int step = 0; step < 4; step++) {
        for (int j = 0; j < n; j++) {
          lp.setBounds(j, lo[j], hi[j]);
        }
        int status = lp.solve(1000);
        assertThat(status).as("run %d step %d", run, step).isNotEqualTo(DualSimplex.LIMIT);
        if (status == DualSimplex.OPTIMAL) {
          optimal++;
          checkOptimal(lp, a, rowLo, rowHi, cost, lo, hi, run);
        } else {
          infeasible++;
          checkFarkas(lp.farkas(), a, rowLo, rowHi, lo, hi, run);
          break;
        }
        // tighten one bound and solve again from the same basis
        int j = rnd.nextInt(n);
        if (rnd.nextBoolean()) {
          lo[j] = Math.min(hi[j], lo[j] + 1 + rnd.nextInt(2));
        } else {
          hi[j] = Math.max(lo[j], hi[j] - 1 - rnd.nextInt(2));
        }
      }
    }
    assertThat(optimal).isGreaterThan(1000);
    assertThat(infeasible).isGreaterThan(300);
  }

  @Test
  void addedRowsKeepTheBasisAndGiveCertificates() {
    Random rnd = new Random(5);
    int optimal = 0;
    int infeasible = 0;
    for (int run = 0; run < 2000; run++) {
      int m = 1 + rnd.nextInt(5);
      int n = 2 + rnd.nextInt(7);
      int extra = 1 + rnd.nextInt(4);
      double[][] a = new double[m + extra][n];
      double[] rowLo = new double[m + extra];
      double[] rowHi = new double[m + extra];
      for (int i = 0; i < m + extra; i++) {
        for (int j = 0; j < n; j++) {
          a[i][j] = rnd.nextInt(3) == 0 ? 0 : rnd.nextInt(11) - 5.0;
        }
        int kind = rnd.nextInt(3);
        double c = rnd.nextInt(21) - 10.0;
        rowLo[i] = kind == 0 ? Double.NEGATIVE_INFINITY : c;
        rowHi[i] = kind == 1 ? Double.POSITIVE_INFINITY : c + (kind == 2 ? rnd.nextInt(3) : 0);
      }
      double[] cost = new double[n];
      for (int j = 0; j < n; j++) {
        cost[j] = rnd.nextInt(5) - 2.0;
      }
      double[] lo = new double[n];
      double[] hi = new double[n];
      for (int j = 0; j < n; j++) {
        lo[j] = rnd.nextInt(5) - 3.0;
        hi[j] = lo[j] + rnd.nextInt(5);
      }
      DualSimplex lp =
          new DualSimplex(
              java.util.Arrays.copyOf(a, m),
              java.util.Arrays.copyOf(rowLo, m),
              java.util.Arrays.copyOf(rowHi, m),
              cost);
      for (int j = 0; j < n; j++) {
        lp.setBounds(j, lo[j], hi[j]);
      }
      if (lp.solve(1000) != DualSimplex.OPTIMAL) {
        continue;
      }
      lp.addRows(
          java.util.Arrays.copyOfRange(a, m, m + extra),
          java.util.Arrays.copyOfRange(rowLo, m, m + extra),
          java.util.Arrays.copyOfRange(rowHi, m, m + extra));
      int status = lp.solve(1000);
      DualSimplex fresh = new DualSimplex(a, rowLo, rowHi, cost);
      for (int j = 0; j < n; j++) {
        fresh.setBounds(j, lo[j], hi[j]);
      }
      int expected = fresh.solve(1000);
      assertThat(status).as("run %d", run).isEqualTo(expected);
      if (status == DualSimplex.OPTIMAL) {
        optimal++;
        checkOptimal(lp, a, rowLo, rowHi, cost, lo, hi, run);
        assertThat(lp.objective())
            .as("run %d objective", run)
            .isCloseTo(fresh.objective(), org.assertj.core.data.Offset.offset(1e-5));
      } else {
        infeasible++;
        checkFarkas(lp.farkas(), a, rowLo, rowHi, lo, hi, run);
      }
    }
    assertThat(optimal).isGreaterThan(200);
    assertThat(infeasible).isGreaterThan(200);
  }

  @Test
  void aRestoredBasisSolvesTheBoundsItWasSavedForAgain() {
    Random rnd = new Random(7);
    int restored = 0;
    for (int run = 0; run < 500; run++) {
      int m = 2 + rnd.nextInt(6);
      int n = 3 + rnd.nextInt(7);
      double[][] a = new double[m][n];
      double[] rowLo = new double[m];
      double[] rowHi = new double[m];
      for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
          a[i][j] = rnd.nextInt(3) == 0 ? 0 : rnd.nextInt(11) - 5;
        }
        rowLo[i] = rnd.nextInt(11) - 10.0;
        rowHi[i] = rowLo[i] + rnd.nextInt(20);
      }
      double[] cost = new double[n];
      for (int j = 0; j < n; j++) {
        cost[j] = rnd.nextInt(5) - 2.0;
      }
      double[] lo = new double[n];
      double[] hi = new double[n];
      java.util.Arrays.fill(lo, -5);
      java.util.Arrays.fill(hi, 5);
      DualSimplex lp = new DualSimplex(a, rowLo, rowHi, cost);
      for (int j = 0; j < n; j++) {
        lp.setBounds(j, lo[j], hi[j]);
      }
      if (lp.solve(1000) != DualSimplex.OPTIMAL) {
        continue;
      }
      double root = lp.objective();
      Object saved = lp.saveBasis();
      // a dive: bounds narrowed around the solution until infeasible or five steps
      for (int step = 0; step < 5; step++) {
        int j = rnd.nextInt(n);
        double v = Math.rint(lp.value(j));
        lp.setBounds(j, Math.max(lo[j], v - 1), Math.min(hi[j], v));
        if (lp.solve(1000) != DualSimplex.OPTIMAL) {
          break;
        }
      }
      for (int j = 0; j < n; j++) {
        lp.setBounds(j, lo[j], hi[j]);
      }
      assertThat(lp.restoreBasis(saved)).isTrue();
      restored++;
      long before = lp.pivots();
      assertThat(lp.solve(1000)).isEqualTo(DualSimplex.OPTIMAL);
      assertThat(lp.pivots() - before).as("run %d", run).isZero();
      assertThat(lp.objective()).isCloseTo(root, org.assertj.core.data.Offset.offset(1e-9));
      checkOptimal(lp, a, rowLo, rowHi, cost, lo, hi, run);
      // in a copy, and after the rows changed, the basis is not restored
      assertThat(lp.copy().restoreBasis(saved)).isFalse();
      lp.addRows(new double[][] {new double[n]}, new double[] {-1}, new double[] {1});
      assertThat(lp.restoreBasis(saved)).isFalse();
    }
    assertThat(restored).isGreaterThan(100);
  }

  static void checkOptimal(
      LpSolver lp,
      double[][] a,
      double[] rowLo,
      double[] rowHi,
      double[] cost,
      double[] lo,
      double[] hi,
      int run) {
    checkOptimal(lp, a, rowLo, rowHi, cost, lo, hi, run, 1e-5);
  }

  // as above, with the tolerance of the dual bound against the perturbation of the costs
  static void checkOptimal(
      LpSolver lp,
      double[][] a,
      double[] rowLo,
      double[] rowHi,
      double[] cost,
      double[] lo,
      double[] hi,
      int run,
      double tolerance) {
    int m = a.length;
    int n = cost.length;
    double[] x = new double[n];
    double primal = 0;
    for (int j = 0; j < n; j++) {
      x[j] = lp.value(j);
      assertThat(x[j]).as("run %d", run).isBetween(lo[j] - TOL, hi[j] + TOL);
      primal += cost[j] * x[j];
    }
    for (int i = 0; i < m; i++) {
      double s = 0;
      for (int j = 0; j < n; j++) {
        s += a[i][j] * x[j];
      }
      assertThat(s).as("run %d row %d", run, i).isBetween(rowLo[i] - TOL, rowHi[i] + TOL);
    }
    // the dual bound: c x = (c - yA) x + y A x >= sum_j min (c - yA)_j x_j + sum_i min y_i [L, U]
    double[] y = lp.duals();
    double bound = 0;
    for (int j = 0; j < n; j++) {
      double r = cost[j];
      for (int i = 0; i < m; i++) {
        r -= y[i] * a[i][j];
      }
      bound += Math.min(r * lo[j], r * hi[j]);
    }
    for (int i = 0; i < m; i++) {
      if (Math.abs(y[i]) > 1e-9) {
        double side = y[i] > 0 ? rowLo[i] : rowHi[i];
        assertThat(Double.isInfinite(side))
            .as("run %d dual %d on a missing side", run, i)
            .isFalse();
        bound += y[i] * side;
      }
    }
    assertThat(bound)
        .as("run %d dual bound", run)
        .isCloseTo(primal, org.assertj.core.data.Offset.offset(tolerance));
  }

  // the combination y A x must be kept from the range of y [L, U] by the bounds of x
  static void checkFarkas(
      double[] y, double[][] a, double[] rowLo, double[] rowHi, double[] lo, double[] hi, int run) {
    int m = a.length;
    int n = lo.length;
    double least = 0;
    double most = 0;
    for (int j = 0; j < n; j++) {
      double r = 0;
      for (int i = 0; i < m; i++) {
        r += y[i] * a[i][j];
      }
      least += Math.min(r * lo[j], r * hi[j]);
      most += Math.max(r * lo[j], r * hi[j]);
    }
    // entries below 1e-9 of the largest multiplier are rounding noise of the ray (a multiplier of
    // 1e-12 on a row with an infinite side would otherwise make that side infinite)
    double largest = 0;
    for (double v : y) {
      largest = Math.max(largest, Math.abs(v));
    }
    double noise = Math.max(1e-12, 1e-9 * largest);
    double sideLo = 0;
    double sideHi = 0;
    for (int i = 0; i < m; i++) {
      if (Math.abs(y[i]) > noise) {
        sideLo += y[i] > 0 ? y[i] * rowLo[i] : y[i] * rowHi[i];
        sideHi += y[i] > 0 ? y[i] * rowHi[i] : y[i] * rowLo[i];
      }
    }
    // y A x lies in [least, most] and must lie in [sideLo, sideHi]: they must be disjoint
    assertThat(most < sideLo - 1e-7 || least > sideHi + 1e-7)
        .as("run %d: [%f, %f] meets [%f, %f]", run, least, most, sideLo, sideHi)
        .isTrue();
  }
}
