/*
 * SparseDualSimplexTest.java
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
import static org.jacop.constraints.lp.DualSimplexTest.checkFarkas;
import static org.jacop.constraints.lp.DualSimplexTest.checkOptimal;

import java.util.Arrays;
import java.util.Random;
import org.assertj.core.data.Offset;
import org.junit.jupiter.api.Test;

/**
 * Tests the sparse dual simplex against the dense one on random bounded LPs: the same status, the
 * same optimal objective, and the certificates of {@link DualSimplexTest} for its own duals and
 * Farkas rows, through warm-started re-solves, added rows, removed rows and copies.
 */
class SparseDualSimplexTest {

  private static final Offset<Double> CLOSE = Offset.offset(1e-5);

  // a random LP: rows a with sides, costs, column bounds
  private static final class Lp {
    double[][] a;
    double[] rowLo;
    double[] rowHi;
    double[] cost;
    double[] lo;
    double[] hi;

    Lp(Random rnd, int m, int n, double density, boolean objective) {
      a = new double[m][n];
      rowLo = new double[m];
      rowHi = new double[m];
      for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
          a[i][j] = rnd.nextDouble() < density ? rnd.nextInt(11) - 5 : 0;
        }
        int kind = rnd.nextInt(3);
        int c = rnd.nextInt(21) - 10;
        rowLo[i] = kind == 0 ? Double.NEGATIVE_INFINITY : c;
        rowHi[i] = kind == 1 ? Double.POSITIVE_INFINITY : c + (kind == 2 ? rnd.nextInt(3) : 0);
      }
      cost = new double[n];
      if (objective) {
        for (int j = 0; j < n; j++) {
          cost[j] = rnd.nextInt(5) - 2;
        }
      }
      lo = new double[n];
      hi = new double[n];
      for (int j = 0; j < n; j++) {
        lo[j] = rnd.nextInt(5) - 3;
        hi[j] = lo[j] + rnd.nextInt(5);
      }
    }

    void bounds(LpSolver lp) {
      for (int j = 0; j < lo.length; j++) {
        lp.setBounds(j, lo[j], hi[j]);
      }
    }

    void tighten(Random rnd) {
      int j = rnd.nextInt(lo.length);
      if (rnd.nextBoolean()) {
        lo[j] = Math.min(hi[j], lo[j] + 1 + rnd.nextInt(2));
      } else {
        hi[j] = Math.max(lo[j], hi[j] - 1 - rnd.nextInt(2));
      }
    }
  }

  // solves both, checks they agree and the sparse certificates; returns the status
  private static int compare(Lp p, LpSolver sparse, LpSolver dense, String what) {
    p.bounds(sparse);
    p.bounds(dense);
    int s = sparse.solve(100_000);
    int d = dense.solve(100_000);
    assertThat(s).as(what).isNotEqualTo(LpSolver.LIMIT);
    assertThat(s).as(what + " status").isEqualTo(d);
    if (s == LpSolver.OPTIMAL) {
      // the costs are perturbed by about 1e-7 per column and unit of value
      checkOptimal(sparse, p.a, p.rowLo, p.rowHi, p.cost, p.lo, p.hi, 0, 1e-5 + 1e-5 * p.lo.length);
      assertThat(sparse.objective()).as(what + " objective").isCloseTo(dense.objective(), CLOSE);
    } else {
      checkFarkas(sparse.farkas(), p.a, p.rowLo, p.rowHi, p.lo, p.hi, 0);
    }
    return s;
  }

  @Test
  void smallLpsAgreeWithTheDenseSimplex() {
    Random rnd = new Random(7);
    int optimal = 0;
    int infeasible = 0;
    for (int run = 0; run < 3000; run++) {
      Lp p = new Lp(rnd, 1 + rnd.nextInt(6), 2 + rnd.nextInt(7), 0.67, rnd.nextBoolean());
      LpSolver sparse = new SparseDualSimplex(p.a, p.rowLo, p.rowHi, p.cost);
      LpSolver dense = new DualSimplex(p.a, p.rowLo, p.rowHi, p.cost);
      for (int step = 0; step < 4; step++) {
        if (compare(p, sparse, dense, "run " + run + " step " + step) == LpSolver.OPTIMAL) {
          optimal++;
        } else {
          infeasible++;
          break;
        }
        p.tighten(rnd);
      }
    }
    assertThat(optimal).isGreaterThan(1000);
    assertThat(infeasible).isGreaterThan(300);
  }

  @Test
  void largerSparseLpsAgreeThroughManyPivotsAndRefactorizations() {
    Random rnd = new Random(11);
    long pivots = 0;
    int optimal = 0;
    for (int run = 0; run < 150; run++) {
      int m = 20 + rnd.nextInt(60);
      int n = 20 + rnd.nextInt(80);
      Lp p = new Lp(rnd, m, n, 4.0 / n, true);
      // wide bounds, so that the LP is feasible more often and takes many pivots
      for (int j = 0; j < n; j++) {
        p.lo[j] = -10 - rnd.nextInt(10);
        p.hi[j] = 10 + rnd.nextInt(10);
      }
      SparseDualSimplex sparse = new SparseDualSimplex(p.a, p.rowLo, p.rowHi, p.cost);
      LpSolver dense = new DualSimplex(p.a, p.rowLo, p.rowHi, p.cost);
      for (int step = 0; step < 20; step++) {
        if (compare(p, sparse, dense, "run " + run + " step " + step) != LpSolver.OPTIMAL) {
          break;
        }
        optimal++;
        for (int k = 0; k < 3; k++) {
          p.tighten(rnd);
        }
      }
      pivots += sparse.pivots();
    }
    assertThat(optimal).isGreaterThan(300);
    assertThat(pivots).isGreaterThan(5000);
  }

  @Test
  void addedRowsKeepTheBasis() {
    Random rnd = new Random(5);
    int optimal = 0;
    int infeasible = 0;
    for (int run = 0; run < 2000; run++) {
      int m = 1 + rnd.nextInt(5);
      int extra = 1 + rnd.nextInt(4);
      Lp p = new Lp(rnd, m + extra, 2 + rnd.nextInt(7), 0.67, true);
      LpSolver sparse =
          new SparseDualSimplex(
              Arrays.copyOf(p.a, m), Arrays.copyOf(p.rowLo, m), Arrays.copyOf(p.rowHi, m), p.cost);
      p.bounds(sparse);
      if (sparse.solve(1000) != LpSolver.OPTIMAL) {
        continue;
      }
      sparse.addRows(
          Arrays.copyOfRange(p.a, m, m + extra),
          Arrays.copyOfRange(p.rowLo, m, m + extra),
          Arrays.copyOfRange(p.rowHi, m, m + extra));
      LpSolver dense = new DualSimplex(p.a, p.rowLo, p.rowHi, p.cost);
      if (compare(p, sparse, dense, "run " + run) == LpSolver.OPTIMAL) {
        optimal++;
      } else {
        infeasible++;
      }
    }
    assertThat(optimal).isGreaterThan(200);
    assertThat(infeasible).isGreaterThan(200);
  }

  @Test
  void removedRowsWithBasicSlacksKeepTheBasis() {
    Random rnd = new Random(13);
    int removedRuns = 0;
    for (int run = 0; run < 2000; run++) {
      int m = 2 + rnd.nextInt(10);
      Lp p = new Lp(rnd, m, 2 + rnd.nextInt(10), 0.5, true);
      SparseDualSimplex sparse = new SparseDualSimplex(p.a, p.rowLo, p.rowHi, p.cost);
      p.bounds(sparse);
      if (sparse.solve(1000) != LpSolver.OPTIMAL) {
        continue;
      }
      int[] ask = new int[1 + rnd.nextInt(m)];
      for (int k = 0; k < ask.length; k++) {
        ask[k] = rnd.nextInt(m);
      }
      int[] kept = sparse.removeRows(ask);
      if (kept == null) {
        continue;
      }
      removedRuns++;
      Lp q = new Lp(rnd, 0, p.cost.length, 0, false);
      q.cost = p.cost;
      q.lo = p.lo;
      q.hi = p.hi;
      q.a = new double[kept.length][];
      q.rowLo = new double[kept.length];
      q.rowHi = new double[kept.length];
      for (int i = 0; i < kept.length; i++) {
        q.a[i] = p.a[kept[i]];
        q.rowLo[i] = p.rowLo[kept[i]];
        q.rowHi[i] = p.rowHi[kept[i]];
      }
      assertThat(sparse.rows()).isEqualTo(kept.length);
      // the basis is still optimal for the rows left: no pivot is needed
      long before = sparse.pivots();
      LpSolver dense = new DualSimplex(q.a, q.rowLo, q.rowHi, q.cost);
      assertThat(compare(q, sparse, dense, "run " + run)).isEqualTo(LpSolver.OPTIMAL);
      assertThat(sparse.pivots()).as("run %d", run).isEqualTo(before);
      // and goes on from there
      for (int step = 0; step < 3; step++) {
        q.tighten(rnd);
        if (compare(q, sparse, dense, "run " + run + " step " + step) != LpSolver.OPTIMAL) {
          break;
        }
      }
    }
    assertThat(removedRuns).isGreaterThan(100);
  }

  @Test
  void aCopyGoesOnIndependently() {
    Random rnd = new Random(17);
    for (int run = 0; run < 500; run++) {
      Lp p = new Lp(rnd, 2 + rnd.nextInt(8), 2 + rnd.nextInt(8), 0.6, true);
      LpSolver sparse = new SparseDualSimplex(p.a, p.rowLo, p.rowHi, p.cost);
      p.bounds(sparse);
      if (sparse.solve(1000) != LpSolver.OPTIMAL) {
        continue;
      }
      double before = sparse.objective();
      LpSolver copy = sparse.copy();
      p.tighten(rnd);
      p.tighten(rnd);
      LpSolver dense = new DualSimplex(p.a, p.rowLo, p.rowHi, p.cost);
      compare(p, copy, dense, "run " + run);
      assertThat(sparse.objective()).isCloseTo(before, CLOSE);
    }
  }
}
