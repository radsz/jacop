/*
 * RevisedDualSimplexTest.java
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

import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests {@link RevisedDualSimplex} on random LPs with finite, one-sided and free columns and rows,
 * scaled and not. Every answer is checked by its own certificate: an optimum by primal and dual
 * feasibility and complementary slackness of the values and duals returned, an infeasibility by its
 * Farkas row, and unboundedness by an objective that keeps improving as a box around the problem
 * grows. Warm-started solves after bound changes must agree with fresh ones.
 */
class RevisedDualSimplexTest {

  private static final double INF = Double.POSITIVE_INFINITY;

  // a random LP, by rows
  private static final class Lp {
    int[][] cols;
    double[][] vals;
    double[] rowLo;
    double[] rowHi;
    double[] cost;
    double[] lo;
    double[] hi;

    Lp(Random rnd, int m, int n, double density, int scaleSpread) {
      cols = new int[m][];
      vals = new double[m][];
      rowLo = new double[m];
      rowHi = new double[m];
      // rows and columns of very different magnitudes, which scaling should even out
      double[] rs = new double[m];
      double[] cs = new double[n];
      for (int i = 0; i < m; i++) {
        rs[i] = Math.pow(10, rnd.nextInt(2 * scaleSpread + 1) - (double) scaleSpread);
      }
      for (int j = 0; j < n; j++) {
        cs[j] = Math.pow(10, rnd.nextInt(2 * scaleSpread + 1) - (double) scaleSpread);
      }
      for (int i = 0; i < m; i++) {
        int[] c = new int[n];
        double[] v = new double[n];
        int k = 0;
        for (int j = 0; j < n; j++) {
          if (rnd.nextDouble() < density) {
            int a = rnd.nextInt(11) - 5;
            if (a != 0) {
              c[k] = j;
              v[k++] = a * rs[i] * cs[j];
            }
          }
        }
        cols[i] = java.util.Arrays.copyOf(c, k);
        vals[i] = java.util.Arrays.copyOf(v, k);
        int kind = rnd.nextInt(4);
        double b = (rnd.nextInt(21) - 10) * rs[i];
        rowLo[i] = kind == 0 ? -INF : b;
        rowHi[i] = kind == 1 ? INF : kind == 2 ? b : b + rnd.nextInt(4) * rs[i];
      }
      cost = new double[n];
      lo = new double[n];
      hi = new double[n];
      for (int j = 0; j < n; j++) {
        cost[j] = (rnd.nextInt(7) - 3) / cs[j];
        int kind = rnd.nextInt(5);
        double l = (rnd.nextInt(7) - 3) / cs[j];
        lo[j] = kind == 3 || kind == 4 ? -INF : l;
        hi[j] = kind == 2 || kind == 4 ? INF : (kind == 3 ? l : l + rnd.nextInt(5) / cs[j]);
      }
    }

    RevisedDualSimplex simplex(boolean scale) {
      RevisedDualSimplex lp = new RevisedDualSimplex(cols, vals, rowLo, rowHi, cost, scale);
      lp.setExact(true);
      bounds(lp);
      return lp;
    }

    void bounds(RevisedDualSimplex lp) {
      for (int j = 0; j < lo.length; j++) {
        lp.setBounds(j, lo[j], hi[j]);
      }
    }

    double activity(int i, double[] x) {
      double s = 0;
      for (int e = 0; e < cols[i].length; e++) {
        s += vals[i][e] * x[cols[i][e]];
      }
      return s;
    }

    @Override
    public String toString() {
      StringBuilder b = new StringBuilder();
      for (int i = 0; i < cols.length; i++) {
        b.append("\nrow ")
            .append(java.util.Arrays.toString(cols[i]))
            .append(java.util.Arrays.toString(vals[i]));
        b.append(" in [").append(rowLo[i]).append(", ").append(rowHi[i]).append("]");
      }
      for (int j = 0; j < cost.length; j++) {
        b.append("\ncol ")
            .append(j)
            .append(" cost ")
            .append(cost[j])
            .append(" in [")
            .append(lo[j])
            .append(", ")
            .append(hi[j])
            .append("]");
      }
      return b.toString();
    }

    double norm(int i) {
      double s = 1;
      for (double v : vals[i]) {
        s = Math.max(s, Math.abs(v));
      }
      return s;
    }
  }

  private static boolean within(double v, double lo, double hi, double tol) {
    return v >= lo - tol * Math.max(1, Math.abs(lo)) && v <= hi + tol * Math.max(1, Math.abs(hi));
  }

  // primal and dual feasibility and complementary slackness of the answer
  private static void checkOptimal(Lp p, RevisedDualSimplex lp, String what) {
    int m = p.rowLo.length;
    int n = p.cost.length;
    double[] x = new double[n];
    double z = 0;
    for (int j = 0; j < n; j++) {
      x[j] = lp.value(j);
      assertThat(within(x[j], p.lo[j], p.hi[j], 1e-6)).as("%s column %d bounds", what, j).isTrue();
      z += p.cost[j] * x[j];
    }
    assertThat(lp.objective())
        .as(what + " objective")
        .isCloseTo(z, org.assertj.core.data.Offset.offset(1e-6 * (1 + Math.abs(z))));
    double[] y = lp.duals();
    double[] d = p.cost.clone();
    for (int i = 0; i < m; i++) {
      double s = p.activity(i, x);
      double tol = 1e-6 * p.norm(i) * (1 + maxAbs(x));
      assertThat(s >= p.rowLo[i] - tol && s <= p.rowHi[i] + tol)
          .as("%s row %d: %s", what, i, s)
          .isTrue();
      assertThat(Math.abs(s - lp.value(n + i))).as("%s slack %d", what, i).isLessThanOrEqualTo(tol);
      for (int e = 0; e < p.cols[i].length; e++) {
        d[p.cols[i][e]] -= y[i] * p.vals[i][e];
      }
      // the slack of the row: column -e_i with no cost, reduced cost y_i
      checkReduced(
          y[i], s, p.rowLo[i], p.rowHi[i], tol, 1e-7 * (1 + Math.abs(y[i])), what + " row " + i);
    }
    for (int j = 0; j < n; j++) {
      double tol = 1e-6 * Math.max(1, Math.abs(x[j]));
      double dualTol = 1e-7 * (1 + Math.abs(p.cost[j]) + dualScale(p, y, j));
      checkReduced(d[j], x[j], p.lo[j], p.hi[j], tol, dualTol, what + " column " + j);
    }
  }

  private static double dualScale(Lp p, double[] y, int j) {
    double s = 0;
    for (int i = 0; i < p.cols.length; i++) {
      for (int e = 0; e < p.cols[i].length; e++) {
        if (p.cols[i][e] == j) {
          s += Math.abs(y[i] * p.vals[i][e]);
        }
      }
    }
    return s;
  }

  private static double maxAbs(double[] x) {
    double s = 0;
    for (double v : x) {
      s = Math.max(s, Math.abs(v));
    }
    return s;
  }

  // a column strictly above its lower bound may not have a positive reduced cost, one strictly
  // below its upper bound not a negative one
  private static void checkReduced(
      double d, double v, double lo, double hi, double tol, double dualTol, String what) {
    if (v > lo + tol) {
      assertThat(d).as(what + " above its lower bound").isLessThanOrEqualTo(dualTol);
    }
    if (v < hi - tol) {
      assertThat(d).as(what + " below its upper bound").isGreaterThanOrEqualTo(-dualTol);
    }
  }

  // the Farkas row y: y (A x - s) = 0 for every solution, but over the bounds it cannot be 0
  private static void checkFarkas(Lp p, double[] y, String what) {
    int n = p.cost.length;
    double[] coef = new double[n];
    double min = 0;
    double max = 0;
    double size = 0;
    for (int i = 0; i < y.length; i++) {
      for (int e = 0; e < p.cols[i].length; e++) {
        coef[p.cols[i][e]] += y[i] * p.vals[i][e];
      }
      size += Math.abs(y[i]) * p.norm(i);
    }
    for (int i = 0; i < y.length; i++) {
      // - y_i s_i with s_i in the bounds of the row; the slacks of the other basic rows have
      // multipliers of round-off size
      double a = -y[i];
      if (Math.abs(a) > 1e-9 * (1 + size)) {
        min += a > 0 ? a * p.rowLo[i] : a * p.rowHi[i];
        max += a > 0 ? a * p.rowHi[i] : a * p.rowLo[i];
      }
    }
    for (int j = 0; j < n; j++) {
      double a = coef[j];
      if (Math.abs(a) > 1e-9 * (1 + size)) {
        min += a > 0 ? a * p.lo[j] : a * p.hi[j];
        max += a > 0 ? a * p.hi[j] : a * p.lo[j];
      }
    }
    double tol = 1e-7 * (1 + size);
    assertThat(min > tol || max < -tol).as("%s Farkas row: [%s, %s]", what, min, max).isTrue();
  }

  // the problem in a box of the given size: finite bounds, so it is never unbounded
  private static double boxed(Lp p, double box, boolean scale) {
    Lp q = copy(p);
    for (int j = 0; j < q.lo.length; j++) {
      q.lo[j] = Math.max(q.lo[j], -box);
      q.hi[j] = Math.min(q.hi[j], box);
    }
    RevisedDualSimplex lp = q.simplex(scale);
    int status = lp.solve(1_000_000);
    assertThat(status).isIn(RevisedDualSimplex.OPTIMAL, RevisedDualSimplex.INFEASIBLE);
    if (status == RevisedDualSimplex.OPTIMAL) {
      checkOptimal(q, lp, "boxed");
      return lp.objective();
    }
    return Double.NaN;
  }

  private static Lp copy(Lp p) {
    Lp q = new Lp(new Random(0), 0, 0, 0, 0);
    q.cols = p.cols;
    q.vals = p.vals;
    q.rowLo = p.rowLo;
    q.rowHi = p.rowHi;
    q.cost = p.cost;
    q.lo = p.lo.clone();
    q.hi = p.hi.clone();
    return q;
  }

  // without scaling the tolerances apply to rows with entries from 1e-4 to 1e4, which can move the
  // optimum by more
  private static double objectiveTolerance(boolean scale) {
    return scale ? 1e-6 : 1e-3;
  }

  // solves and checks one answer; returns the status
  private static int solveAndCheck(Lp p, RevisedDualSimplex lp, boolean scale, String what) {
    return solveAndCheck(p, lp, scale, false, what);
  }

  private static int solveAndCheck(
      Lp p, RevisedDualSimplex lp, boolean scale, boolean primal, String what) {
    try {
      return solveAndCheckOnce(p, lp, scale, primal, what);
    } catch (AssertionError e) {
      throw new AssertionError(e.getMessage() + "\nscaled " + scale + p, e);
    }
  }

  private static int solveAndCheckOnce(
      Lp p, RevisedDualSimplex lp, boolean scale, boolean primal, String what) {
    int status = primal ? lp.solvePrimal(1_000_000) : lp.solve(1_000_000);
    switch (status) {
      case RevisedDualSimplex.OPTIMAL -> {
        checkOptimal(p, lp, what);
        double size = 0;
        for (int j = 0; j < p.cost.length; j++) {
          size = Math.max(size, Math.abs(lp.value(j)));
        }
        double b = boxed(p, Math.max(1e5, 100 * size), scale);
        assertThat(b)
            .as(what + " boxed optimum")
            .isCloseTo(
                lp.objective(),
                org.assertj.core.data.Offset.offset(objectiveTolerance(scale) * (1 + Math.abs(b))));
      }
      case RevisedDualSimplex.INFEASIBLE -> checkFarkas(p, lp.farkas(), what);
      case RevisedDualSimplex.UNBOUNDED -> {
        double small = boxed(p, 1e3, scale);
        double large = boxed(p, 1e5, scale);
        assertThat(large)
            .as(what + " unbounded: the objective improves with the box")
            .isLessThan(small - 1e-3);
      }
      default -> throw new AssertionError(what + " stopped at the limit");
    }
    return status;
  }

  @Test
  void givenDualsHaveNoPerturbation() {
    // min z with z - x - y >= 0, x + y >= 3, x - y <= 1, all in [0, 10]: duals 1, 1, 0
    double inf = Double.POSITIVE_INFINITY;
    RevisedDualSimplex lp =
        new RevisedDualSimplex(
            new int[][] {{0, 1, 2}, {1, 2}, {1, 2}},
            new double[][] {{1, -1, -1}, {1, 1}, {1, -1}},
            new double[] {0, 3, -inf},
            new double[] {inf, inf, 1},
            new double[] {1, 0, 0},
            true);
    for (int j = 0; j < 3; j++) {
      lp.setBounds(j, 0, 10);
    }
    assertThat(lp.solve(100)).isEqualTo(RevisedDualSimplex.OPTIMAL);
    // + 0.0 turns -0.0 into 0.0
    assertThat(java.util.Arrays.stream(lp.givenDuals()).map(v -> v + 0.0).toArray())
        .containsExactly(1, 1, 0);
    assertThat(lp.duals()[0]).isNotEqualTo(1.0);
  }

  @Test
  void randomLpsAreAnsweredWithCertificates() {
    Random rnd = new Random(3);
    int[] counts = new int[4];
    int runs = Integer.getInteger("jalp.test.runs", 3000);
    for (int run = 0; run < runs; run++) {
      boolean scale = rnd.nextBoolean();
      Lp p = new Lp(rnd, 1 + rnd.nextInt(8), 1 + rnd.nextInt(9), 0.6, rnd.nextInt(3));
      RevisedDualSimplex lp = p.simplex(scale);
      counts[solveAndCheck(p, lp, scale, "run " + run)]++;
    }
    String found = java.util.Arrays.toString(counts);
    assertThat(counts[RevisedDualSimplex.OPTIMAL]).as(found).isGreaterThan(runs / 10);
    assertThat(counts[RevisedDualSimplex.INFEASIBLE]).as(found).isGreaterThan(runs / 10);
    assertThat(counts[RevisedDualSimplex.UNBOUNDED]).as(found).isGreaterThan(runs / 20);
  }

  @Test
  void crashBasesAgreeWithTheSlackBasis() {
    Random rnd = new Random(11);
    int runs = Integer.getInteger("jalp.test.runs", 3000) / 3;
    int crashed = 0;
    for (int run = 0; run < runs; run++) {
      boolean scale = rnd.nextBoolean();
      int m = 1 + rnd.nextInt(12);
      int n = 1 + rnd.nextInt(14);
      Lp p = new Lp(rnd, m, n, 0.4, rnd.nextInt(3));
      RevisedDualSimplex slack = p.simplex(scale);
      slack.setPresolve(false);
      slack.setCrash(-1);
      int status = solveAndCheck(p, slack, scale, "run " + run + " slack basis");
      assertThat(slack.crashed()).isZero();
      for (int rows = 0; rows <= 2; rows++) {
        String what = "run " + run + " crash " + rows;
        RevisedDualSimplex lp = p.simplex(scale);
        lp.setPresolve(false);
        lp.setCrash(rows);
        assertThat(solveAndCheck(p, lp, scale, what)).as(what).isEqualTo(status);
        crashed += lp.crashed() > 0 ? 1 : 0;
        if (status == RevisedDualSimplex.OPTIMAL) {
          assertThat(lp.objective())
              .as(what)
              .isCloseTo(
                  slack.objective(),
                  org.assertj.core.data.Offset.offset(
                      objectiveTolerance(scale) * (1 + Math.abs(slack.objective()))));
        }
      }
    }
    assertThat(crashed).isGreaterThan(runs);
  }

  @Test
  void presolvedSolvesAgreeWithPlainOnes() {
    Random rnd = new Random(23);
    // the chunks of the chunked solves, apart so that they leave the problems as they were
    Random chunks = new Random(29);
    int runs = Integer.getInteger("jalp.test.runs", 3000) / 3;
    int reduced = 0;
    int optimal = 0;
    for (int run = 0; run < runs; run++) {
      boolean scale = rnd.nextBoolean();
      int m = 1 + rnd.nextInt(14);
      int n = 1 + rnd.nextInt(16);
      // sparse rows, so that singleton and doubleton rows, free column singletons and empty
      // columns are common
      Lp p = new Lp(rnd, m, n, 0.1 + 0.3 * rnd.nextDouble(), rnd.nextInt(3));
      if (rnd.nextBoolean()) {
        for (int j = 0; j < n; j++) {
          if (rnd.nextInt(6) == 0) {
            p.hi[j] = p.lo[j] == Double.NEGATIVE_INFINITY ? 0 : p.lo[j];
            p.lo[j] = p.hi[j];
          } else if (rnd.nextInt(4) == 0) {
            p.cost[j] = 0;
          }
        }
      }
      if (rnd.nextInt(4) > 0) {
        feasibleAround(p);
      }
      RevisedDualSimplex plain = p.simplex(scale);
      plain.setPresolve(false);
      int status = solveAndCheck(p, plain, scale, "run " + run + " without presolve");
      assertThat(plain.presolvedRows()).isEqualTo(-1);
      String what = "run " + run + " presolved";
      RevisedDualSimplex lp = p.simplex(scale);
      lp.setPresolve(true);
      assertThat(solveAndCheck(p, lp, scale, what)).as(what).isEqualTo(status);
      // a solve in short chunks, as the root solve of LinearRelaxation makes, goes on with the
      // reduced problem; a query in between takes the basis postsolved from it
      RevisedDualSimplex chunked = p.simplex(scale);
      chunked.setPresolve(true);
      for (int k = 0;
          k < 100_000 && chunked.solve(1 + chunks.nextInt(3)) == RevisedDualSimplex.LIMIT;
          k++) {
        if (chunks.nextInt(8) == 0) {
          chunked.objective();
        }
      }
      String inChunks = what + " in chunks";
      assertThat(solveAndCheck(p, chunked, scale, inChunks)).as(inChunks).isEqualTo(status);
      if (status == RevisedDualSimplex.OPTIMAL) {
        optimal++;
        if (lp.presolvedRows() >= 0) {
          reduced++;
        }
        assertThat(lp.objective())
            .as(what)
            .isCloseTo(
                plain.objective(),
                org.assertj.core.data.Offset.offset(
                    objectiveTolerance(scale) * (1 + Math.abs(plain.objective()))));
        // warm starts after the presolved first solve hold their certificates too
        for (int j = 0; j < n; j++) {
          if (rnd.nextInt(3) == 0 && p.hi[j] != INF && p.lo[j] != p.hi[j]) {
            Lp q = copy(p);
            q.hi[j] = q.lo[j] == Double.NEGATIVE_INFINITY ? q.hi[j] - 1 : q.lo[j];
            q.bounds(lp);
            solveAndCheck(q, lp, scale, what + " then column " + j + " tightened");
            break;
          }
        }
      }
    }
    assertThat(reduced).isGreaterThan(optimal / 2);
  }

  // moves the bounds of the rows so that a point within the column bounds satisfies them all
  private static void feasibleAround(Lp p) {
    int n = p.cost.length;
    double[] x = new double[n];
    for (int j = 0; j < n; j++) {
      x[j] = p.lo[j] != Double.NEGATIVE_INFINITY ? p.lo[j] : p.hi[j] != INF ? p.hi[j] : 0;
      if (p.hi[j] != INF && p.lo[j] != Double.NEGATIVE_INFINITY) {
        x[j] = (p.lo[j] + p.hi[j]) / 2;
      }
    }
    for (int i = 0; i < p.rowLo.length; i++) {
      double s = p.activity(i, x);
      double width = p.rowHi[i] - p.rowLo[i];
      if (p.rowLo[i] == p.rowHi[i]) {
        p.rowLo[i] = s;
        p.rowHi[i] = s;
      } else if (p.rowLo[i] == Double.NEGATIVE_INFINITY) {
        p.rowHi[i] = Math.max(p.rowHi[i], s);
      } else if (p.rowHi[i] == INF) {
        p.rowLo[i] = Math.min(p.rowLo[i], s);
      } else {
        p.rowLo[i] = s - width / 2;
        p.rowHi[i] = s + width / 2;
      }
    }
  }

  @Test
  void aPresolvedSolveEndsWithFewPivotsAfterTheReducedOne() {
    // x0 = 2 x1 (doubleton), x2 only in row 1 (free column singleton), 1 <= x3 <= 3 (singleton
    // row), x4 fixed, x5 with no row (empty column): min x0 + x1 - x2 + x3 + x5
    int[][] cols = {{0, 1}, {2, 0, 3}, {3}, {4, 1}};
    double[][] vals = {{1, -2}, {1, 1, 1}, {1}, {1, 1}};
    double[] rowLo = {0, 4, 1, 1};
    double[] rowHi = {0, 4, 3, 10};
    double[] cost = {1, 1, -1, 1, 0, 1};
    RevisedDualSimplex lp = new RevisedDualSimplex(cols, vals, rowLo, rowHi, cost, true);
    lp.setExact(true);
    lp.setPresolve(true);
    lp.setBounds(0, 0, 10);
    lp.setBounds(1, 0, 10);
    lp.setBounds(2, -INF, INF);
    lp.setBounds(3, 0, 10);
    lp.setBounds(4, 2, 2);
    lp.setBounds(5, 0, 5);
    assertThat(lp.solve(1000)).isEqualTo(RevisedDualSimplex.OPTIMAL);
    assertThat(lp.presolvedRows()).isLessThan(4);
    // x2 = 4 - x0 - x3, so the objective is 2 x0 + x1 + 2 x3 - 4 = 5 x1 + 2 x3 - 4: x1 = 0, x3 = 1
    assertThat(lp.objective()).isCloseTo(-2, org.assertj.core.data.Offset.offset(1e-9));
    assertThat(lp.value(3)).isCloseTo(1, org.assertj.core.data.Offset.offset(1e-9));
    assertThat(lp.value(4)).isCloseTo(2, org.assertj.core.data.Offset.offset(1e-9));
    assertThat(lp.value(5)).isCloseTo(0, org.assertj.core.data.Offset.offset(1e-9));
  }

  @Test
  void theRefactorizationRulesAgree() {
    Random rnd = new Random(11);
    int runs = Math.max(3, Integer.getInteger("jalp.test.runs", 3000) / 300);
    long forWork = 0;
    for (int run = 0; run < runs; run++) {
      int m = 120 + rnd.nextInt(80);
      int n = 150 + rnd.nextInt(150);
      Lp p = new Lp(rnd, m, n, 5.0 / n, 1);
      for (int j = 0; j < n; j++) {
        p.lo[j] = -5.0 - rnd.nextInt(5);
        p.hi[j] = 5.0 + rnd.nextInt(5);
      }
      // the fixed limit, the default weight, and a factorization so cheap it is rebuilt often
      int status = -1;
      double objective = 0;
      for (double weight : new double[] {0, 1, 0.01}) {
        String what = "run " + run + " weight " + weight;
        RevisedDualSimplex lp = p.simplex(true);
        lp.setRefactorWeight(weight);
        int s = solveAndCheck(p, lp, true, what);
        if (weight <= 0) {
          status = s;
          objective = s == RevisedDualSimplex.OPTIMAL ? lp.objective() : 0;
          assertThat(lp.refactorsForWork()).as(what).isZero();
          continue;
        }
        assertThat(s).as(what).isEqualTo(status);
        if (s == RevisedDualSimplex.OPTIMAL) {
          assertThat(lp.objective())
              .as(what)
              .isCloseTo(
                  objective, org.assertj.core.data.Offset.offset(1e-6 * (1 + Math.abs(objective))));
        }
        if (weight < 1) {
          forWork += lp.refactorsForWork();
        }
      }
    }
    // the cheap factorization makes the rule fire
    assertThat(forWork).isPositive();
  }

  @Test
  void thePrimalSimplexAnswersRandomLpsWithCertificates() {
    Random rnd = new Random(7);
    int[] counts = new int[4];
    int runs = Integer.getInteger("jalp.test.runs", 3000);
    for (int run = 0; run < runs; run++) {
      boolean scale = rnd.nextBoolean();
      Lp p = new Lp(rnd, 1 + rnd.nextInt(8), 1 + rnd.nextInt(9), 0.6, rnd.nextInt(3));
      RevisedDualSimplex lp = p.simplex(scale);
      int status = solveAndCheck(p, lp, scale, true, "primal run " + run);
      counts[status]++;
      assertThat(p.simplex(scale).solve(1_000_000))
          .as("primal run %d, dual", run)
          .isEqualTo(status);
    }
    String found = java.util.Arrays.toString(counts);
    assertThat(counts[RevisedDualSimplex.OPTIMAL]).as(found).isGreaterThan(runs / 10);
    assertThat(counts[RevisedDualSimplex.INFEASIBLE]).as(found).isGreaterThan(runs / 10);
    assertThat(counts[RevisedDualSimplex.UNBOUNDED]).as(found).isGreaterThan(runs / 20);
  }

  @Test
  void objectiveChangesAreSolvedByThePrimalSimplexFromTheBasisKept() {
    Random rnd = new Random(11);
    int runs = Integer.getInteger("jalp.test.runs", 3000) / 10;
    long warm = 0;
    long fresh = 0;
    long warmDual = 0;
    int solved = 0;
    for (int run = 0; run < runs; run++) {
      int m = 10 + rnd.nextInt(40);
      int n = 10 + rnd.nextInt(60);
      Lp p = new Lp(rnd, m, n, 4.0 / n, 1);
      for (int j = 0; j < n; j++) {
        p.lo[j] = -5.0 - rnd.nextInt(5);
        p.hi[j] = 5.0 + rnd.nextInt(5);
      }
      RevisedDualSimplex lp = p.simplex(true);
      if (lp.solve(1_000_000) != RevisedDualSimplex.OPTIMAL) {
        continue;
      }
      for (int step = 0; step < 5; step++) {
        String what = "run " + run + " step " + step;
        // a new objective: some costs change, some change sign
        double[] c = p.cost.clone();
        for (int j = 0; j < n; j++) {
          if (rnd.nextInt(3) == 0) {
            c[j] = rnd.nextInt(7) - 3.0;
          }
        }
        p.cost = c;
        RevisedDualSimplex dual = lp.copy();
        lp.setCost(c);
        dual.setCost(c);
        long before = lp.pivots();
        long dualBefore = dual.pivots();
        assertThat(dual.solve(1_000_000)).as(what + " dual").isEqualTo(RevisedDualSimplex.OPTIMAL);
        warmDual += dual.pivots() - dualBefore;
        int status = solveAndCheck(p, lp, true, true, what);
        assertThat(status).as(what).isEqualTo(RevisedDualSimplex.OPTIMAL);
        RevisedDualSimplex again = p.simplex(true);
        assertThat(again.solve(1_000_000)).as(what + " fresh").isEqualTo(status);
        assertThat(again.objective())
            .as(what)
            .isCloseTo(
                lp.objective(),
                org.assertj.core.data.Offset.offset(1e-6 * (1 + Math.abs(lp.objective()))));
        warm += lp.pivots() - before;
        fresh += again.pivots();
        solved++;
        // and a bound change on top, solved by the dual simplex
        int j = rnd.nextInt(n);
        p.hi[j] = Math.max(p.lo[j], Math.floor(lp.value(j) - 0.5));
        p.bounds(lp);
        if (solveAndCheck(p, lp, true, what + " bound") != RevisedDualSimplex.OPTIMAL) {
          break;
        }
      }
    }
    assertThat(solved).isGreaterThan(runs / 2);
    // the basis pivots after a new objective: far fewer than a fresh solve, about as many as the
    // dual simplex makes from the same basis (660 and 595 of 2933, with the flips not counted)
    String found = "primal " + warm + " dual " + warmDual + " fresh " + fresh;
    assertThat(warm * 2).as(found).isLessThan(fresh);
    assertThat(warm).as(found).isLessThan(2 * warmDual);
  }

  @Test
  void warmStartsAgreeWithFreshSolves() {
    Random rnd = new Random(5);
    int runs = Integer.getInteger("jalp.test.runs", 3000) / 10;
    long warm = 0;
    long fresh = 0;
    for (int run = 0; run < runs; run++) {
      int m = 10 + rnd.nextInt(40);
      int n = 10 + rnd.nextInt(60);
      Lp p = new Lp(rnd, m, n, 4.0 / n, 1);
      for (int j = 0; j < n; j++) {
        // boxed columns, so that most problems are feasible and bounded
        p.lo[j] = -5.0 - rnd.nextInt(5);
        p.hi[j] = 5.0 + rnd.nextInt(5);
      }
      RevisedDualSimplex lp = p.simplex(true);
      for (int step = 0; step < 10; step++) {
        String what = "run " + run + " step " + step;
        long before = lp.pivots();
        int status = solveAndCheck(p, lp, true, what);
        RevisedDualSimplex again = p.simplex(true);
        assertThat(again.solve(1_000_000)).as(what + " fresh").isEqualTo(status);
        if (step > 0) {
          warm += lp.pivots() - before;
          fresh += again.pivots();
        }
        if (status != RevisedDualSimplex.OPTIMAL) {
          break;
        }
        assertThat(again.objective())
            .as(what)
            .isCloseTo(
                lp.objective(),
                org.assertj.core.data.Offset.offset(1e-6 * (1 + Math.abs(lp.objective()))));
        int j = rnd.nextInt(n);
        double mid = lp.value(j);
        if (rnd.nextBoolean()) {
          p.lo[j] = Math.min(p.hi[j], Math.ceil(mid + 0.5));
        } else {
          p.hi[j] = Math.max(p.lo[j], Math.floor(mid - 0.5));
        }
        p.bounds(lp);
      }
    }
    // a warm start after one bound change needs far fewer pivots than a fresh solve
    assertThat(warm * 3).isLessThan(fresh);
  }

  // the search changes a few bounds between solves, tightens and loosens them, and often changes
  // none; the simplex only places and moves the columns whose bounds changed, and every answer must
  // still hold by its certificate
  @Test
  void solvesAfterFewBoundChangesHoldTheirCertificates() {
    Random rnd = new Random(11);
    int runs = Integer.getInteger("jalp.test.runs", 3000) / 20;
    int[] counts = new int[4];
    for (int run = 0; run < runs; run++) {
      int n = 5 + rnd.nextInt(30);
      Lp p = new Lp(rnd, 3 + rnd.nextInt(20), n, 4.0 / n, 1);
      double[] wideLo = new double[n];
      double[] wideHi = new double[n];
      for (int j = 0; j < n; j++) {
        wideLo[j] = p.lo[j] = -4.0 - rnd.nextInt(4);
        wideHi[j] = p.hi[j] = 4.0 + rnd.nextInt(4);
      }
      RevisedDualSimplex lp = p.simplex(true);
      for (int step = 0; step < 30; step++) {
        counts[solveAndCheck(p, lp, true, "run " + run + " step " + step)]++;
        for (int k = rnd.nextInt(4); k > 0; k--) {
          int j = rnd.nextInt(n);
          switch (rnd.nextInt(3)) {
            case 0 -> p.lo[j] = Math.min(p.hi[j], p.lo[j] + 1);
            case 1 -> p.hi[j] = Math.max(p.lo[j], p.hi[j] - 1);
            default -> {
              // a backtrack: the bounds go back
              p.lo[j] = wideLo[j];
              p.hi[j] = wideHi[j];
            }
          }
          lp.setBounds(j, p.lo[j], p.hi[j]);
        }
      }
    }
    String found = java.util.Arrays.toString(counts);
    assertThat(counts[RevisedDualSimplex.OPTIMAL]).as(found).isGreaterThan(runs);
    assertThat(counts[RevisedDualSimplex.INFEASIBLE]).as(found).isGreaterThan(runs);
  }

  @Test
  void aCopyAndRemovedRowsGoOnIndependently() {
    Random rnd = new Random(9);
    int removed = 0;
    for (int run = 0; run < 500; run++) {
      Lp p = new Lp(rnd, 2 + rnd.nextInt(8), 2 + rnd.nextInt(8), 0.6, 1);
      for (int j = 0; j < p.lo.length; j++) {
        p.lo[j] = -3;
        p.hi[j] = 3;
      }
      RevisedDualSimplex lp = p.simplex(true);
      if (lp.solve(1000) != RevisedDualSimplex.OPTIMAL) {
        continue;
      }
      double before = lp.objective();
      RevisedDualSimplex copy = lp.copy();
      int[] kept = copy.removeRows(new int[] {rnd.nextInt(p.rowLo.length)});
      assertThat(lp.solve(1000)).isEqualTo(RevisedDualSimplex.OPTIMAL);
      assertThat(lp.objective()).isCloseTo(before, org.assertj.core.data.Offset.offset(1e-9));
      if (kept == null) {
        continue;
      }
      removed++;
      Lp q = copy(p);
      q.cols = new int[kept.length][];
      q.vals = new double[kept.length][];
      q.rowLo = new double[kept.length];
      q.rowHi = new double[kept.length];
      for (int i = 0; i < kept.length; i++) {
        q.cols[i] = p.cols[kept[i]];
        q.vals[i] = p.vals[kept[i]];
        q.rowLo[i] = p.rowLo[kept[i]];
        q.rowHi[i] = p.rowHi[kept[i]];
      }
      assertThat(solveAndCheck(q, copy, true, "run " + run)).isEqualTo(RevisedDualSimplex.OPTIMAL);
      assertThat(copy.objective())
          .isCloseTo(before, org.assertj.core.data.Offset.offset(1e-6 * (1 + Math.abs(before))));
    }
    assertThat(removed).isGreaterThan(50);
  }

  @Test
  void aRestoredBasisSolvesTheBoundsItWasSavedForAgain() {
    Random rnd = new Random(11);
    int restored = 0;
    int withRows = 0;
    for (int run = 0; run < 400; run++) {
      int m = 10 + rnd.nextInt(30);
      int n = 10 + rnd.nextInt(40);
      Lp p = new Lp(rnd, m, n, 4.0 / n, 1);
      for (int j = 0; j < n; j++) {
        p.lo[j] = -5.0 - rnd.nextInt(5);
        p.hi[j] = 5.0 + rnd.nextInt(5);
      }
      RevisedDualSimplex lp = p.simplex(true);
      // the perturbed costs throughout, as in search, so that the saved basis is optimal for them
      lp.setExact(false);
      if (lp.solve(1_000_000) != RevisedDualSimplex.OPTIMAL) {
        continue;
      }
      double root = lp.objective();
      RevisedDualSimplex exact = p.simplex(true);
      assertThat(solveAndCheck(p, exact, true, "run " + run)).isEqualTo(RevisedDualSimplex.OPTIMAL);
      assertThat(root)
          .isCloseTo(
              exact.objective(),
              org.assertj.core.data.Offset.offset(1e-4 * (1 + Math.abs(exact.objective()))));
      RevisedDualSimplex.Basis saved = lp.saveBasis();
      assertThat(saved.rows()).isEqualTo(m);
      double[] lo = p.lo.clone();
      double[] hi = p.hi.clone();
      // a dive: bounds halved around the solution, until infeasible or ten steps
      for (int step = 0; step < 10; step++) {
        for (int k = 0; k < 3; k++) {
          int j = rnd.nextInt(n);
          double v = Math.rint(lp.value(j));
          p.lo[j] = Math.max(p.lo[j], v - 1);
          p.hi[j] = Math.min(p.hi[j], v + 1);
        }
        p.bounds(lp);
        if (lp.solve(1_000_000) != RevisedDualSimplex.OPTIMAL) {
          break;
        }
      }
      // a row added in the dive: its slack is basic in the restored basis
      Lp q = p;
      if (rnd.nextBoolean()) {
        int j = rnd.nextInt(n);
        q = copy(p);
        q.cols = java.util.Arrays.copyOf(p.cols, m + 1);
        q.vals = java.util.Arrays.copyOf(p.vals, m + 1);
        q.rowLo = java.util.Arrays.copyOf(p.rowLo, m + 1);
        q.rowHi = java.util.Arrays.copyOf(p.rowHi, m + 1);
        q.cols[m] = new int[] {j};
        q.vals[m] = new double[] {1};
        q.rowLo[m] = -INF;
        q.rowHi[m] = INF;
        lp.addRows(
            new int[][] {{j}}, new double[][] {{1}}, new double[] {-INF}, new double[] {INF});
        withRows++;
      }
      // back at the bounds of the root: the restored basis is optimal again
      q.lo = lo;
      q.hi = hi;
      q.bounds(lp);
      assertThat(lp.restoreBasis(saved)).isTrue();
      restored++;
      long before = lp.pivots();
      assertThat(lp.solve(1_000_000)).isEqualTo(RevisedDualSimplex.OPTIMAL);
      assertThat(lp.pivots() - before).as("run " + run).isZero();
      assertThat(lp.objective())
          .isCloseTo(root, org.assertj.core.data.Offset.offset(1e-9 * (1 + Math.abs(root))));
      // after a removal of rows, and in another simplex, the basis is not restored
      assertThat(lp.copy().restoreBasis(saved)).isFalse();
      if (lp.removeRows(new int[] {rnd.nextInt(m)}) != null) {
        assertThat(lp.restoreBasis(saved)).isFalse();
      }
    }
    assertThat(restored).isGreaterThan(60);
    assertThat(withRows).isGreaterThan(20);
  }
}
