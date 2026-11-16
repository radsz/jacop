/*
 * CoverCutsTest.java
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
 * Tests the lifted cover cuts: every lifted cover inequality of random knapsacks, with any minimal
 * cover and both lifting functions, holds on all their 0/1 points; every cut of random rows over
 * 0/1 and general integer columns with weights of both signs holds on all their integer points and
 * is violated by the LP point it was separated from; a textbook knapsack gets its lifted weights;
 * and random multi-knapsack models solved with the relaxation and its cover cuts keep their
 * optimum.
 */
class CoverCutsTest {

  private static final int TRIALS = Integer.getInteger("cover.trials", 3000);

  /** 5 y1 + 5 y2 + 5 y3 + 11 y4 <= 14: cover {1,2,3}, y4 lifted to 2 (11 > mu_2 - lambda = 9). */
  @Test
  void textbookKnapsackLiftsHeavyItem() {
    long[] a = {5, 5, 5, 11};
    boolean[] cover = {true, true, true, false};
    long[] coef = CoverCuts.lifted(4, a, cover, 14);
    assertThat(coef).containsExactly(1, 1, 1, 2);
  }

  /** At the fractional point the cover cut is found and is violated. */
  @Test
  void separatesViolatedCover() {
    int[] columns = {0, 1, 2, 3};
    long[] c = {5, 5, 5, 11};
    double[] value = {1, 1, 0.8, 0};
    long[] lo = {0, 0, 0, 0};
    long[] hi = {1, 1, 1, 1};
    MirCut cut = CoverCuts.separate(columns, c, 14, value, lo, hi);
    assertThat(cut).isNotNull();
    assertThat(cut.rhs).isEqualTo(2);
    assertThat(cut.weights).containsExactly(1, 1, 1, 2);
    assertThat(cut.efficacy).isPositive();
  }

  /** The lifted inequality of any minimal cover holds on every 0/1 point of the knapsack. */
  @Test
  void liftedCoversAreValid() {
    Random random = new Random(1);
    int checked = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      int m = 2 + random.nextInt(9);
      long[] a = new long[m];
      long total = 0;
      for (int k = 0; k < m; k++) {
        a[k] = 1 + random.nextInt(random.nextBoolean() ? 10 : 60);
        total += a[k];
      }
      long side = random.nextInt((int) total);
      boolean[] cover = randomMinimalCover(random, a, side);
      if (cover == null) {
        continue;
      }
      boolean scaled = trial % 2 == 1;
      long[] coef = CoverCuts.lifted(m, a, cover, side, scaled);
      long scale = coef[m];
      long[] integral = CoverCuts.lifted(m, a, cover, side);
      for (int k = 0; k < m; k++) {
        // the scaled function is at least its integral rounding down
        assertThat(coef[k]).isGreaterThanOrEqualTo(integral[k] * scale);
      }
      int r = 0;
      for (int k = 0; k < m; k++) {
        if (cover[k]) {
          r++;
          assertThat(coef[k]).isEqualTo(scale);
        }
      }
      for (int mask = 0; mask < 1 << m; mask++) {
        long w = 0;
        long lhs = 0;
        for (int k = 0; k < m; k++) {
          if ((mask >> k & 1) == 1) {
            w += a[k];
            lhs += coef[k];
          }
        }
        if (w <= side) {
          assertThat(lhs)
              .as(
                  "a %s side %d cover %s coef %s point %s",
                  java.util.Arrays.toString(a),
                  side,
                  java.util.Arrays.toString(cover),
                  java.util.Arrays.toString(coef),
                  Integer.toBinaryString(mask))
              .isLessThanOrEqualTo((r - 1L) * scale);
        }
      }
      checked++;
    }
    assertThat(checked).isGreaterThan(TRIALS / 2);
  }

  /** Cuts of random rows hold on every integer point within the bounds. */
  @Test
  void cutsOfMixedRowsAreValid() {
    Random random = new Random(2);
    int found = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      int n = 2 + random.nextInt(6);
      int[] columns = new int[n];
      long[] c = new long[n];
      long[] lo = new long[n];
      long[] hi = new long[n];
      double[] value = new double[n];
      for (int k = 0; k < n; k++) {
        columns[k] = k;
        c[k] = (random.nextInt(4) == 0 ? -1 : 1) * (1 + random.nextInt(20));
        int kind = random.nextInt(6);
        if (kind == 0) {
          lo[k] = hi[k] = random.nextInt(3) - 1;
        } else if (kind == 1) {
          lo[k] = random.nextInt(3) - 1;
          hi[k] = lo[k] + 1 + random.nextInt(2);
        } else {
          hi[k] = 1;
        }
        value[k] = lo[k] + random.nextDouble() * (hi[k] - lo[k]);
      }
      long b = random.nextInt(60) - 5;
      MirCut cut = CoverCuts.separate(columns, c, b, value, lo, hi);
      if (cut == null) {
        continue;
      }
      found++;
      double act = 0;
      for (int q = 0; q < cut.columns.length; q++) {
        act += cut.weights[q] * value[cut.columns[q]];
      }
      assertThat(act).isGreaterThan(cut.rhs);
      long[] point = lo.clone();
      while (true) {
        long row = 0;
        for (int k = 0; k < n; k++) {
          row += c[k] * point[k];
        }
        if (row <= b) {
          long lhs = 0;
          for (int q = 0; q < cut.columns.length; q++) {
            lhs += cut.weights[q] * point[cut.columns[q]];
          }
          assertThat(lhs).isLessThanOrEqualTo(cut.rhs);
        }
        int k = 0;
        while (k < n && point[k] == hi[k]) {
          point[k] = lo[k];
          k++;
        }
        if (k == n) {
          break;
        }
        point[k]++;
      }
    }
    assertThat(found).isGreaterThan(TRIALS / 20);
  }

  /**
   * Random multi-knapsacks (maximum profit as min cost = -profit), with a complemented item and an
   * integer column in some rows: the relaxation with cover cuts keeps the optimum found without it,
   * its bounds stay below the optimum, and cover cuts are added.
   */
  @Test
  void multiKnapsacksKeepTheirOptimum() {
    Random rnd = new Random(11);
    long covers = 0;
    boolean was = LinearRelaxation.coverOn;
    LinearRelaxation.coverOn = true;
    try {
      for (int run = 0; run < 60; run++) {
        int n = 6 + rnd.nextInt(7);
        int rows = 1 + rnd.nextInt(3);
        int[][] w = new int[rows][n + 1];
        int[] cap = new int[rows];
        for (int i = 0; i < rows; i++) {
          int sum = 0;
          for (int k = 0; k < n; k++) {
            w[i][k] = (rnd.nextInt(8) == 0 ? -1 : 1) * (3 + rnd.nextInt(30));
            sum += Math.max(0, w[i][k]);
          }
          w[i][n] = rnd.nextInt(3) == 0 ? 1 + rnd.nextInt(4) : 0;
          cap[i] = sum / 2 + rnd.nextInt(5);
        }
        int[] p = new int[n];
        for (int k = 0; k < n; k++) {
          p[k] = 1 + rnd.nextInt(20);
        }
        long expected = new Knapsacks(n, w, cap, p).optimum();
        Knapsacks m = new Knapsacks(n, w, cap, p);
        LinearRelaxation r = LinearRelaxation.of(m.store, m.cost, false);
        assertThat(r).as("run %d", run).isNotNull();
        m.store.impose(r);
        long got = m.optimum();
        assertThat(got).as("run %d", run).isEqualTo(expected);
        assertThat(r.rootBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
        if (!Double.isNaN(r.cutBound)) {
          assertThat(r.cutBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
        }
        covers += r.coverCuts;
      }
    } finally {
      LinearRelaxation.coverOn = was;
    }
    assertThat(covers).isPositive();
  }

  // sum p x maximised as min cost = -sum p x, rows sum w x + w_n z <= cap with z in 0..2
  private static final class Knapsacks {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    Knapsacks(int n, int[][] w, int[] cap, int[] p) {
      x = new IntVar[n + 1];
      int total = 0;
      for (int k = 0; k < n; k++) {
        x[k] = new IntVar(store, "x" + k, 0, 1);
        total += p[k];
      }
      x[n] = new IntVar(store, "z", 0, 2);
      cost = new IntVar(store, "cost", -total, 0);
      for (int i = 0; i < w.length; i++) {
        store.impose(new LinearInt(x, w[i], "<=", cap[i]));
      }
      IntVar[] vars = new IntVar[n + 1];
      int[] ws = new int[n + 1];
      for (int k = 0; k < n; k++) {
        vars[k] = x[k];
        ws[k] = p[k];
      }
      vars[n] = cost;
      ws[n] = 1;
      store.impose(new LinearInt(vars, ws, "==", 0));
    }

    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(store, new InputOrderSelect<>(store, x, new IndomainMin<>()), cost);
      return found ? search.getCostValue() : Long.MIN_VALUE;
    }
  }

  // a cover grown in random order and made minimal in random order, or null when none exists
  private static boolean[] randomMinimalCover(Random random, long[] a, long side) {
    int m = a.length;
    boolean[] in = new boolean[m];
    long sum = 0;
    int[] order = random.ints(0, Integer.MAX_VALUE).limit(m).toArray();
    Integer[] idx = new Integer[m];
    for (int k = 0; k < m; k++) {
      idx[k] = k;
    }
    java.util.Arrays.sort(idx, (p, q) -> Integer.compare(order[p], order[q]));
    for (int k : idx) {
      if (sum > side) {
        break;
      }
      in[k] = true;
      sum += a[k];
    }
    if (sum <= side) {
      return null;
    }
    for (int k : idx) {
      if (in[k] && sum - a[k] > side) {
        in[k] = false;
        sum -= a[k];
      }
    }
    return in;
  }
}
