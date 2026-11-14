/*
 * BasisLuTest.java
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
 * Tests the hypersparse solves of {@link BasisLu}: on sparse random bases, through Forrest-Tomlin
 * updates, a solve from a listed right-hand side gives the result of the dense solve entry for
 * entry, lists exactly the nonzeros of its result, and leaves its right-hand side zero.
 */
class BasisLuTest {

  // a sparse random basis of size m: a permuted diagonal and a few entries per column
  private static double[][] basis(Random rnd, int m, int[][] idx, int[] len) {
    double[][] val = new double[m][];
    int[] perm = new int[m];
    for (int i = 0; i < m; i++) {
      perm[i] = i;
    }
    for (int i = m - 1; i > 0; i--) {
      int j = rnd.nextInt(i + 1);
      int t = perm[i];
      perm[i] = perm[j];
      perm[j] = t;
    }
    for (int k = 0; k < m; k++) {
      int extra = rnd.nextInt(3);
      idx[k] = new int[1 + extra];
      val[k] = new double[1 + extra];
      idx[k][0] = perm[k];
      val[k][0] = 1 + rnd.nextInt(4);
      int n = 1;
      for (int e = 0; e < extra; e++) {
        int i = rnd.nextInt(m);
        boolean dup = false;
        for (int f = 0; f < n; f++) {
          dup |= idx[k][f] == i;
        }
        if (!dup) {
          idx[k][n] = i;
          val[k][n++] = rnd.nextInt(7) - 3 + 0.5;
        }
      }
      len[k] = n;
    }
    return val;
  }

  // a random right-hand side with a few nonzeros, dense in d and listed in s / si
  private static int rhs(Random rnd, int m, double[] d, double[] s, int[] si) {
    int n = 0;
    int count = 1 + rnd.nextInt(3);
    for (int c = 0; c < count; c++) {
      int i = rnd.nextInt(m);
      if (s[i] == 0) {
        si[n++] = i;
      }
      double v = rnd.nextInt(9) - 4 + 0.25;
      s[i] += v;
      d[i] += v;
    }
    return n;
  }

  private static void assertSame(double[] dense, double[] sparse, int[] yi, int yn, String what) {
    boolean[] listed = new boolean[dense.length];
    for (int k = 0; k < yn; k++) {
      assertThat(listed[yi[k]]).as(what + " lists " + yi[k] + " twice").isFalse();
      listed[yi[k]] = true;
      assertThat(sparse[yi[k]]).as(what + " lists a zero").isNotZero();
    }
    for (int i = 0; i < dense.length; i++) {
      // the same double, up to the sign of a zero
      assertThat(sparse[i] == dense[i]).as(what + " entry " + i).isTrue();
      assertThat(listed[i] || sparse[i] == 0).as(what + " misses " + i).isTrue();
    }
  }

  private static void assertZero(double[] x, String what) {
    for (double v : x) {
      assertThat(v).as(what).isZero();
    }
  }

  @Test
  void hypersparseSolvesMatchDenseSolvesThroughUpdates() {
    Random rnd = new Random(11);
    int hyperSolves = 0;
    int flipHyperSolves = 0;
    for (int run = 0; run < 30; run++) {
      int m = 200 + rnd.nextInt(200);
      int[][] idx = new int[m][];
      int[] len = new int[m];
      double[][] val = basis(rnd, m, idx, len);
      BasisLu sparse = new BasisLu(m, idx, val, len);
      BasisLu dense = new BasisLu(m, idx, val, len);
      for (int step = 0; step < 60; step++) {
        String what = "run " + run + " step " + step;
        double[] d = new double[m];
        double[] s = new double[m];
        int[] si = new int[m];
        double[] yd = new double[m];
        double[] ys = new double[m];
        int[] yi = new int[m];
        // ftran of a column that enters, then the update with it
        int xn = rhs(rnd, m, d, s, si);
        dense.ftranColumn(d, yd);
        int yn = sparse.ftran(s, si, xn, ys, yi, true);
        assertSame(yd, ys, yi, yn, what + " ftranColumn");
        assertZero(s, what + " ftran rhs");
        hyperSolves += yn < m / 10 ? 1 : 0;
        // btran of a unit row and of a few positions
        d = new double[m];
        s = new double[m];
        int zn = rhs(rnd, m, d, s, si);
        double[] wd = new double[m];
        double[] ws = new double[m];
        dense.btran(d, wd);
        int wn = sparse.btran(s, si, zn, ws, yi);
        assertSame(wd, ws, yi, wn, what + " btran");
        assertZero(s, what + " btran rhs");
        // another ftran, not kept
        d = new double[m];
        s = new double[m];
        double[] td = new double[m];
        double[] ts = new double[m];
        xn = rhs(rnd, m, d, s, si);
        dense.ftran(d, td);
        int tn = sparse.ftran(s, si, xn, ts, yi, false);
        assertSame(td, ts, yi, tn, what + " ftran");
        // the ftran of bound flips, with its own history
        d = new double[m];
        s = new double[m];
        td = new double[m];
        ts = new double[m];
        xn = rhs(rnd, m, d, s, si);
        dense.ftran(d, td);
        tn = sparse.ftranFlips(s, si, xn, ts, yi);
        assertSame(td, ts, yi, tn, what + " ftranFlips");
        assertZero(s, what + " ftranFlips rhs");
        flipHyperSolves += tn < m / 10 ? 1 : 0;
        // replace a position whose entry in the solved column is not small
        int r = -1;
        for (int k = 0; k < m && r < 0; k++) {
          int q = (step * 37 + k) % m;
          if (Math.abs(yd[q]) > 0.1) {
            r = q;
          }
        }
        if (r < 0) {
          break;
        }
        boolean stableDense = dense.update(r);
        boolean stableSparse = sparse.update(r);
        assertThat(stableSparse).as(what + " update").isEqualTo(stableDense);
        if (!stableDense) {
          break;
        }
      }
    }
    // the searches ran on most of the solves
    assertThat(hyperSolves).isGreaterThan(500);
    assertThat(flipHyperSolves).isGreaterThan(500);
  }
}
