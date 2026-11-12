/*
 * RevisedDualSimplexCycleTest.java
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
import static org.assertj.core.api.Assertions.within;

import java.io.IOException;
import java.io.InputStream;
import java.util.concurrent.TimeUnit;
import java.util.zip.GZIPInputStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

/**
 * Tests that {@link RevisedDualSimplex} ends on LPs where it went round the same bases without end.
 * Two are Dantzig-Wolfe master LPs of work-task-variation (osolpro benchmarks/decomposition-bounds,
 * costs near 1e7): reduced costs of a few units in the last place, past the dual tolerance, took
 * either sign as the basis changed, so the dual simplex flipped two parallel columns to an
 * artificial bound and back at every check of its reduced costs, and the primal simplex let two
 * columns enter in turn after every refactorization. Each is solved with the round-off taken as
 * zero, and without that, by the guard against pivots back to recent bases alone. The third is a
 * small LP of the exact fuzzer where round-off of free columns at artificial bounds of 1e12 left a
 * row outside its bounds and the dual simplex swapped the slacks of two parallel rows forever.
 */
class RevisedDualSimplexCycleTest {

  private static final double INF = Double.POSITIVE_INFINITY;

  private static final int LIMIT = 100_000;

  private static LpProblem read(String name) throws IOException {
    try (InputStream in =
        new GZIPInputStream(RevisedDualSimplexCycleTest.class.getResourceAsStream(name))) {
      return MpsReader.read(in, name);
    }
  }

  private static void solves(String name, boolean primal, double roundOff, double optimum)
      throws IOException {
    LpProblem p = read(name);
    RevisedDualSimplex lp = p.simplex(true);
    lp.setExact(true);
    lp.setRoundOff(roundOff);
    int status = primal ? lp.solvePrimal(LIMIT) : lp.solve(LIMIT);
    assertThat(status).isEqualTo(RevisedDualSimplex.OPTIMAL);
    assertThat(lp.objective() + p.costConstant).isCloseTo(optimum, within(1e-6 * optimum));
    assertThat(lp.pivots()).isLessThan(5_000);
  }

  @Test
  @Timeout(value = 20, unit = TimeUnit.SECONDS)
  void dualSimplexEndsOnMasterLp() throws IOException {
    solves("jalp-dual-cycles.mps.gz", false, 1e-14, 28339273.0556);
    solves("jalp-dual-cycles.mps.gz", false, 0, 28339273.0556);
    solves("jalp-dual-cycles.mps.gz", true, 1e-14, 28339273.0556);
  }

  @Test
  @Timeout(value = 20, unit = TimeUnit.SECONDS)
  void primalSimplexEndsOnMasterLp() throws IOException {
    solves("jalp-primal-hangs.mps.gz", true, 1e-14, 23568462.1497);
    solves("jalp-primal-hangs.mps.gz", true, 0, 23568462.1497);
    solves("jalp-primal-hangs.mps.gz", false, 1e-14, 23568462.1497);
  }

  @Test
  @Timeout(value = 10, unit = TimeUnit.SECONDS)
  void roundOffCycleOfParallelRowsEnds() {
    // rows 0 and 1 are parallel, and so are rows 7 and 8; columns 1, 3, 5 and 9 are free
    int[][] c = {
      {2, 5, 6, 8, 9},
      {2, 5, 6, 8, 9},
      {2, 3, 4, 5, 6, 8},
      {2, 3, 4, 5, 6, 8},
      {6, 7},
      {0, 5, 7},
      {0, 5, 7},
      {0, 1, 2, 3, 5, 9},
      {0, 1, 2, 3, 5, 9}
    };
    double[][] v = {
      {-3, -4, -7, 7, 9},
      {3, 4, 7, -7, -9},
      {-3, 5, -2, -6, -1, -1},
      {9, -15, 6, 18, 3, 3},
      {-5, -3},
      {-3, 4, 3},
      {3, -4, -3},
      {1, -3, 5, -4, 3, 1},
      {-1, 3, -5, 4, -3, -1}
    };
    double[] rowLo = {-INF, -8, 2, -6, -INF, -2, 1, 9, -INF};
    double[] rowHi = {8, INF, 2, -6, -1, -1, 2, INF, -9};
    double[] cost = {-5, 1, -2, -1, -1, -5, 5, 2, -1, 5, -2};
    double[] lo = {1, -INF, -INF, -INF, 0, -INF, -1, -2, 3, -INF, 2};
    double[] hi = {3, INF, 6, INF, 7, INF, INF, 1, INF, 0, INF};
    RevisedDualSimplex lp = new RevisedDualSimplex(c, v, rowLo, rowHi, cost, true);
    for (int j = 0; j < cost.length; j++) {
      lp.setBounds(j, lo[j], hi[j]);
    }
    assertThat(lp.solve(LIMIT)).isEqualTo(RevisedDualSimplex.UNBOUNDED);
    // a cut that leaves the problem unbounded (x1 and x5 are still free)
    lp.addRows(
        new int[][] {{0, 3, 10}},
        new double[][] {{4, -4, -2}},
        new double[] {-15},
        new double[] {-13});
    assertThat(lp.solve(LIMIT)).isEqualTo(RevisedDualSimplex.UNBOUNDED);
    assertThat(lp.pivots()).isLessThan(1_000);
  }
}
