/*
 * ZeroHalfCutsTest.java
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

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests the zero-half separator: on an odd cycle of edge rows it finds the whole cycle, every set
 * it returns on random rows has an odd right side and the violation it was chosen for, and the
 * relaxation of random weighted stable-set models with the cuts keeps their optimum while the cuts
 * raise the root bound of odd cycles.
 */
class ZeroHalfCutsTest {

  /** {@code x_i + x_(i+1) <= 1} around a 5-cycle at x = 1/2: the five rows sum to 2 sum x <= 5. */
  @Test
  void oddCycleOfEdgesIsOneSet() {
    int n = 5;
    int[][] columns = new int[n][];
    long[][] weights = new long[n][];
    boolean[] odd = new boolean[n];
    double[] slack = new double[n];
    for (int i = 0; i < n; i++) {
      columns[i] = new int[] {i, (i + 1) % n};
      weights[i] = new long[] {1, 1};
      odd[i] = true; // right side 1, both columns at their lower bound 0
    }
    double[] distance = new double[n];
    java.util.Arrays.fill(distance, 0.5);
    List<int[]> sets = ZeroHalfCuts.separate(columns, weights, odd, slack, distance, 10);
    assertThat(sets).isNotEmpty();
    assertThat(sets.get(0)).containsExactly(0, 1, 2, 3, 4);
  }

  /** An even cycle has no zero-half cut: its edge rows at 1/2 give no odd combination. */
  @Test
  void evenCycleHasNoSet() {
    int n = 6;
    int[][] columns = new int[n][];
    long[][] weights = new long[n][];
    boolean[] odd = new boolean[n];
    for (int i = 0; i < n; i++) {
      columns[i] = new int[] {i, (i + 1) % n};
      weights[i] = new long[] {1, 1};
      odd[i] = true;
    }
    double[] distance = new double[n];
    java.util.Arrays.fill(distance, 0.5);
    List<int[]> sets = ZeroHalfCuts.separate(columns, weights, odd, new double[n], distance, 10);
    for (int[] set : sets) {
      // the six rows sum to an even right side: no set may take all of them
      assertThat(set.length).isLessThan(n);
    }
  }

  /**
   * Every set returned has an odd sum of right sides, and the slack of its rows plus the distance
   * of the columns left odd in its sum is below 0.8, the violation of at least 0.1 it was chosen
   * for.
   */
  @Test
  void setsAreOddAndViolated() {
    Random rnd = new Random(3);
    int found = 0;
    for (int run = 0; run < 2000; run++) {
      int rows = 2 + rnd.nextInt(12);
      int cols = 2 + rnd.nextInt(10);
      int[][] columns = new int[rows][];
      long[][] weights = new long[rows][];
      boolean[] odd = new boolean[rows];
      double[] slack = new double[rows];
      for (int i = 0; i < rows; i++) {
        List<Integer> cs = new ArrayList<>();
        for (int j = 0; j < cols; j++) {
          if (rnd.nextInt(3) == 0) {
            cs.add(j);
          }
        }
        if (cs.isEmpty()) {
          cs.add(rnd.nextInt(cols));
        }
        columns[i] = cs.stream().mapToInt(Integer::intValue).toArray();
        weights[i] = new long[columns[i].length];
        for (int k = 0; k < weights[i].length; k++) {
          weights[i][k] = rnd.nextInt(7) - 3L;
        }
        odd[i] = rnd.nextBoolean();
        slack[i] = rnd.nextInt(3) == 0 ? 0 : rnd.nextDouble() * 0.3;
      }
      double[] distance = new double[cols];
      for (int j = 0; j < cols; j++) {
        distance[j] = rnd.nextInt(3) == 0 ? 0 : rnd.nextDouble() * 0.5;
      }
      for (int[] set : ZeroHalfCuts.separate(columns, weights, odd, slack, distance, 50)) {
        found++;
        boolean parity = false;
        double cost = 0;
        long[] colParity = new long[cols];
        for (int i : set) {
          parity ^= odd[i];
          cost += slack[i];
          for (int k = 0; k < columns[i].length; k++) {
            colParity[columns[i][k]] += weights[i][k];
          }
        }
        for (int j = 0; j < cols; j++) {
          if ((colParity[j] & 1) != 0) {
            cost += distance[j];
          }
        }
        assertThat(parity).as("run %d", run).isTrue();
        assertThat(cost).as("run %d", run).isLessThan(0.8 + 1e-9);
      }
    }
    assertThat(found).isGreaterThan(100);
  }

  /**
   * Weighted stable sets on random graphs with odd cycles: the relaxation with zero-half cuts keeps
   * the optimum found without it, its root bound stays below the optimum, and on the 5-cycles (unit
   * weights, LP bound 5/2, optimum 2) the cuts raise the bound to the optimum.
   */
  @Test
  void stableSetsKeepTheirOptimum() {
    Random rnd = new Random(7);
    long zeroHalf = 0;
    boolean was = LinearRelaxation.zeroHalfOn;
    LinearRelaxation.zeroHalfOn = true;
    try {
      for (int run = 0; run < 60; run++) {
        int n = run % 3 == 0 ? 5 : 5 + rnd.nextInt(6);
        List<int[]> edges = new ArrayList<>();
        for (int i = 0; i < n; i++) {
          edges.add(new int[] {i, (i + 1) % n});
        }
        if (run % 3 != 0) {
          for (int e = 0; e < n / 2; e++) {
            int a = rnd.nextInt(n);
            int b = rnd.nextInt(n);
            if (a != b) {
              edges.add(new int[] {a, b});
            }
          }
        }
        long[] w = new long[n];
        for (int i = 0; i < n; i++) {
          w[i] = run % 3 == 0 ? 1 : 1 + rnd.nextInt(5);
        }
        long expected = new Model(n, edges, w).optimum();
        Model m = new Model(n, edges, w);
        LinearRelaxation r = LinearRelaxation.of(m.store, m.cost, false);
        assertThat(r).as("run %d", run).isNotNull();
        m.store.impose(r);
        long got = m.optimum();
        assertThat(got).as("run %d", run).isEqualTo(expected);
        assertThat(r.rootBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
        if (!Double.isNaN(r.cutBound)) {
          assertThat(r.cutBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
        }
        if (run % 3 == 0) {
          assertThat(r.cutBound).as("run %d", run).isGreaterThanOrEqualTo(expected - 1e-6);
        }
        zeroHalf += r.zeroHalfCuts;
      }
    } finally {
      LinearRelaxation.zeroHalfOn = was;
    }
    assertThat(zeroHalf).isPositive();
  }

  // maximum weight stable set as min cost = -sum w x, with x_a + x_b <= 1 for each edge
  private static final class Model {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    Model(int n, List<int[]> edges, long[] w) {
      x = new IntVar[n];
      long total = 0;
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
        total += w[i];
      }
      cost = new IntVar(store, "cost", (int) -total, 0);
      for (int[] e : edges) {
        store.impose(new LinearInt(new IntVar[] {x[e[0]], x[e[1]]}, new int[] {1, 1}, "<=", 1));
      }
      IntVar[] vars = new IntVar[n + 1];
      int[] ws = new int[n + 1];
      for (int i = 0; i < n; i++) {
        vars[i] = x[i];
        ws[i] = (int) w[i];
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
}
