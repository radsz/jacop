/*
 * LinearRelaxationTest.java
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

package org.jacop.presolve;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** The root check of the linear relaxation. */
class LinearRelaxationTest {

  private static final int TRIALS = Integer.getInteger("presolve.lp.trials", 2000);

  private static final String[] RELATIONS = {"<=", "==", ">="};

  /**
   * A transport problem: every row of x sums to its supply, every column to at most its capacity.
   * Each constraint alone is satisfiable within the bounds, so propagation sees nothing; only the
   * sum of all rows against the sum of all columns shows that the supply exceeds the capacity.
   */
  private static Store transport(int[] supply, int[] capacity) {
    Store store = new Store();
    IntVar[][] x = new IntVar[supply.length][capacity.length];
    for (int i = 0; i < supply.length; i++) {
      for (int j = 0; j < capacity.length; j++) {
        x[i][j] = new IntVar(store, "x" + i + "_" + j, 0, 10);
      }
      store.impose(new LinearInt(x[i], ones(capacity.length), "==", supply[i]));
    }
    for (int j = 0; j < capacity.length; j++) {
      IntVar[] column = new IntVar[supply.length];
      for (int i = 0; i < supply.length; i++) {
        column[i] = x[i][j];
      }
      store.impose(new LinearInt(column, ones(supply.length), "<=", capacity[j]));
    }
    assertThat(store.consistency()).isTrue();
    return store;
  }

  private static int[] ones(int n) {
    int[] w = new int[n];
    Arrays.fill(w, 1);
    return w;
  }

  @Test
  void supplyAboveCapacityIsInfeasible() {
    // supply 3 * 16 = 48, capacity 4 * 11 = 44
    LinearRelaxation.Result r =
        LinearRelaxation.check(transport(new int[] {16, 16, 16}, new int[] {11, 11, 11, 11}), 1000);
    assertThat(r.infeasible()).isTrue();
    assertThat(r.rows()).isEqualTo(7);
    assertThat(r.columns()).isEqualTo(12);
  }

  @Test
  void supplyWithinCapacityIsNotReported() {
    // supply 48, capacity 48: the LP has a solution, and so has the problem
    LinearRelaxation.Result r =
        LinearRelaxation.check(transport(new int[] {16, 16, 16}, new int[] {12, 12, 12, 12}), 1000);
    assertThat(r.infeasible()).isFalse();
    assertThat(r.skipped()).isFalse();
  }

  /** A linear constraint as posted: sum(w * x) rel c. */
  private record Linear(int[] w, String rel, int c) {
    boolean holds(int[] point) {
      long sum = 0;
      for (int i = 0; i < w.length; i++) {
        sum += (long) w[i] * point[i];
      }
      return switch (rel) {
        case "<=" -> sum <= c;
        case ">=" -> sum >= c;
        default -> sum == c;
      };
    }
  }

  /**
   * Random small systems of linear constraints: whenever the check reports infeasibility, no
   * integer point of the bounds satisfies the constraints. It must also find some infeasible ones
   * that propagation does not, or the test proves nothing.
   */
  @Test
  void reportsInfeasibilityOnlyWithoutIntegerSolutions() {
    Random random = new Random(20261028);
    int reported = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Store store = new Store();
      int n = 2 + random.nextInt(3);
      IntVar[] x = new IntVar[n];
      int[] lo = new int[n];
      int[] hi = new int[n];
      for (int i = 0; i < n; i++) {
        lo[i] = random.nextInt(7) - 3;
        hi[i] = lo[i] + random.nextInt(5);
        x[i] = new IntVar(store, "x" + i, lo[i], hi[i]);
      }
      List<Linear> constraints = new ArrayList<>();
      int m = 2 + random.nextInt(4);
      for (int k = 0; k < m; k++) {
        int[] w = new int[n];
        for (int i = 0; i < n; i++) {
          w[i] = random.nextInt(7) - 3;
        }
        Linear l =
            new Linear(w, RELATIONS[random.nextInt(RELATIONS.length)], random.nextInt(13) - 6);
        constraints.add(l);
        store.impose(new LinearInt(x, w, l.rel(), l.c()));
      }
      if (!store.consistency()) {
        continue;
      }
      if (LinearRelaxation.check(store, 1000).infeasible()) {
        reported++;
        assertThat(hasSolution(lo, hi, constraints)).as("trial %d", trial).isFalse();
      }
    }
    assertThat(reported).isPositive();
  }

  // enumerates the integer points of the original bounds
  private static boolean hasSolution(int[] lo, int[] hi, List<Linear> constraints) {
    int[] point = lo.clone();
    while (true) {
      int[] p = point;
      if (constraints.stream().allMatch(l -> l.holds(p))) {
        return true;
      }
      int i = 0;
      while (i < point.length && point[i] == hi[i]) {
        point[i] = lo[i];
        i++;
      }
      if (i == point.length) {
        return false;
      }
      point[i]++;
    }
  }
}
