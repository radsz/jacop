/*
 * LinearConflictTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.lcg.LinearForm;
import org.junit.jupiter.api.Test;

/**
 * Tests cut-based conflict analysis ({@code jacop.lcg.linear=learn}) on random linear models
 * against brute force: the optimum must be the brute-force one, and every learnt sum must hold in
 * every solution of the model.
 */
class LinearConflictTest {

  @Test
  void learntSumsHoldInEverySolution() {
    String before = System.getProperty("jacop.lcg.linear");
    System.setProperty("jacop.lcg.linear", "learn");
    try {
      Random rnd = new Random(5);
      long learnt = 0;
      for (int instance = 0; instance < 600; instance++) {
        learnt += instance(rnd, instance);
      }
      assertThat(learnt).isGreaterThan(100);
    } finally {
      if (before == null) {
        System.clearProperty("jacop.lcg.linear");
      } else {
        System.setProperty("jacop.lcg.linear", before);
      }
    }
  }

  // one random model; returns the number of sums learnt
  private static int instance(Random rnd, int instance) {
    Store store = new Store();
    int n = 6;
    IntVar[] x = new IntVar[n + 1];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 4);
    }
    List<int[]> rows = new ArrayList<>(); // weights over x, then the relation (0 <=, 1 >=, 2 =), c
    for (int c = 3 + rnd.nextInt(5); c > 0; c--) {
      int[] row = new int[n + 2];
      for (int t = 0; t < 3 + rnd.nextInt(2); t++) {
        row[rnd.nextInt(n)] = rnd.nextInt(7) - 3;
      }
      row[n] = rnd.nextInt(5) == 0 ? 2 : rnd.nextInt(2);
      row[n + 1] = rnd.nextInt(9) - 2;
      rows.add(row);
      store.impose(
          new LinearInt(Arrays.copyOf(x, n), Arrays.copyOf(row, n), rel(row[n]), row[n + 1]));
    }
    int i0 = rnd.nextInt(n);
    int j0 = (i0 + 1 + rnd.nextInt(n - 1)) % n;
    int k0 = rnd.nextInt(n);
    boolean plus = k0 != i0 && k0 != j0 && rnd.nextBoolean();
    if (plus) {
      store.impose(new XplusYeqZ(x[i0], x[j0], x[k0]));
    }
    int[] cost = new int[n];
    for (int i = 0; i < n; i++) {
      cost[i] = rnd.nextInt(7) - 3;
    }
    x[n] = new IntVar(store, "cost", -100, 100);
    int[] withCost = Arrays.copyOf(cost, n + 1);
    withCost[n] = -1;
    store.impose(new LinearInt(x, withCost, "==", 0));

    // brute force: every solution, with its cost as x[n]
    List<int[]> solutions = new ArrayList<>();
    int[] t = new int[n + 1];
    for (int code = 0; code < 15625; code++) {
      int r = code;
      for (int i = 0; i < n; i++) {
        t[i] = r % 5;
        r /= 5;
      }
      boolean ok = !plus || t[i0] + t[j0] == t[k0];
      for (int[] row : rows) {
        long s = 0;
        for (int i = 0; i < n; i++) {
          s += (long) row[i] * t[i];
        }
        ok &= row[n] == 0 ? s <= row[n + 1] : row[n] == 1 ? s >= row[n + 1] : s == row[n + 1];
      }
      if (ok) {
        long s = 0;
        for (int i = 0; i < n; i++) {
          s += (long) cost[i] * t[i];
        }
        t[n] = (int) s;
        solutions.add(t.clone());
      }
    }
    long best = solutions.stream().mapToLong(s -> s[n]).min().orElse(Long.MAX_VALUE);

    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.sat().setSeed(instance);
    int status = solver.minimize(x[n]);
    if (solutions.isEmpty()) {
      assertThat(status).as("instance %d", instance).isEqualTo(CdclSolver.UNSAT);
    } else {
      assertThat(status).as("instance %d", instance).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(x[n])).as("instance %d", instance).isEqualTo(best);
    }
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    for (int i = 0; i <= n; i++) {
      index.put(x[i], i);
    }
    for (LinearForm f : solver.learntLinear()) {
      for (int[] s : solutions) {
        long sum = 0;
        for (int k = 0; k < f.vars().length; k++) {
          Integer i = index.get(f.vars()[k]);
          assertThat(i).as("instance %d: %s", instance, f).isNotNull();
          sum += f.weights()[k] * s[i];
        }
        assertThat(sum)
            .as("instance %d: %s cuts off a solution", instance, f)
            .isLessThanOrEqualTo(f.c());
      }
    }
    return solver.learntLinear().size();
  }

  private static String rel(int r) {
    return r == 0 ? "<=" : r == 1 ? ">=" : "==";
  }
}
