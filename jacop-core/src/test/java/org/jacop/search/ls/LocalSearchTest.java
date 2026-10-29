/*
 * LocalSearchTest.java
 * <p>
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

package org.jacop.search.ls;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** Tests of {@link LocalSearch}. */
class LocalSearchTest {

  private static final Duration LIMIT = Duration.ofSeconds(10);

  /** n queens with all-distinct diagonals, through views made by x + c = z. */
  @Test
  void findsQueens() {
    int n = 12;
    Store store = new Store();
    IntVar[] q = new IntVar[n];
    IntVar[] up = new IntVar[n];
    IntVar[] down = new IntVar[n];
    for (int i = 0; i < n; i++) {
      q[i] = new IntVar(store, "q" + i, 0, n - 1);
      up[i] = new IntVar(store, "u" + i, 0, 2 * n);
      down[i] = new IntVar(store, "d" + i, -n, n);
      store.impose(new XplusCeqZ(q[i], i, up[i]));
      store.impose(new XplusCeqZ(q[i], -i, down[i]));
    }
    store.impose(new Alldistinct(q));
    store.impose(new Alldistinct(up));
    store.impose(new Alldistinct(down));
    assertTrue(store.consistency());
    int level = store.level;
    List<int[]> found = new ArrayList<>();
    LocalSearch ls =
        LocalSearch.builder(store)
            .order(q)
            .timeLimit(LIMIT)
            .seed(3)
            .onSolution(
                s -> {
                  // the handler sees the solution in the store
                  int[] v = new int[n];
                  for (int i = 0; i < n; i++) {
                    assertTrue(q[i].singleton());
                    v[i] = q[i].value();
                  }
                  found.add(v);
                })
            .build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertEquals(level, store.level);
    assertEquals(1, found.size());
    int[] v = ls.getSolution(q);
    assertNotNull(v);
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        assertTrue(v[i] != v[j] && v[i] + i != v[j] + j && v[i] - i != v[j] - j);
      }
    }
  }

  /**
   * Minimises the makespan of tasks on a cumulative resource, with a reified linear constraint
   * between two tasks; each solution reported is better than the last.
   */
  @Test
  void improvesTheCost() {
    Store store = new Store();
    int n = 8;
    int[] dur = {3, 2, 4, 1, 2, 3, 2, 1};
    int[] use = {2, 1, 2, 1, 3, 1, 2, 2};
    IntVar[] s = new IntVar[n];
    IntVar[] d = new IntVar[n];
    IntVar[] r = new IntVar[n];
    IntVar makespan = new IntVar(store, "makespan", 0, 60);
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 40);
      d[i] = new IntVar(store, dur[i], dur[i]);
      r[i] = new IntVar(store, use[i], use[i]);
      store.impose(new LinearInt(new IntVar[] {s[i], makespan}, new int[] {1, -1}, "<=", -dur[i]));
    }
    store.impose(new Cumulative(s, d, r, new IntVar(store, 3, 3)));
    IntVar b = new IntVar(store, "b", 0, 1);
    store.impose(new Reified(new XeqC(s[0], 0), b));
    store.impose(new XeqC(b, 1));
    assertTrue(store.consistency());
    List<Integer> costs = new ArrayList<>();
    LocalSearch ls =
        LocalSearch.builder(store)
            .order(s)
            .minimize(makespan)
            .timeLimit(Duration.ofSeconds(2))
            .seed(5)
            .onSolution(x -> costs.add(makespan.value()))
            .build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertTrue(costs.size() >= 1);
    for (int k = 1; k < costs.size(); k++) {
      assertTrue(costs.get(k) < costs.get(k - 1), costs.toString());
    }
    assertEquals(costs.get(costs.size() - 1), ls.getCostValue());
    // the energy is 24 on a capacity of 3
    assertTrue(ls.getCostValue() >= 8);
    assertEquals(0, ls.getSolution(new IntVar[] {s[0]})[0]);
  }
}
