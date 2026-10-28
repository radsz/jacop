/*
 * EnergyPrecedenceTest.java
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

package org.jacop;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.EnergyPrecedence;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.junit.jupiter.api.Test;

/**
 * Checks of {@link EnergyPrecedence}: the example of Laborie's paper, the bound after a set of
 * successors, and the solutions of random project scheduling problems, which must not change when
 * the constraint is added to the cumulative and the precedences. Solution sets of the constraint
 * alone are compared with a brute-force enumeration in {@link GlobalConstraintBruteForceTest}.
 */
class EnergyPrecedenceTest {

  // -Denergyprecedence.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("energyprecedence.instances", 1000);

  @Test
  void energyOfThePredecessors() {
    // Fig. 5 of the paper: four tasks of height 2 before x on a resource of capacity 4
    Store store = new Store();
    int[] durations = {10, 2, 8, 8};
    IntVar[] s = new IntVar[4];
    IntVar[] d = new IntVar[4];
    IntVar[] r = new IntVar[4];
    IntVar x = new IntVar(store, "x", 0, 100);
    IntVar[] from = new IntVar[4];
    IntVar[] to = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 100);
      d[i] = new IntVar(store, durations[i], durations[i]);
      r[i] = new IntVar(store, 2, 2);
      from[i] = s[i];
      to[i] = x;
    }
    IntVar limit = new IntVar(store, 4, 4);
    store.impose(new EnergyPrecedence(s, d, r, limit, from, to, durations));
    assertTrue(store.consistency());
    // (2 * 10 + 2 * 2 + 2 * 8 + 2 * 8) / 4
    assertEquals(14, x.min());
  }

  @Test
  void energyOfTheSuccessors() {
    // a chain a -> b, then three tasks of height 1 after b on a resource of capacity 1, due by 20
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 20);
    IntVar[] s = new IntVar[4];
    IntVar[] d = new IntVar[4];
    IntVar[] r = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 20 - 4);
      d[i] = new IntVar(store, 4, 4);
      r[i] = new IntVar(store, 1, 1);
    }
    // a + 1 <= s0, and s0 + 4 <= s1, s2, s3
    IntVar[] from = {a, s[0], s[0], s[0]};
    IntVar[] to = {s[0], s[1], s[2], s[3]};
    int[] lag = {1, 4, 4, 4};
    store.impose(new EnergyPrecedence(s, d, r, new IntVar(store, 1, 1), from, to, lag));
    assertTrue(store.consistency());
    // s1, s2 and s3 need 12 units before 20, so s0 <= 20 - 12 - 4 and a <= s0 - 1
    assertEquals(4, s[0].max());
    assertEquals(3, a.max());
  }

  @Test
  void randomProjectsKeepTheirSolutions() {
    Random random = new Random(20261027);
    int pruned = 0;
    for (int k = 0; k < INSTANCES; k++) {
      Project p = Project.random(random);
      long[] with = p.solve(true);
      long[] without = p.solve(false);
      assertEquals(without[0], with[0], () -> "solutions of " + p);
      assertEquals(without[1], with[1], () -> "optimum of " + p);
      if (with[2] < without[2]) {
        pruned++;
      }
    }
    // the instances are large enough for the rule to cut the search on some of them
    assertTrue(pruned > INSTANCES / 20, "the rule pruned on " + pruned + " instances");
  }

  /** Tasks with precedences (a DAG with some negative lags) and a makespan after every task. */
  private record Project(
      int n, int horizon, int[] dur, int[] height, int capacity, List<int[]> arcs) {

    @Override
    public String toString() {
      StringBuilder b = new StringBuilder("dur=" + Arrays.toString(dur));
      b.append(" height=").append(Arrays.toString(height)).append(" capacity=").append(capacity);
      for (int[] a : arcs) {
        b.append(" s").append(a[0]).append("+").append(a[2]).append("<=s").append(a[1]);
      }
      return b.toString();
    }

    static Project random(Random random) {
      int n = 3 + random.nextInt(3);
      int[] dur = new int[n];
      int[] height = new int[n];
      int capacity = 2 + random.nextInt(2);
      int total = 0;
      for (int i = 0; i < n; i++) {
        dur[i] = 1 + random.nextInt(3);
        height[i] = 1 + random.nextInt(capacity);
        total += dur[i];
      }
      List<int[]> arcs = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          int c = random.nextInt(6);
          if (c < 2) {
            // i ends before j starts, sometimes with a delay
            arcs.add(new int[] {i, j, dur[i] + (c == 1 ? 1 : 0)});
          } else if (c == 2) {
            // a start-to-start lag, which may or may not order the tasks
            arcs.add(new int[] {i, j, random.nextInt(dur[i] + 1)});
          } else if (c == 3) {
            // a maximal delay: j starts at most 3 after i
            arcs.add(new int[] {j, i, -3});
          }
        }
      }
      return new Project(n, total + 1, dur, height, capacity, arcs);
    }

    // solutions, best makespan and decisions to enumerate all solutions
    long[] solve(boolean energy) {
      Store store = new Store();
      IntVar[] vars = model(store, energy);
      long solutions = 0;
      long decisions = 0;
      if (store.consistency()) {
        Search<IntVar> search = new DepthFirstSearch<>();
        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(false);
        search.setPrintInfo(false);
        if (search.labeling(store, new InputOrderSelect<>(store, vars, new IndomainMin<>()))) {
          solutions = search.getSolutionListener().solutionsNo();
        }
        decisions = search.getDecisions();
      }
      long best = -1;
      Store again = new Store();
      IntVar[] v = model(again, energy);
      if (again.consistency()) {
        Search<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        SelectChoicePoint<IntVar> select = new InputOrderSelect<>(again, v, new IndomainMin<>());
        if (search.labeling(again, select, v[n])) {
          best = search.getCostValue();
        }
      }
      return new long[] {solutions, best, decisions};
    }

    // the starts followed by the makespan
    private IntVar[] model(Store store, boolean energy) {
      IntVar[] s = new IntVar[n];
      IntVar[] d = new IntVar[n];
      IntVar[] r = new IntVar[n];
      IntVar makespan = new IntVar(store, "makespan", 0, horizon);
      List<IntVar> from = new ArrayList<>();
      List<IntVar> to = new ArrayList<>();
      List<Integer> lags = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i, 0, horizon);
        d[i] = new IntVar(store, dur[i], dur[i]);
        r[i] = new IntVar(store, height[i], height[i]);
      }
      for (int[] a : arcs) {
        from.add(s[a[0]]);
        to.add(s[a[1]]);
        lags.add(a[2]);
      }
      for (int i = 0; i < n; i++) {
        from.add(s[i]);
        to.add(makespan);
        lags.add(dur[i]);
      }
      for (int k = 0; k < from.size(); k++) {
        store.impose(new XplusClteqZ(from.get(k), lags.get(k), to.get(k)));
      }
      IntVar limit = new IntVar(store, capacity, capacity);
      store.impose(new CumulativeBasic(s, d, r, limit));
      if (energy) {
        store.impose(
            new EnergyPrecedence(
                s,
                d,
                r,
                limit,
                from.toArray(new IntVar[0]),
                to.toArray(new IntVar[0]),
                lags.stream().mapToInt(Integer::intValue).toArray()));
      }
      IntVar[] vars = Arrays.copyOf(s, n + 1);
      vars[n] = makespan;
      return vars;
    }
  }
}
