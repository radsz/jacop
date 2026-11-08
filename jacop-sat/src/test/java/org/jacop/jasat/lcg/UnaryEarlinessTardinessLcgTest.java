/*
 * UnaryEarlinessTardinessLcgTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Or;
import org.jacop.constraints.UnaryEarlinessTardiness;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * UnaryEarlinessTardiness under lazy clause generation, with every explanation checked: random
 * earliness and tardiness problems on one or two unary machines (stated as disjunctions), with or
 * without precedences (then relaxed in the bound with Lagrangian multipliers), minimised with the
 * global and compared with the decomposition alone by depth-first search.
 */
class UnaryEarlinessTardinessLcgTest {

  // -Dunaryet.lcg.instances=5000 for a longer run
  private static final int INSTANCES = Integer.getInteger("unaryet.lcg.instances", 300);

  private record Problem(
      int n, int[] p, int[] lo, int[] hi, int[][] machines, int[][] terms, int[][] precedences) {

    static Problem random(Random r) {
      int n = 3 + r.nextInt(4);
      int[] p = new int[n];
      int[] lo = new int[n];
      int[] hi = new int[n];
      for (int i = 0; i < n; i++) {
        p[i] = 1 + r.nextInt(4);
        lo[i] = r.nextInt(4);
        hi[i] = lo[i] + 6 + r.nextInt(10);
      }
      int count = 1 + r.nextInt(2);
      List<List<Integer>> on = new ArrayList<>();
      for (int m = 0; m < count; m++) {
        on.add(new ArrayList<>());
      }
      for (int i = 0; i < n; i++) {
        on.get(r.nextInt(count)).add(i);
      }
      int[][] machines = new int[count][];
      for (int m = 0; m < count; m++) {
        machines[m] = on.get(m).stream().mapToInt(Integer::intValue).toArray();
      }
      List<int[]> terms = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int k = r.nextInt(3); k > 0; k--) {
          terms.add(new int[] {i, r.nextInt(16), r.nextInt(4), r.nextInt(4)});
        }
      }
      List<int[]> precedences = new ArrayList<>();
      if (r.nextBoolean()) {
        for (int i = 0; i < n; i++) {
          for (int j = i + 1; j < n; j++) {
            if (r.nextInt(4) == 0) {
              precedences.add(new int[] {i, j, r.nextInt(p[i] + 2)});
            }
          }
        }
      }
      return new Problem(
          n, p, lo, hi, machines, terms.toArray(new int[0][]), precedences.toArray(new int[0][]));
    }

    IntVar[] post(Store store, IntVar cost, boolean global) {
      IntVar[] s = new IntVar[n];
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i, lo[i], hi[i]);
      }
      int[] owner = new int[n];
      for (int m = 0; m < machines.length; m++) {
        int[] tasks = machines[m];
        for (int a = 0; a < tasks.length; a++) {
          owner[tasks[a]] = m;
          for (int b = a + 1; b < tasks.length; b++) {
            int i = tasks[a];
            int j = tasks[b];
            store.impose(
                new Or(new XplusClteqZ(s[i], p[i], s[j]), new XplusClteqZ(s[j], p[j], s[i])));
          }
        }
      }
      for (int[] q : precedences) {
        store.impose(new XplusClteqZ(s[q[0]], q[2], s[q[1]]));
      }
      IntVar[] vars = new IntVar[2 * terms.length + 1];
      int[] w = new int[vars.length];
      for (int k = 0; k < terms.length; k++) {
        int[] t = terms[k];
        IntVar early = new IntVar(store, "e" + k, 0, 100);
        IntVar late = new IntVar(store, "l" + k, 0, 100);
        store.impose(new LinearInt(new IntVar[] {early, s[t[0]]}, new int[] {1, 1}, ">=", t[1]));
        store.impose(new LinearInt(new IntVar[] {late, s[t[0]]}, new int[] {1, -1}, ">=", -t[1]));
        vars[2 * k] = early;
        w[2 * k] = t[2];
        vars[2 * k + 1] = late;
        w[2 * k + 1] = t[3];
      }
      vars[vars.length - 1] = cost;
      w[w.length - 1] = -1;
      store.impose(new LinearInt(vars, w, "<=", 0));
      if (global) {
        store.impose(new UnaryEarlinessTardiness(s, p, machines, owner, terms, precedences, cost));
      }
      return s;
    }
  }

  @Test
  void minimizesWithCheckedExplanations() {
    long reasons = 0;
    int solved = 0;
    for (int instance = 0; instance < INSTANCES; instance++) {
      Problem q = Problem.random(new Random(instance));

      Store reference = new Store();
      IntVar refCost = new IntVar(reference, "cost", 0, 2000);
      IntVar[] rs = q.post(reference, refCost, false);
      IntVar[] all = Arrays.copyOf(rs, q.n + 1);
      all[q.n] = refCost;
      Search<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(reference, new SimpleSelect<>(all, null, new IndomainMin<>()), refCost);

      Store store = new Store();
      IntVar cost = new IntVar(store, "cost", 0, 2000);
      q.post(store, cost, true);
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setSeed(instance % 3);
      int status;
      try {
        status = solver.minimize(cost);
      } catch (IllegalStateException e) {
        throw new IllegalStateException("instance " + instance, e);
      }
      if (!found) {
        assertThat(status).as("instance %d %s", instance, q).isEqualTo(CdclSolver.UNSAT);
        continue;
      }
      assertThat(status).as("instance %d %s", instance, q).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(cost))
          .as("instance %d %s", instance, q)
          .isEqualTo(search.getCostValue());
      long[] counts = solver.explanationStatistics().get("UnaryEarlinessTardiness");
      if (counts != null) {
        reasons += counts[0] + counts[3];
      }
      solved++;
    }
    assertThat(solved).isGreaterThan(INSTANCES / 2);
    assertThat(reasons).isPositive();
  }
}
