/*
 * PrecedenceCostLcgTest.java
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
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.PrecedenceCost;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * PrecedenceCost under lazy clause generation, with every explanation checked: random earliness and
 * tardiness problems with precedences (and a few start times that must differ, so that the search
 * conflicts), minimised with the global, and with the decomposition by depth-first search.
 */
class PrecedenceCostLcgTest {

  // -Dprecedencecost.lcg.instances=5000 for a longer run
  private static final int INSTANCES = Integer.getInteger("precedencecost.lcg.instances", 300);

  private record Problem(int n, int lo, int hi, int[][] prec, int[][] terms, int[][] differ) {

    static Problem random(Random r) {
      int n = 3 + r.nextInt(5);
      List<int[]> prec = new ArrayList<>();
      for (int j = 1; j < n; j++) {
        for (int i = 0; i < j; i++) {
          if (r.nextInt(3) == 0) {
            prec.add(new int[] {i, j, r.nextInt(5) - 1});
          }
        }
      }
      List<int[]> terms = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int k = r.nextInt(3); k > 0; k--) {
          terms.add(new int[] {i, r.nextInt(14), r.nextInt(4), r.nextInt(4)});
        }
      }
      List<int[]> differ = new ArrayList<>();
      for (int k = r.nextInt(n); k > 0; k--) {
        int i = r.nextInt(n);
        int j = r.nextInt(n);
        if (i != j) {
          differ.add(new int[] {i, j});
        }
      }
      return new Problem(
          n,
          r.nextInt(3),
          8 + r.nextInt(8),
          prec.toArray(new int[0][]),
          terms.toArray(new int[0][]),
          differ.toArray(new int[0][]));
    }

    IntVar[] post(Store store, IntVar cost, boolean global, boolean decomposition) {
      IntVar[] s = new IntVar[n];
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i, lo, hi);
      }
      for (int[] d : differ) {
        store.impose(new XneqY(s[d[0]], s[d[1]]));
      }
      if (decomposition) {
        for (int[] q : prec) {
          store.impose(
              new LinearInt(new IntVar[] {s[q[0]], s[q[1]]}, new int[] {1, -1}, "<=", -q[2]));
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
      }
      if (global) {
        store.impose(new PrecedenceCost(s, prec, terms, cost));
      }
      return s;
    }
  }

  @Test
  void minimizesWithCheckedExplanations() {
    long reasons = 0;
    long generic = 0;
    int solved = 0;
    for (int instance = 0; instance < INSTANCES; instance++) {
      Problem p = Problem.random(new Random(instance));

      Store reference = new Store();
      IntVar refCost = new IntVar(reference, "cost", 0, 2000);
      IntVar[] rs = p.post(reference, refCost, false, true);
      IntVar[] all = java.util.Arrays.copyOf(rs, p.n + 1);
      all[p.n] = refCost;
      Search<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(reference, new SimpleSelect<>(all, null, new IndomainMin<>()), refCost);

      Store store = new Store();
      IntVar cost = new IntVar(store, "cost", 0, 2000);
      p.post(store, cost, true, instance % 2 == 0);
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setSeed(instance % 3);
      int status = solver.minimize(cost);
      if (!found) {
        assertThat(status).as("instance %d %s", instance, p).isEqualTo(CdclSolver.UNSAT);
        continue;
      }
      assertThat(status).as("instance %d %s", instance, p).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(cost))
          .as("instance %d %s", instance, p)
          .isEqualTo(search.getCostValue());
      long[] counts = solver.explanationStatistics().get("PrecedenceCost");
      if (counts != null) {
        reasons += counts[0] + counts[3];
        generic += counts[1] + counts[4];
      }
      solved++;
    }
    assertThat(solved).isGreaterThan(INSTANCES / 2);
    assertThat(reasons).isPositive();
    // every propagation and failure of the constraint has a reason of its own
    assertThat(generic).isZero();
  }
}
