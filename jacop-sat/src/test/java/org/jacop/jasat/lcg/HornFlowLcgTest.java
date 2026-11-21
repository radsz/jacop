/*
 * HornFlowLcgTest.java
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

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Map;
import java.util.Random;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.HornFlow;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Solves random scheduling instances with {@link HornFlow} under lazy clause generation with every
 * explanation checked, alone (so that its min-cut explanations drive the search) and next to {@link
 * Cumulative}, and compares satisfiability with a depth-first search over the cumulative alone.
 */
class HornFlowLcgTest {

  private static final int TRIALS = Integer.getInteger("hornflow.lcg.trials", 1000);

  @Test
  void minCutExplanationsAreSound() {
    Random rnd = new Random(Long.getLong("hornflow.seed", 20261106L));
    long failures = 0;
    long generic = 0;
    int sat = 0;
    int unsat = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      int n = 4 + rnd.nextInt(10);
      boolean unit = rnd.nextBoolean();
      int capacity = unit ? 2 + rnd.nextInt(2) : 2 + rnd.nextInt(3);
      int[] lo = new int[n];
      int[] hi = new int[n];
      int[] p = new int[n];
      int[] r = new int[n];
      int energy = 0;
      for (int j = 0; j < n; j++) {
        p[j] = 1 + rnd.nextInt(4);
        r[j] = unit ? 1 : 1 + rnd.nextInt(capacity);
        energy += p[j] * r[j];
      }
      int horizon = Math.max(4, (energy + capacity - 1) / capacity + rnd.nextInt(3));
      for (int j = 0; j < n; j++) {
        p[j] = Math.min(p[j], horizon);
        lo[j] = rnd.nextInt(horizon - p[j] + 1);
        hi[j] = lo[j] + rnd.nextInt(horizon - p[j] - lo[j] + 1);
      }
      boolean variableLimit = rnd.nextInt(4) == 0;
      boolean withCumulative = rnd.nextBoolean();
      boolean compulsory = rnd.nextBoolean();

      boolean expected = reference(lo, hi, p, r, capacity);

      Store store = new Store();
      IntVar[] s = new IntVar[n];
      IntVar[] d = new IntVar[n];
      IntVar[] u = new IntVar[n];
      for (int j = 0; j < n; j++) {
        s[j] = new IntVar(store, "s" + j, lo[j], hi[j]);
        d[j] = new IntVar(store, p[j], p[j]);
        u[j] = new IntVar(store, r[j], r[j]);
      }
      IntVar limit =
          variableLimit
              ? new IntVar(store, "c", capacity - 1, capacity)
              : new IntVar(store, capacity, capacity);
      if (variableLimit) {
        // the limit is a variable bound by the model, which the explanations cite
        store.impose(new org.jacop.constraints.XeqC(limit, capacity));
      }
      HornFlow flow = new HornFlow(s, d, u, limit);
      flow.useCompulsoryParts(compulsory);
      store.impose(flow);
      if (withCumulative) {
        store.impose(new Cumulative(s, d, u, limit));
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("trial %d", trial)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        sat++;
      } else {
        unsat++;
      }
      Map<String, long[]> stats = solver.explanationStatistics();
      long[] c = stats.get("HornFlow");
      if (c != null) {
        failures += c[3];
        generic += c[4];
      }
    }
    System.out.printf(
        "HornFlowLcgTest: %d sat, %d unsat, %d HornFlow failures explained, %d generic%n",
        sat, unsat, failures, generic);
    assertThat(failures).isGreaterThan(0);
    assertThat(generic).isZero();
  }

  private static boolean reference(int[] lo, int[] hi, int[] p, int[] r, int capacity) {
    Store store = new Store();
    int n = p.length;
    IntVar[] s = new IntVar[n];
    IntVar[] d = new IntVar[n];
    IntVar[] u = new IntVar[n];
    for (int j = 0; j < n; j++) {
      s[j] = new IntVar(store, lo[j], hi[j]);
      d[j] = new IntVar(store, p[j], p[j]);
      u[j] = new IntVar(store, r[j], r[j]);
    }
    store.impose(new Cumulative(s, d, u, new IntVar(store, capacity, capacity)));
    if (!store.consistency()) {
      return false;
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    return search.labeling(store, new SimpleSelect<>(s, null, new IndomainMin<>()));
  }
}
