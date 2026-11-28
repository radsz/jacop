/*
 * DualAggregateCutsTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in material and source distributions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.junit.jupiter.api.Test;

/** The MIR cuts of the rows weighted by their LP duals, on weighted multiset covers. */
class DualAggregateCutsTest {

  /**
   * Covers with near-equal weights (MiniZinc Challenge 2021 wmsmc-int in small): the cuts keep the
   * optimum, never raise the root bound above it, and raise it above the plain LP bound, since the
   * rounded dual row counts the candidates a cover needs.
   */
  @Test
  void coversKeepTheirOptimum() {
    Random rnd = new Random(11);
    long dual = 0;
    int raised = 0;
    boolean was = LinearRelaxation.dualAggregateOn;
    try {
      for (int run = 0; run < 40; run++) {
        int[][] a = new int[3][6 + rnd.nextInt(3)];
        int[] req = new int[3];
        int[] w = new int[a[0].length];
        for (int c = 0; c < w.length; c++) {
          w[c] = 100 + rnd.nextInt(4);
          for (int e = 0; e < 3; e++) {
            a[e][c] = rnd.nextInt(3) == 0 ? 0 : 1 + rnd.nextInt(9);
          }
        }
        for (int e = 0; e < 3; e++) {
          req[e] = 10 + rnd.nextInt(30);
        }
        LinearRelaxation.dualAggregateOn = false;
        long expected = new Cover(a, req, w).optimum();
        Cover plain = new Cover(a, req, w);
        LinearRelaxation p = LinearRelaxation.of(plain.store, plain.cost, false);
        plain.store.impose(p);
        assertThat(plain.optimum()).as("run %d", run).isEqualTo(expected);
        LinearRelaxation.dualAggregateOn = true;
        Cover m = new Cover(a, req, w);
        LinearRelaxation r = LinearRelaxation.of(m.store, m.cost, false);
        assertThat(r).as("run %d", run).isNotNull();
        m.store.impose(r);
        assertThat(m.optimum()).as("run %d", run).isEqualTo(expected);
        if (!Double.isNaN(r.cutBound)) {
          assertThat(r.cutBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
          if (!Double.isNaN(p.cutBound) && r.cutBound > p.cutBound + 1e-6) {
            raised++;
          }
        }
        dual += r.dualCuts;
      }
    } finally {
      LinearRelaxation.dualAggregateOn = was;
    }
    assertThat(dual).isPositive();
    assertThat(raised).isPositive();
  }

  // min cost = sum w x subject to sum_c a[e][c] x_c >= req[e] for each element e, x in 0..6
  private static final class Cover {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    Cover(int[][] a, int[] req, int[] w) {
      int n = w.length;
      x = new IntVar[n];
      int total = 0;
      for (int c = 0; c < n; c++) {
        x[c] = new IntVar(store, "x" + c, 0, 6);
        total += 6 * w[c];
      }
      cost = new IntVar(store, "cost", 0, total);
      for (int e = 0; e < a.length; e++) {
        store.impose(new LinearInt(x, a[e], ">=", req[e]));
      }
      IntVar[] vars = new IntVar[n + 1];
      int[] ws = new int[n + 1];
      for (int c = 0; c < n; c++) {
        vars[c] = x[c];
        ws[c] = w[c];
      }
      vars[n] = cost;
      ws[n] = -1;
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
