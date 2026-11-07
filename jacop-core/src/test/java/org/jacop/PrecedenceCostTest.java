/*
 * PrecedenceCostTest.java
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

import static org.assertj.core.api.Assertions.assertThatThrownBy;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.PrecedenceCost;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks of {@link PrecedenceCost}: its minimum over random boxes against a brute-force
 * enumeration, and optima of random earliness/tardiness problems with precedences against the
 * decomposition into linear constraints. Solution sets of the constraint alone are compared with a
 * brute-force enumeration in {@link GlobalConstraintBruteForceTest}.
 */
class PrecedenceCostTest {

  // -Dprecedencecost.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("precedencecost.instances", 1500);

  @Test
  void boundOfAChain() {
    // a before b by 3; a due 5, b due 6, tardiness 2 and 1, earliness 1 and 1
    // best: a = 4 (early 1) with b = 7 (late 1), or a = 5 with b = 8 (late 2), both cost 2
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 20);
    IntVar b = new IntVar(store, "b", 0, 20);
    IntVar c = new IntVar(store, "c", 0, 3);
    PrecedenceCost pc =
        new PrecedenceCost(
            new IntVar[] {a, b},
            new int[][] {{0, 1, 3}},
            new int[] {5, 6},
            new int[] {1, 1},
            new int[] {2, 1},
            c);
    store.impose(pc);
    assertTrue(store.consistency());
    assertEquals(2, c.min());
    assertEquals(2, pc.minimumCost());
    // a = 2 costs 3 and a = 5 costs 2 (with b = 8), a = 6 costs 2 + 3 and a = 7 costs 4 + 4;
    // the reduced cost of one path removes a = 7 and above
    assertEquals(2, a.min());
    assertTrue(a.max() >= 5 && a.max() <= 6, a.toString());
  }

  @Test
  void failsAboveTheMaximum() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 20);
    IntVar b = new IntVar(store, "b", 0, 20);
    IntVar c = new IntVar(store, "c", 0, 1);
    store.impose(
        new PrecedenceCost(
            new IntVar[] {a, b},
            new int[][] {{0, 1, 3}},
            new int[] {5, 6},
            new int[] {1, 1},
            new int[] {2, 1},
            c));
    assertFalse(store.consistency());
  }

  @Test
  void rejectsBadArguments() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 5);
    IntVar b = new IntVar(store, "b", 0, 5);
    IntVar c = new IntVar(store, "c", 0, 5);
    IntVar[] s = {a, b};
    int[][] none = new int[0][];
    assertThatThrownBy(() -> new PrecedenceCost(s, new int[][] {{0, 1, 1}, {1, 0, 1}}, none, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PrecedenceCost(s, new int[][] {{0, 2, 1}}, none, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PrecedenceCost(s, none, new int[][] {{0, 1, -1, 0}}, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PrecedenceCost(new IntVar[] {a, a}, none, none, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PrecedenceCost(new IntVar[] {a, c}, none, none, c))
        .isInstanceOf(IllegalArgumentException.class);
  }

  // a random acyclic graph with lags, and earliness and tardiness terms
  private record Problem(int n, int[][] prec, int[][] terms, int[] lo, int[] hi) {

    static Problem random(Random r, int maxTasks, int horizon) {
      int n = 1 + r.nextInt(maxTasks);
      List<int[]> prec = new ArrayList<>();
      for (int j = 1; j < n; j++) {
        for (int i = 0; i < j; i++) {
          if (r.nextInt(3) == 0) {
            prec.add(new int[] {i, j, r.nextInt(6) - 1});
          }
        }
      }
      List<int[]> terms = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int k = r.nextInt(3); k > 0; k--) {
          terms.add(new int[] {i, r.nextInt(horizon + 4) - 2, r.nextInt(4), r.nextInt(4)});
        }
      }
      int[] lo = new int[n];
      int[] hi = new int[n];
      for (int i = 0; i < n; i++) {
        lo[i] = r.nextInt(horizon / 2 + 1);
        hi[i] = lo[i] + r.nextInt(horizon / 2 + 1);
      }
      return new Problem(n, prec.toArray(new int[0][]), terms.toArray(new int[0][]), lo, hi);
    }

    long cost(int[] s) {
      long total = 0;
      for (int[] t : terms) {
        total +=
            (long) t[2] * Math.max(0, t[1] - s[t[0]]) + (long) t[3] * Math.max(0, s[t[0]] - t[1]);
      }
      return total;
    }

    boolean feasible(int[] s) {
      for (int[] p : prec) {
        if (s[p[1]] < s[p[0]] + p[2]) {
          return false;
        }
      }
      return true;
    }

    long bruteMinimum() {
      int[] s = lo.clone();
      long best = Long.MAX_VALUE;
      while (true) {
        if (feasible(s)) {
          best = Math.min(best, cost(s));
        }
        int k = 0;
        while (k < n && s[k] == hi[k]) {
          s[k] = lo[k];
          k++;
        }
        if (k == n) {
          return best;
        }
        s[k]++;
      }
    }

    @Override
    public String toString() {
      return "prec="
          + Arrays.deepToString(prec)
          + " terms="
          + Arrays.deepToString(terms)
          + " lo="
          + Arrays.toString(lo)
          + " hi="
          + Arrays.toString(hi);
    }
  }

  @Test
  void minimumMatchesBruteForce() {
    Random r = new Random(1);
    for (int t = 0; t < 4 * INSTANCES; t++) {
      Problem p = Problem.random(r, 5, 8);
      Store store = new Store();
      IntVar[] s = new IntVar[p.n];
      for (int i = 0; i < p.n; i++) {
        s[i] = new IntVar(store, "s" + i, p.lo[i], p.hi[i]);
      }
      IntVar c = new IntVar(store, "c", 0, 10_000);
      PrecedenceCost pc = new PrecedenceCost(s, p.prec, p.terms, c);
      assertEquals(p.bruteMinimum(), pc.minimumCost(), "instance " + t + ": " + p);
    }
  }

  /**
   * Random earliness/tardiness problems: tasks with durations under precedences between due dates;
   * the optimum with the constraint alone, with the decomposition alone and with both agree.
   */
  @Test
  void optimaMatchDecomposition() {
    Random r = new Random(2);
    for (int t = 0; t < INSTANCES; t++) {
      Problem p = Problem.random(r, 7, 14);
      long[] optimum = new long[3];
      for (int model = 0; model < 3; model++) {
        optimum[model] = optimum(p, model != 1, model != 0);
      }
      assertEquals(optimum[0], optimum[1], "instance " + t + ": " + p);
      assertEquals(optimum[0], optimum[2], "instance " + t + ": " + p);
    }
  }

  // the minimum cost, -1 when there is no schedule
  private static long optimum(Problem p, boolean decomposition, boolean global) {
    Store store = new Store();
    IntVar[] s = new IntVar[p.n];
    for (int i = 0; i < p.n; i++) {
      s[i] = new IntVar(store, "s" + i, p.lo[i], p.hi[i]);
    }
    IntVar cost = new IntVar(store, "cost", 0, 100_000);
    if (decomposition) {
      for (int[] q : p.prec) {
        store.impose(
            new LinearInt(new IntVar[] {s[q[0]], s[q[1]]}, new int[] {1, -1}, "<=", -q[2]));
      }
      IntVar[] vars = new IntVar[2 * p.terms.length + 1];
      int[] w = new int[vars.length];
      for (int k = 0; k < p.terms.length; k++) {
        int[] term = p.terms[k];
        IntVar early = new IntVar(store, "e" + k, 0, 1000);
        IntVar late = new IntVar(store, "l" + k, 0, 1000);
        // early >= b - s, late >= s - b
        store.impose(
            new LinearInt(new IntVar[] {early, s[term[0]]}, new int[] {1, 1}, ">=", term[1]));
        store.impose(
            new LinearInt(new IntVar[] {late, s[term[0]]}, new int[] {1, -1}, ">=", -term[1]));
        vars[2 * k] = early;
        w[2 * k] = term[2];
        vars[2 * k + 1] = late;
        w[2 * k + 1] = term[3];
      }
      vars[vars.length - 1] = cost;
      w[w.length - 1] = -1;
      store.impose(new LinearInt(vars, w, "<=", 0));
    }
    if (global) {
      store.impose(new PrecedenceCost(s, p.prec, p.terms, cost));
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    IntVar[] all = Arrays.copyOf(s, p.n + 1);
    all[p.n] = cost;
    SelectChoicePoint<IntVar> select = new SimpleSelect<>(all, null, new IndomainMin<>());
    boolean found = search.labeling(store, select, cost);
    return found ? search.getCostValue() : -1;
  }
}
