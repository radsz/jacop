/*
 * ConjunctionSumTest.java
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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Random;
import org.jacop.constraints.ConjunctionSum;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link ConjunctionSum}: its bounds on small cases, solution counts against brute force,
 * and its reasons for lazy clause generation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class ConjunctionSumTest {

  // a random instance: variables with small domains and terms of one to three literals
  private record Instance(
      int[] lo, int[] hi, int[][] vars, int[][] values, boolean[][] eq, int[] w) {

    static Instance random(Random rnd) {
      int n = 2 + rnd.nextInt(3);
      int[] lo = new int[n];
      int[] hi = new int[n];
      for (int i = 0; i < n; i++) {
        lo[i] = rnd.nextInt(2);
        hi[i] = lo[i] + 1 + rnd.nextInt(2);
      }
      int m = 2 + rnd.nextInt(8);
      int[][] vars = new int[m][];
      int[][] values = new int[m][];
      boolean[][] eq = new boolean[m][];
      int[] w = new int[m];
      for (int t = 0; t < m; t++) {
        int k = 1 + rnd.nextInt(3);
        vars[t] = new int[k];
        values[t] = new int[k];
        eq[t] = new boolean[k];
        for (int l = 0; l < k; l++) {
          int v = rnd.nextInt(n);
          vars[t][l] = v;
          values[t][l] = lo[v] + rnd.nextInt(hi[v] - lo[v] + 2) - (rnd.nextInt(5) == 0 ? 1 : 0);
          eq[t][l] = rnd.nextInt(4) != 0;
        }
        w[t] = rnd.nextInt(4);
      }
      return new Instance(lo, hi, vars, values, eq, w);
    }

    IntVar[] variables(Store store) {
      IntVar[] x = new IntVar[lo.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, lo[i], hi[i]);
      }
      return x;
    }

    ConjunctionSum constraint(IntVar[] x, IntVar sum) {
      IntVar[][] tv = new IntVar[vars.length][];
      for (int t = 0; t < vars.length; t++) {
        tv[t] = new IntVar[vars[t].length];
        for (int l = 0; l < vars[t].length; l++) {
          tv[t][l] = x[vars[t][l]];
        }
      }
      return new ConjunctionSum(tv, values, eq, w, sum);
    }

    int total(int[] a) {
      int s = 0;
      for (int t = 0; t < vars.length; t++) {
        boolean all = true;
        for (int l = 0; l < vars[t].length; l++) {
          boolean same = a[vars[t][l]] == values[t][l];
          all &= eq[t][l] == same;
        }
        if (all) {
          s += w[t];
        }
      }
      return s;
    }

    int maxTotal() {
      int s = 0;
      for (int v : w) {
        s += v;
      }
      return s;
    }

    // assignments of x with sum in 0..cap and sum >= the weighted count
    long bruteForce(int cap) {
      int n = lo.length;
      int[] a = lo.clone();
      long count = 0;
      while (true) {
        count += Math.max(0, cap - total(a) + 1);
        int i = 0;
        while (i < n && a[i] == hi[i]) {
          a[i] = lo[i];
          i++;
        }
        if (i == n) {
          return count;
        }
        a[i]++;
      }
    }
  }

  @Test
  void waitingTermsRaiseTheBound() {
    // costs c[a][b] of y1 = a /\ y2 = b: once y1 = 0 the least of row 0 is 2
    Store store = new Store();
    IntVar y1 = new IntVar(store, "y1", 0, 1);
    IntVar y2 = new IntVar(store, "y2", 0, 2);
    IntVar s = new IntVar(store, "s", 0, 20);
    int[][] c = {{3, 2, 5}, {0, 1, 4}};
    int m = 6;
    IntVar[][] tv = new IntVar[m][];
    int[][] values = new int[m][];
    boolean[][] eq = new boolean[m][];
    int[] w = new int[m];
    for (int a = 0; a < 2; a++) {
      for (int b = 0; b < 3; b++) {
        int t = 3 * a + b;
        tv[t] = new IntVar[] {y1, y2};
        values[t] = new int[] {a, b};
        eq[t] = new boolean[] {true, true};
        w[t] = c[a][b];
      }
    }
    store.impose(new ConjunctionSum(tv, values, eq, w, s));
    assertTrue(store.consistency());
    assertEquals(0, s.min());
    store.setLevel(1);
    y1.domain.in(1, y1, 0, 0);
    assertTrue(store.consistency());
    assertEquals(2, s.min());
    // at most 3: y2 = 2 (cost 5) goes
    store.setLevel(2);
    s.domain.inMax(2, s, 3);
    assertTrue(store.consistency());
    assertFalse(y2.domain.contains(2));
    // y2 = 1 as well: the bound 2 is above a maximum of 1 once s is at most 1 from elsewhere
    store.setLevel(3);
    IntVar t = new IntVar(store, "t", 0, 1);
    store.impose(new org.jacop.constraints.XgteqY(t, s));
    assertFalse(store.consistency());
  }

  @Test
  void solutionCountsMatchBruteForce() {
    Random rnd = new Random(7);
    for (int instance = 0; instance < 300; instance++) {
      Instance in = Instance.random(rnd);
      Store store = new Store();
      IntVar[] x = in.variables(store);
      int cap = in.maxTotal() + 1;
      IntVar s = new IntVar(store, "s", 0, cap);
      store.impose(in.constraint(x, s));
      IntVar[] all = new IntVar[x.length + 1];
      System.arraycopy(x, 0, all, 0, x.length);
      all[x.length] = s;
      Search<IntVar> search = new DepthFirstSearch<>();
      SelectChoicePoint<IntVar> select = new SimpleSelect<>(all, null, new IndomainMin<>());
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      search.setPrintInfo(false);
      boolean found = search.labeling(store, select);
      long expected = in.bruteForce(cap);
      long count = found ? search.getSolutionListener().solutionsNo() : 0;
      assertEquals(expected, count, "instance " + instance);
    }
  }

  @Test
  void incrementalBoundMatchesScratchAfterBacktracking() {
    Random rnd = new Random(5);
    int compared = 0;
    for (int instance = 0; instance < 500; instance++) {
      Instance in = Instance.random(rnd);
      Store store = new Store();
      IntVar[] x = in.variables(store);
      IntVar s = new IntVar(store, "s", 0, 1000);
      ConjunctionSum c = in.constraint(x, s);
      store.impose(c);
      if (!store.consistency()) {
        continue;
      }
      for (int step = 0; step < 30; step++) {
        if (store.level > 0 && rnd.nextInt(3) == 0) {
          int back = 1 + rnd.nextInt(store.level);
          for (int k = 0; k < back; k++) {
            store.removeLevel(store.level);
            store.setLevel(store.level - 1);
          }
        } else {
          store.setLevel(store.level + 1);
          IntVar v = x[rnd.nextInt(x.length)];
          int a = v.min() + rnd.nextInt(v.max() - v.min() + 1);
          boolean ok;
          try {
            if (rnd.nextBoolean()) {
              v.domain.in(store.level, v, a, a);
            } else if (!v.singleton()) {
              v.domain.inComplement(store.level, v, a);
            }
            ok = store.consistency();
          } catch (FailException _) {
            ok = false;
          }
          if (!ok) {
            store.removeLevel(store.level);
            store.setLevel(store.level - 1);
            continue;
          }
        }
        assertEquals(c.scratchBound(), s.min(), "instance " + instance + " step " + step);
        compared++;
      }
    }
    assertTrue(compared > 1000, "compared: " + compared);
  }

  @Test
  void reasonsImplyTheirAtoms() {
    Random rnd = new Random(11);
    int checked = 0;
    int failures = 0;
    for (int instance = 0; instance < 1000; instance++) {
      Instance in = Instance.random(rnd);
      Store store = new Store();
      IntVar[] x = in.variables(store);
      IntVar s = new IntVar(store, "s", 0, in.maxTotal() + 1);
      AtomicTrail trail = new AtomicTrail(store);
      ConjunctionSum c = in.constraint(x, s);
      store.impose(c);
      boolean consistent = store.consistency();
      for (int step = 0; consistent && step < 8; step++) {
        store.setLevel(store.level + 1);
        IntVar v = rnd.nextInt(3) == 0 ? s : x[rnd.nextInt(x.length)];
        int a = v == s ? s.min() + rnd.nextInt(2) : v.min() + rnd.nextInt(v.max() - v.min() + 1);
        try {
          switch (v == s ? 0 : rnd.nextInt(3)) {
            case 0 -> v.domain.inMax(store.level, v, a);
            case 1 -> v.domain.inComplement(store.level, v, a);
            default -> v.domain.in(store.level, v, a, a);
          }
          consistent = store.consistency();
        } catch (FailException _) {
          consistent = false;
        }
      }
      ExplanationChecker checker = new ExplanationChecker(trail);
      for (int e = 0; e < trail.size(); e++) {
        if (trail.reason(e) == c) {
          EntryList reason = new EntryList();
          assertTrue(trail.explain(e, reason), "instance " + instance);
          assertNull(checker.checkReason(e, reason), "instance " + instance);
          checked++;
        }
      }
      if (!consistent && store.recentlyFailedConstraint == c) {
        EntryList reason = new EntryList();
        if (c.explainFailure(trail, reason)) {
          assertNull(checker.checkFailure(c, reason), "instance " + instance);
          failures++;
        }
      }
      trail.detach();
    }
    assertTrue(checked > 100, "reasons checked: " + checked);
    assertTrue(failures > 3, "failures checked: " + failures);
  }
}
