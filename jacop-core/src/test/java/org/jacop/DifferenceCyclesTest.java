/*
 * DifferenceCyclesTest.java
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

package org.jacop;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.DifferenceCycles;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;
import org.jacop.lcg.ExplanationMinimality;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

/** Tests of {@link DifferenceCycles}. */
class DifferenceCyclesTest {

  @Test
  @Timeout(10)
  void failsWhenTheLastArcOfANegativeCycleHolds() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 500_000_000);
    IntVar y = new IntVar(store, "y", 0, 500_000_000);
    IntVar z = new IntVar(store, "z", 0, 500_000_000);
    IntVar b1 = new IntVar(store, "b1", 0, 1);
    IntVar b2 = new IntVar(store, "b2", 0, 1);
    IntVar b3 = new IntVar(store, "b3", 0, 1);
    // b1 -> x + 1 <= y, b2 -> y + 1 <= z, b3 -> z + 1 <= x: bounds propagation creeps round it
    store.impose(new XplusClteqZImplied(b1, x, 1, y));
    store.impose(new XplusClteqZImplied(b2, y, 1, z));
    store.impose(new XplusClteqZImplied(b3, z, 1, x));
    DifferenceCycles cycles =
        new DifferenceCycles(
            new IntVar[] {x, y, z},
            new IntVar[] {y, z, x},
            new int[] {-1, -1, -1},
            new IntVar[] {b1, b2, b3},
            new int[] {1, 1, 1});
    assertEquals(3, cycles.conditionalArcs());
    store.impose(cycles);
    assertTrue(store.consistency());

    store.setLevel(1);
    b1.domain.in(1, b1, 1, 1);
    b2.domain.in(1, b2, 1, 1);
    assertTrue(store.consistency());
    store.setLevel(2);
    b3.domain.in(2, b3, 1, 1);
    // fails at once instead of after 10^8 rounds of bounds propagation
    assertFalse(store.consistency());
    assertEquals(1, cycles.cyclesFound());
    store.removeLevel(2);
    store.setLevel(1);
    store.setLevel(2);
    b3.domain.in(2, b3, 0, 0);
    assertTrue(store.consistency());
  }

  @Test
  void dropsArcsThatAreOnNoCycle() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", 0, 10);
    IntVar z = new IntVar(store, "z", 0, 10);
    IntVar b = new IntVar(store, "b", 0, 1);
    // x <= y, b -> y <= z - 1: a chain without cycles
    DifferenceCycles cycles =
        new DifferenceCycles(
            new IntVar[] {x, y},
            new IntVar[] {y, z},
            new int[] {0, -1},
            new IntVar[] {null, b},
            new int[] {1, 1});
    assertEquals(0, cycles.conditionalArcs());
  }

  @Test
  void explainsAFailureByTheLiteralsOfTheCycle() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 100);
    IntVar y = new IntVar(store, "y", 0, 100);
    IntVar z = new IntVar(store, "z", 0, 100);
    IntVar b1 = new IntVar(store, "b1", 0, 1);
    IntVar b2 = new IntVar(store, "b2", 0, 1);
    IntVar b3 = new IntVar(store, "b3", 0, 1);
    AtomicTrail trail = new AtomicTrail(store);
    // y - x <= -2 always; b1 -> z - y <= 0; b2 = 0 -> x - z <= 1; b3 on an arc off the cycle
    DifferenceCycles cycles =
        new DifferenceCycles(
            new IntVar[] {y, z, x, x},
            new IntVar[] {x, y, z, y},
            new int[] {-2, 0, 1, 5},
            new IntVar[] {null, b1, b2, b3},
            new int[] {1, 1, 0, 1});
    store.impose(cycles);
    assertTrue(store.consistency());
    store.setLevel(1);
    b3.domain.inMin(1, b3, 1);
    b1.domain.inMin(1, b1, 1);
    assertTrue(store.consistency());
    store.setLevel(2);
    b2.domain.inMax(2, b2, 0);
    assertFalse(store.consistency());
    EntryList out = new EntryList();
    assertTrue(cycles.explainFailure(trail, out));
    List<String> atoms = new ArrayList<>();
    for (int i = 0; i < out.size(); i++) {
      atoms.add(trail.variable(out.get(i)).id());
    }
    atoms.sort(String::compareTo);
    assertEquals(List.of("b1", "b2"), atoms);
    // the scope holds only the literals, so the explanation checker and the minimality sampler
    // cannot copy the constraint alone and skip it instead of throwing
    ExplanationChecker checker = new ExplanationChecker(trail);
    assertNull(checker.checkFailure(cycles, out));
    assertEquals(1, checker.skipped);
    assertNull(new ExplanationMinimality(trail).minimise(cycles, -1, out));
    trail.detach();
  }

  @Test
  void explainsALiteralWiderThanZeroOneByBothBounds() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 100);
    IntVar y = new IntVar(store, "y", 0, 100);
    IntVar k = new IntVar(store, "k", 0, 2);
    AtomicTrail trail = new AtomicTrail(store);
    // k == 1 -> x - y <= -1 and y - x <= -1, as the arcs of two elements indexed by k
    DifferenceCycles cycles =
        new DifferenceCycles(
            new IntVar[] {x, y},
            new IntVar[] {y, x},
            new int[] {-1, -1},
            new IntVar[] {k, k},
            new int[] {1, 1});
    store.impose(cycles);
    assertTrue(store.consistency());
    store.setLevel(1);
    k.domain.inMin(1, k, 1);
    assertTrue(store.consistency());
    store.setLevel(2);
    k.domain.inMax(2, k, 1);
    assertFalse(store.consistency());
    EntryList out = new EntryList();
    assertTrue(cycles.explainFailure(trail, out));
    // k is now within 0..1, but k >= 1 alone does not fix it to 1: k = 2 is still allowed by it
    Set<Integer> entries = new HashSet<>();
    for (int i = 0; i < out.size(); i++) {
      assertEquals("k", trail.variable(out.get(i)).id());
      entries.add(out.get(i));
    }
    assertEquals(2, entries.size());
    trail.detach();
  }

  @Test
  void failsOnACycleWhoseWeightDependsOnAnOffset() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 100);
    IntVar y = new IntVar(store, "y", 0, 100);
    IntVar d = new IntVar(store, "d", 0, 10);
    AtomicTrail trail = new AtomicTrail(store);
    // y >= x + d, that is x - y <= 0 - d, and y - x <= 3
    DifferenceCycles cycles =
        new DifferenceCycles(
            new IntVar[] {x, y},
            new IntVar[] {y, x},
            new int[] {0, 3},
            new IntVar[] {null, null},
            new int[] {1, 1},
            new IntVar[] {d, null},
            new int[] {1, 0});
    assertEquals(1, cycles.offsetArcs());
    store.impose(cycles);
    assertTrue(store.consistency());
    store.setLevel(1);
    d.domain.inMin(1, d, 3);
    assertTrue(store.consistency());
    store.setLevel(2);
    d.domain.inMin(2, d, 4);
    assertFalse(store.consistency());
    EntryList out = new EntryList();
    assertTrue(cycles.explainFailure(trail, out));
    assertEquals(1, out.size());
    assertEquals("d", trail.variable(out.get(0)).id());
    trail.detach();
    store.removeLevel(2);
    store.setLevel(1);
    assertTrue(store.consistency());
  }

  @Test
  void copiesKeepTheArcsOfVariablesFixedAfterTheConstraintWasBuilt() {
    // LcgFuzzTest seed 7049418: x0 is fixed at the root after the constraint is built, so the
    // explanation checker copies it over x0 = 1; a copy that dropped the arcs of x0 missed the
    // cycle and reported a sound reason as wrong
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", -1, 4);
    IntVar x2 = new IntVar(store, "x2", -1, 3);
    IntVar x3 = new IntVar(store, "x3", 0, 3);
    IntVar b0 = new IntVar(store, "b0", 0, 1);
    IntVar b1 = new IntVar(store, "b1", 0, 1);
    DifferenceCycles cycles =
        new DifferenceCycles(
            new IntVar[] {x3, x0, x2, x0, x3},
            new IntVar[] {x2, x2, x0, x3, x2},
            new int[] {-2, 1, 1, -2, -1},
            new IntVar[] {b1, x2, b0, b0, null},
            new int[] {1, -1, 1, 1, 1},
            new IntVar[] {null, x3, x0, null, x0},
            new int[] {0, -1, 1, 0, -1});
    x0.domain.in(0, x0, 1, 1);
    AtomicTrail trail = new AtomicTrail(store);
    store.impose(cycles);
    assertTrue(store.consistency());
    store.setLevel(1);
    b0.domain.inMin(1, b0, 1);
    assertFalse(store.consistency());
    EntryList out = new EntryList();
    assertTrue(cycles.explainFailure(trail, out));
    ExplanationChecker checker = new ExplanationChecker(trail);
    assertNull(checker.checkFailure(cycles, out));
    assertEquals(0, checker.skipped);
    trail.detach();
  }

  @Test
  void failsExactlyOnNegativeCyclesOfTheArcsThatHold() {
    Random r = new Random(20261106);
    int checks = 0;
    for (int run = 0; run < 300; run++) {
      Store store = new Store();
      int n = 3 + r.nextInt(4);
      IntVar[] v = new IntVar[n];
      for (int i = 0; i < n; i++) {
        v[i] = new IntVar(store, "v" + i, -1000, 1000);
      }
      int nb = 1 + r.nextInt(5);
      IntVar[] lits = new IntVar[nb];
      for (int i = 0; i < nb; i++) {
        lits[i] = new IntVar(store, "b" + i, 0, 1);
      }
      int m = n + r.nextInt(3 * n);
      IntVar[] x = new IntVar[m];
      IntVar[] y = new IntVar[m];
      int[] c = new int[m];
      IntVar[] b = new IntVar[m];
      int[] val = new int[m];
      int[] t = new int[m];
      int[] h = new int[m];
      for (int k = 0; k < m; k++) {
        h[k] = r.nextInt(n);
        t[k] = (h[k] + 1 + r.nextInt(n - 1)) % n;
        x[k] = v[h[k]];
        y[k] = v[t[k]];
        c[k] = r.nextInt(9) - 3;
        if (r.nextInt(3) > 0) {
          b[k] = lits[r.nextInt(nb)];
          val[k] = r.nextInt(2);
        }
      }
      if (negativeCycle(n, t, h, c, b, val)) {
        // the arcs that always hold already have one
        continue;
      }
      DifferenceCycles cycles = new DifferenceCycles(x, y, c, b, val);
      store.impose(cycles);
      assertTrue(store.consistency());
      // random dives with backtracking
      for (int step = 0; step < 30; step++) {
        List<IntVar> open = new ArrayList<>();
        for (IntVar l : lits) {
          if (!l.singleton()) {
            open.add(l);
          }
        }
        if (open.isEmpty() || r.nextInt(5) == 0) {
          if (store.level > 0) {
            store.removeLevel(store.level);
            store.setLevel(store.level - 1);
          }
          continue;
        }
        IntVar l = open.get(r.nextInt(open.size()));
        store.setLevel(store.level + 1);
        int value = r.nextInt(2);
        l.domain.in(store.level, l, value, value);
        boolean expected = !negativeCycle(n, t, h, c, b, val);
        assertEquals(expected, store.consistency(), "run " + run + " step " + step);
        checks++;
        if (!expected) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
      }
    }
    assertTrue(checks > 1000, "checks " + checks);
  }

  // Bellman-Ford over the arcs that hold now
  private static boolean negativeCycle(int n, int[] t, int[] h, int[] c, IntVar[] b, int[] val) {
    long[] d = new long[n];
    for (int round = 0; round <= n; round++) {
      boolean changed = false;
      for (int k = 0; k < t.length; k++) {
        boolean holds = b[k] == null || (b[k].singleton() && b[k].value() == val[k]);
        if (holds && d[t[k]] + c[k] < d[h[k]]) {
          d[h[k]] = d[t[k]] + c[k];
          changed = true;
        }
      }
      if (!changed) {
        return false;
      }
    }
    return true;
  }
}
