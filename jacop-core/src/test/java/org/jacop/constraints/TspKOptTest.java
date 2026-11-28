/*
 * TspKOptTest.java
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

package org.jacop.constraints;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.junit.jupiter.api.Test;

/** Tests of {@link TspKOpt}: its rules keep the optimum, and its explanations hold. */
class TspKOptTest {

  // points on a line: the optimal tour goes out and back
  private static long[][] line(int... p) {
    int n = p.length;
    long[][] d = new long[n][n];
    for (int v = 0; v < n; v++) {
      for (int w = 0; w < n; w++) {
        d[v][w] = Math.abs(p[v] - p[w]);
      }
    }
    return d;
  }

  private static IntVar[] successors(Store store, int n) {
    IntVar[] x = new IntVar[n];
    for (int v = 0; v < n; v++) {
      x[v] = new IntVar(store, "x" + v, 0, n - 1);
      x[v].domain.inComplement(0, x[v], v);
    }
    return x;
  }

  @Test
  void twoOptRemovesTheCrossingArc() {
    // 0, 1, 2, 3 on a line at 0, 1, 2, 3; with 0 -> 2 fixed, 1 -> 3 crosses it:
    // d(0,1) + d(2,3) = 2 < d(0,2) + d(1,3) = 4
    Store store = new Store();
    IntVar[] x = successors(store, 4);
    AtomicTrail trail = new AtomicTrail(store);
    TspKOpt c = new TspKOpt(x, 0, line(0, 1, 2, 3));
    store.impose(c);
    assertTrue(store.consistency());
    store.setLevel(1);
    x[0].domain.in(1, x[0], 2, 2);
    assertTrue(store.consistency());
    assertFalse(x[1].domain.contains(3));
    int entry = lastEntry(trail, x[1]);
    EntryList out = new EntryList();
    assertTrue(c.explain(trail, entry, out));
    assertNull(new ExplanationChecker(trail).checkReason(entry, out));
    trail.detach();
  }

  @Test
  void failsOnAPathThatAMoveShortens() {
    // the path 0 -> 3 -> 1 -> 2 -> 4 at 0, 10, 20, 1, 30 visits 3 (at 1) out of order: moving it
    // next to 0 is shorter
    Store store = new Store();
    IntVar[] x = successors(store, 6);
    AtomicTrail trail = new AtomicTrail(store);
    long[][] d = line(0, 10, 20, 1, 30, 15);
    TspKOpt c = new TspKOpt(x, 0, d);
    store.impose(c);
    assertTrue(store.consistency());
    store.setLevel(1);
    boolean ok = true;
    int[][] arcs = {{0, 1}, {1, 3}, {3, 2}, {2, 4}};
    try {
      for (int[] a : arcs) {
        x[a[0]].domain.in(1, x[a[0]], a[1], a[1]);
      }
      ok = store.consistency();
    } catch (org.jacop.core.FailException e) {
      ok = false;
    }
    assertFalse(ok);
    EntryList out = new EntryList();
    if (c.explainFailure(trail, out)) {
      assertNull(new ExplanationChecker(trail).checkFailure(c, out));
    }
    trail.detach();
  }

  @Test
  void rejectsAsymmetricLengths() {
    Store store = new Store();
    IntVar[] x = successors(store, 4);
    long[][] d = line(0, 1, 2, 3);
    d[0][1] = 5;
    assertThrows(IllegalArgumentException.class, () -> new TspKOpt(x, 0, d));
  }

  @Test
  void randomToursKeepTheOptimum() {
    Random random = new Random(11);
    long nodesWith = 0;
    long nodesWithout = 0;
    for (int trial = 0; trial < 150; trial++) {
      int n = 5 + random.nextInt(4);
      long[][] d = randomLengths(random, n);
      long[] with = solve(d, true);
      long[] without = solve(d, false);
      assertEquals(without[0], with[0], "optimum of trial " + trial);
      nodesWith += with[1];
      nodesWithout += without[1];
    }
    assertTrue(nodesWith < nodesWithout, nodesWith + " nodes with, " + nodesWithout + " without");
  }

  @Test
  void randomToursKeepEveryOptimalTour() {
    Random random = new Random(13);
    for (int trial = 0; trial < 60; trial++) {
      int n = 5 + random.nextInt(3);
      long[][] d = randomLengths(random, n);
      long optimum = solve(d, false)[0];
      assertEquals(countTours(d, optimum, false), countTours(d, optimum, true), "trial " + trial);
    }
  }

  @Test
  void randomDivesHaveSoundExplanations() {
    Random random = new Random(3);
    int explained = 0;
    for (int trial = 0; trial < 300; trial++) {
      int n = 4 + random.nextInt(6);
      long[][] d = randomLengths(random, n);
      Store store = new Store();
      IntVar[] x = successors(store, n);
      AtomicTrail trail = new AtomicTrail(store);
      ExplanationChecker checker = new ExplanationChecker(trail);
      TspKOpt c = new TspKOpt(x, 0, d);
      store.impose(new Circuit(x, 0));
      store.impose(c);
      boolean ok = store.consistency();
      int level = 0;
      while (ok) {
        List<IntVar> open = new ArrayList<>();
        for (IntVar v : x) {
          if (!v.singleton()) {
            open.add(v);
          }
        }
        if (open.isEmpty()) {
          break;
        }
        store.setLevel(++level);
        IntVar v = open.get(random.nextInt(open.size()));
        int[] values = v.dom().toIntArray();
        int value = values[random.nextInt(values.length)];
        int before = trail.size();
        try {
          if (random.nextInt(3) == 0) {
            v.domain.inComplement(level, v, value);
          } else {
            v.domain.in(level, v, value, value);
          }
          ok = store.consistency();
        } catch (org.jacop.core.FailException e) {
          ok = false;
        }
        for (int entry = before; entry < trail.size(); entry++) {
          if (trail.reason(entry) == c) {
            EntryList out = new EntryList();
            assertTrue(c.explain(trail, entry, out), "no reason for entry " + entry);
            assertNull(checker.checkReason(entry, out));
            explained++;
          }
        }
        if (!ok && store.currentConstraint == c) {
          EntryList out = new EntryList();
          assertTrue(c.explainFailure(trail, out));
          assertNull(checker.checkFailure(c, out));
          explained++;
        }
      }
      trail.detach();
    }
    assertTrue(explained > 100, explained + " explanations checked");
  }

  private static long[][] randomLengths(Random random, int n) {
    long[][] d = new long[n][n];
    for (int v = 0; v < n; v++) {
      for (int w = v + 1; w < n; w++) {
        d[v][w] = 1 + random.nextInt(20);
        d[w][v] = d[v][w];
      }
    }
    return d;
  }

  // the optimal tour length and the number of nodes of a depth-first branch and bound
  private static long[] solve(long[][] d, boolean kOpt) {
    int n = d.length;
    Store store = new Store();
    IntVar[] x = successors(store, n);
    IntVar[] cost = new IntVar[n];
    for (int v = 0; v < n; v++) {
      int[] row = new int[n];
      for (int w = 0; w < n; w++) {
        row[w] = (int) d[v][w];
      }
      cost[v] = new IntVar(store, "c" + v, 0, 1000);
      store.impose(new ElementInteger(x[v], row, cost[v], -1));
    }
    IntVar obj = new IntVar(store, "obj", 0, 100_000);
    store.impose(new Circuit(x, 0));
    store.impose(new SumInt(cost, "==", obj));
    if (kOpt) {
      store.impose(new TspKOpt(x, 0, d));
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select = new InputOrderSelect<>(store, x, new IndomainMin<>());
    search.setPrintInfo(false);
    assertTrue(search.labeling(store, select, obj));
    return new long[] {search.getCostValue(), search.getNodes()};
  }

  // the number of tours of the given length
  private static int countTours(long[][] d, long length, boolean kOpt) {
    int n = d.length;
    Store store = new Store();
    IntVar[] x = successors(store, n);
    IntVar[] cost = new IntVar[n];
    for (int v = 0; v < n; v++) {
      int[] row = new int[n];
      for (int w = 0; w < n; w++) {
        row[w] = (int) d[v][w];
      }
      cost[v] = new IntVar(store, "c" + v, 0, 1000);
      store.impose(new ElementInteger(x[v], row, cost[v], -1));
    }
    store.impose(new Circuit(x, 0));
    store.impose(new SumInt(cost, "==", new IntVar(store, "obj", (int) length, (int) length)));
    if (kOpt) {
      store.impose(new TspKOpt(x, 0, d));
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select = new InputOrderSelect<>(store, x, new IndomainMin<>());
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, select);
    return search.getSolutionListener().solutionsNo();
  }

  private static int lastEntry(AtomicTrail trail, IntVar v) {
    for (int entry = trail.size() - 1; entry >= 0; entry--) {
      if (trail.variable(entry) == v) {
        return entry;
      }
    }
    throw new AssertionError("no entry of " + v.id());
  }
}
