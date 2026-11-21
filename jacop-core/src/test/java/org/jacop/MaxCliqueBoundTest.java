/*
 * MaxCliqueBoundTest.java
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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.MaxCliqueBound;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link MaxCliqueBound}: the maximum clique it finds against brute force, its bound at
 * the root, and its reasons for lazy clause generation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class MaxCliqueBoundTest {

  // a random conflict graph: conflicts[i] lists the vertices that cannot be 1 together with i
  private static int[][] randomConflicts(Random rnd, int n) {
    double density = 0.2 + 0.6 * rnd.nextDouble();
    List<List<Integer>> lists = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      lists.add(new ArrayList<>());
    }
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (rnd.nextDouble() < density) {
          lists.get(i).add(j);
          if (rnd.nextBoolean()) {
            lists.get(j).add(i);
          }
        }
      }
    }
    int[][] out = new int[n][];
    for (int i = 0; i < n; i++) {
      out[i] = lists.get(i).stream().mapToInt(Integer::intValue).toArray();
    }
    return out;
  }

  private static boolean[][] matrix(int[][] conflicts) {
    int n = conflicts.length;
    boolean[][] c = new boolean[n][n];
    for (int i = 0; i < n; i++) {
      for (int j : conflicts[i]) {
        c[i][j] = true;
        c[j][i] = true;
      }
    }
    return c;
  }

  // the largest set of vertices no two of which are in conflict, by enumeration
  private static int bruteForce(int[][] conflicts) {
    int n = conflicts.length;
    boolean[][] c = matrix(conflicts);
    int best = 0;
    for (int mask = 0; mask < 1 << n; mask++) {
      int size = Integer.bitCount(mask);
      if (size <= best) {
        continue;
      }
      boolean ok = true;
      for (int i = 0; i < n && ok; i++) {
        for (int j = i + 1; j < n && ok; j++) {
          ok = (mask >> i & 1) == 0 || (mask >> j & 1) == 0 || !c[i][j];
        }
      }
      if (ok) {
        best = size;
      }
    }
    return best;
  }

  @Test
  void maximumAgainstBruteForce() {
    Random rnd = new Random(7);
    for (int instance = 0; instance < 300; instance++) {
      int n = 1 + rnd.nextInt(12);
      int[][] conflicts = randomConflicts(rnd, n);
      int expected = bruteForce(conflicts);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
      }
      IntVar s = new IntVar(store, "s", 0, n);
      store.impose(new SumInt(x, "==", s));
      MaxCliqueBound c = new MaxCliqueBound(x, conflicts, s);
      store.impose(c);
      assertTrue(store.consistency());
      assertTrue(s.max() >= expected, "root bound, instance " + instance);
      IntVar cost = new IntVar(store, "cost", -n, 0);
      store.impose(new XplusYeqC(s, cost, 0));
      Search<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      SelectChoicePoint<IntVar> select = new SimpleSelect<>(x, null, new IndomainMax<>());
      assertTrue(search.labeling(store, select, cost));
      assertEquals(-expected, cost.value(), "instance " + instance);
    }
  }

  @Test
  void reasonsImplyTheirAtoms() {
    Random rnd = new Random(11);
    int checked = 0;
    int failures = 0;
    for (int instance = 0; instance < 1000; instance++) {
      int n = 2 + rnd.nextInt(10);
      int[][] conflicts = randomConflicts(rnd, n);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
      }
      IntVar s = new IntVar(store, "s", 0, n);
      AtomicTrail trail = new AtomicTrail(store);
      MaxCliqueBound c = new MaxCliqueBound(x, conflicts, s);
      store.impose(c);
      boolean consistent = store.consistency();
      for (int step = 0; consistent && step < 8; step++) {
        store.setLevel(store.level + 1);
        try {
          if (rnd.nextInt(3) == 0) {
            s.domain.inMin(store.level, s, Math.min(s.max(), s.min() + 1 + rnd.nextInt(2)));
          } else {
            IntVar v = x[rnd.nextInt(n)];
            int a = rnd.nextInt(2);
            v.domain.in(store.level, v, a, a);
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

  // the largest set of pairwise compatible vertices, by a plain branch and bound over bit masks
  private static int reference(long[] compatible, long candidates, int size, int best) {
    if (candidates == 0) {
      return Math.max(size, best);
    }
    if (size + Long.bitCount(candidates) <= best) {
      return best;
    }
    int v = Long.numberOfTrailingZeros(candidates);
    best = reference(compatible, candidates & compatible[v], size + 1, best);
    return reference(compatible, candidates & ~(1L << v), size, best);
  }

  private static int reference(int[][] conflicts) {
    int n = conflicts.length;
    boolean[][] c = matrix(conflicts);
    long[] compatible = new long[n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i != j && !c[i][j]) {
          compatible[i] |= 1L << j;
        }
      }
    }
    return reference(compatible, n == 64 ? -1L : (1L << n) - 1, 0, 0);
  }

  // larger graphs, where the vertices beyond the incumbent are covered by re-coloring and MaxSAT
  // reasoning, and the one vertex left uncovered is set to 1
  @Test
  void largerGraphsAgainstReference() {
    Random rnd = new Random(23);
    for (int instance = 0; instance < 150; instance++) {
      int n = 15 + rnd.nextInt(26);
      int[][] conflicts = randomConflicts(rnd, n);
      int expected = reference(conflicts);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
      }
      IntVar s = new IntVar(store, "s", 0, n);
      store.impose(new SumInt(x, "==", s));
      store.impose(new MaxCliqueBound(x, conflicts, s));
      IntVar cost = new IntVar(store, "cost", -n, 0);
      store.impose(new XplusYeqC(s, cost, 0));
      Search<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      SelectChoicePoint<IntVar> select = new SimpleSelect<>(x, null, new IndomainMax<>());
      assertTrue(search.labeling(store, select, cost));
      assertEquals(-expected, cost.value(), "instance " + instance);
    }
  }

  // reasons on larger graphs with a raised lower bound on the sum, so that the bound covers
  // vertices beyond it and sets the last uncovered vertex to 1
  @Test
  void reasonsOfCoveredBounds() {
    Random rnd = new Random(31);
    int forced = 0;
    int failures = 0;
    int checked = 0;
    for (int instance = 0; instance < 400; instance++) {
      int n = 12 + rnd.nextInt(14);
      int[][] conflicts = randomConflicts(rnd, n);
      int expected = reference(conflicts);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
      }
      IntVar s = new IntVar(store, "s", 0, n);
      AtomicTrail trail = new AtomicTrail(store);
      MaxCliqueBound c = new MaxCliqueBound(x, conflicts, s);
      store.impose(c);
      boolean consistent = store.consistency();
      for (int step = 0; consistent && step < 10; step++) {
        store.setLevel(store.level + 1);
        try {
          if (step == 0 || rnd.nextInt(3) == 0) {
            int target = Math.max(s.min(), expected - 1 + rnd.nextInt(3));
            s.domain.inMin(store.level, s, Math.min(s.max(), target));
          } else {
            IntVar v = x[rnd.nextInt(n)];
            int a = rnd.nextInt(4) == 0 ? 1 : 0;
            v.domain.in(store.level, v, a, a);
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
          if (trail.kind(e) == AtomicTrail.GE && trail.variable(e) != s) {
            forced++;
          }
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
    assertTrue(forced > 10, "forced vertices checked: " + forced);
    assertTrue(failures > 10, "failures checked: " + failures);
  }
}
