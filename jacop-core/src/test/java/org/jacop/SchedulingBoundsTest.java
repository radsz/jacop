/*
 * SchedulingBoundsTest.java
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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Arrays;
import java.util.Random;
import org.jacop.constraints.LateCount;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.WeightedCompletion;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeUnary;
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
import org.jacop.search.SmallestMin;
import org.junit.jupiter.api.Test;

/**
 * Checks of the Eastman, Even and Isaacs bound ({@link WeightedCompletion} with a capacity above 1)
 * and of {@link LateCount}: root bounds against closed forms and exact optima of the relaxations,
 * and optima of random P|r_j|sum w_j C_j and 1|r_j|sum U_j problems against the cumulative or
 * disjunctive decomposition alone. Solution sets of the constraints alone are compared with a
 * brute-force enumeration in {@link GlobalConstraintBruteForceTest}.
 */
class SchedulingBoundsTest {

  // -Dschedulingbounds.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("schedulingbounds.instances", 300);

  @Test
  void rejectsBadArguments() {
    Store store = new Store();
    IntVar[] s = {new IntVar(store, 0, 5)};
    IntVar c = new IntVar(store, 0, 50);
    int[] one = {1};
    assertThatThrownBy(() -> new WeightedCompletion(s, one, one, one, 0, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new WeightedCompletion(s, one, new int[] {-1}, one, 2, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new WeightedCompletion(s, one, new int[] {1, 1}, one, 2, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new LateCount(s, new int[] {-1}, one, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new LateCount(s, one, new int[] {1, 2}, c))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void eastmanEvenIsaacsOnTwoMachines() {
    // four unit tasks of weight 1 on two machines from 0: the optimum and the bound are 1+1+2+2
    Store store = new Store();
    IntVar[] s = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 10);
    }
    IntVar cost = new IntVar(store, "cost", 0, 100);
    int[] one = {1, 1, 1, 1};
    store.impose(new WeightedCompletion(s, one, one, one, 2, cost));
    assertTrue(store.consistency());
    // LB1 = 1 + 2 + 3 + 4 = 10, 10 / 2 + 1 / 4 * 4 = 6
    assertEquals(6, cost.min());
    store.setLevel(1);
    cost.domain.in(1, cost, 6, 6);
    assertTrue(store.consistency());
    // the other three have the bound 2.25 + 1.5 = 3.75, so s0 + 1 <= 6 - 3.75
    assertEquals(1, s[0].max());
  }

  @Test
  void fixedTasksOverloadFails() {
    Store store = new Store();
    IntVar[] s = {new IntVar(store, 0, 0), new IntVar(store, 1, 1), new IntVar(store, 0, 9)};
    IntVar cost = new IntVar(store, 0, 1000);
    store.impose(
        new WeightedCompletion(
            s, new int[] {2, 2, 1}, new int[] {1, 1, 1}, new int[] {1, 1, 1}, 2, cost));
    assertTrue(store.consistency());
    store.setLevel(1);
    s[2].domain.in(1, s[2], 1, 1);
    assertFalse(store.consistency());
  }

  /**
   * Without release dates and with unit uses the bound is LB1 / m + (m - 1) / (2m) * sum w * p, LB1
   * the single machine bound of Smith's rule; with releases it never exceeds the optimum.
   */
  @Test
  void parallelBoundMatchesClosedFormAndOptimum() {
    Random random = new Random(11);
    for (int t = 0; t < INSTANCES; t++) {
      int n = 2 + random.nextInt(5);
      int m = 2 + random.nextInt(2);
      int[] p = new int[n];
      int[] w = new int[n];
      int[] r = new int[n];
      int[] use = new int[n];
      boolean releases = random.nextBoolean();
      boolean demands = releases && random.nextBoolean();
      for (int i = 0; i < n; i++) {
        p[i] = 1 + random.nextInt(4);
        w[i] = random.nextInt(5);
        r[i] = releases ? random.nextInt(4) : 0;
        use[i] = demands ? 1 + random.nextInt(m) : 1;
      }
      String what =
          "p="
              + Arrays.toString(p)
              + " w="
              + Arrays.toString(w)
              + " r="
              + Arrays.toString(r)
              + " use="
              + Arrays.toString(use)
              + " m="
              + m;
      long root = parallelRoot(p, w, r, use, m);
      int with = parallelOptimum(p, w, r, use, m, true);
      int without = parallelOptimum(p, w, r, use, m, false);
      assertEquals(without, with, what);
      assertTrue(root <= with, what + " root " + root + " optimum " + with);
      if (!releases) {
        assertTrue(root >= eastmanEvenIsaacs(p, w, m), what);
      }
    }
  }

  // ceil(LB1 / m + (m - 1) / (2m) * sum w * p), exactly
  private static long eastmanEvenIsaacs(int[] p, int[] w, int m) {
    Integer[] order = new Integer[p.length];
    for (int i = 0; i < p.length; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (a, b) -> Long.compare((long) w[b] * p[a], (long) w[a] * p[b]));
    long time = 0;
    long lb1 = 0;
    long wp = 0;
    for (int i : order) {
      time += p[i];
      lb1 += (long) w[i] * time;
      wp += (long) w[i] * p[i];
    }
    long numerator = 2 * lb1 + (m - 1) * wp;
    return Math.floorDiv(numerator + 2L * m - 1, 2L * m);
  }

  private static long parallelRoot(int[] p, int[] w, int[] r, int[] use, int m) {
    Store store = new Store();
    int n = p.length;
    IntVar[] s = new IntVar[n];
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, r[i], 40);
    }
    IntVar cost = new IntVar(store, 0, 100000);
    store.impose(new WeightedCompletion(s, p, use, w, m, cost));
    assertTrue(store.consistency());
    return cost.min();
  }

  private static int parallelOptimum(int[] p, int[] w, int[] r, int[] use, int m, boolean global) {
    Store store = new Store();
    int n = p.length;
    IntVar[] s = new IntVar[n];
    IntVar[] dv = new IntVar[n];
    IntVar[] rv = new IntVar[n];
    int horizon = 4 + Arrays.stream(p).sum();
    IntVar[] terms = new IntVar[n + 1];
    int[] coefficients = new int[n + 1];
    int constant = 0;
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, r[i], horizon);
      dv[i] = new IntVar(store, p[i], p[i]);
      rv[i] = new IntVar(store, use[i], use[i]);
      terms[i] = s[i];
      coefficients[i] = w[i];
      constant += w[i] * p[i];
    }
    IntVar cost = new IntVar(store, "cost", 0, 100000);
    terms[n] = cost;
    coefficients[n] = -1;
    store.impose(new LinearInt(terms, coefficients, "==", -constant));
    store.impose(new Cumulative(s, dv, rv, new IntVar(store, m, m)));
    if (global) {
      store.impose(new WeightedCompletion(s, p, use, w, m, cost));
    }
    return minimize(store, s, cost);
  }

  private static int minimize(Store store, IntVar[] s, IntVar cost) {
    Search<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(s, new SmallestMin<>(), new IndomainMin<>());
    search.setPrintInfo(false);
    assertTrue(search.labeling(store, select, cost));
    return cost.value();
  }

  /** Without release dates the root bound is the optimum of 1||sum U_j (Moore and Hodgson). */
  @Test
  void lateCountRootIsMooreHodgson() {
    Random random = new Random(12);
    for (int t = 0; t < INSTANCES * 3; t++) {
      int n = 1 + random.nextInt(8);
      int[] p = new int[n];
      int[] due = new int[n];
      for (int i = 0; i < n; i++) {
        p[i] = random.nextInt(5);
        due[i] = random.nextInt(14);
      }
      Store store = new Store();
      IntVar[] s = new IntVar[n];
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, 0, 40);
      }
      IntVar late = new IntVar(store, 0, n);
      store.impose(new LateCount(s, p, due, late));
      assertTrue(store.consistency());
      assertEquals(
          minLate(p, due), late.min(), "p=" + Arrays.toString(p) + " due=" + Arrays.toString(due));
    }
  }

  // the fewest late jobs on one machine from 0: the largest subset that meets its due dates by EDD
  private static int minLate(int[] p, int[] due) {
    int n = p.length;
    Integer[] order = new Integer[n];
    for (int i = 0; i < n; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (a, b) -> Integer.compare(due[a], due[b]));
    int best = n;
    for (int mask = 0; mask < 1 << n; mask++) {
      long time = 0;
      boolean ok = true;
      for (int i : order) {
        if ((mask >> i & 1) != 0) {
          time += p[i];
          ok &= time <= due[i];
        }
      }
      if (ok) {
        best = Math.min(best, n - Integer.bitCount(mask));
      }
    }
    return best;
  }

  /** Optima of random 1|r_j|sum U_j with and without the constraint. */
  @Test
  void lateCountOptimaMatchDecomposition() {
    Random random = new Random(13);
    for (int t = 0; t < INSTANCES; t++) {
      int n = 2 + random.nextInt(6);
      int[] p = new int[n];
      int[] r = new int[n];
      int[] due = new int[n];
      for (int i = 0; i < n; i++) {
        p[i] = random.nextInt(5);
        r[i] = random.nextInt(8);
        due[i] = r[i] + random.nextInt(10);
      }
      String what =
          "p=" + Arrays.toString(p) + " r=" + Arrays.toString(r) + " due=" + Arrays.toString(due);
      int optimum = lateOptimum(p, r, due, 0);
      assertEquals(optimum, lateOptimum(p, r, due, 1), what);
      // the horizon leaves room for the late tasks, so the dominance rule keeps an optimum
      assertEquals(optimum, lateOptimum(p, r, due, 2), what + " with dominance");
    }
  }

  // global: 0 the decomposition only, 1 with LateCount, 2 with LateCount and its dominance rule
  private static int lateOptimum(int[] p, int[] r, int[] due, int global) {
    Store store = new Store();
    int n = p.length;
    int horizon = 8 + Arrays.stream(p).sum();
    IntVar[] s = new IntVar[n];
    IntVar[] dv = new IntVar[n];
    IntVar[] one = new IntVar[n];
    IntVar[] b = new IntVar[n];
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, r[i], horizon);
      dv[i] = new IntVar(store, p[i], p[i]);
      one[i] = new IntVar(store, 1, 1);
      b[i] = new IntVar(store, 0, 1);
      store.impose(new Reified(new XgtC(s[i], due[i] - p[i]), b[i]));
    }
    IntVar late = new IntVar(store, "late", 0, n);
    store.impose(new SumInt(b, "==", late));
    store.impose(new CumulativeUnary(s, dv, one, new IntVar(store, 1, 1)));
    if (global > 0) {
      store.impose(new LateCount(s, p, due, late, global == 2));
    }
    return minimize(store, s, late);
  }

  /**
   * Random dives on LateCount alone, with release dates, zero durations and the dominance rule:
   * every reason it gives (the count, the dominance pairs, fixed overlaps, failures) must imply its
   * atom with the domains before the dive.
   */
  @Test
  void lateCountReasonsImplyTheirAtoms() {
    Random rnd = new Random(31);
    int checked = 0;
    int failures = 0;
    for (int instance = 0; instance < 400; instance++) {
      Store store = new Store();
      int n = 3 + rnd.nextInt(5);
      IntVar[] s = new IntVar[n];
      int[] d = new int[n];
      int[] due = new int[n];
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i, rnd.nextInt(5), 14);
        if (rnd.nextInt(4) == 0) {
          s[i].domain.inComplement(0, s[i], s[i].min() + 1 + rnd.nextInt(4));
        }
        d[i] = rnd.nextInt(6) == 0 ? 0 : 1 + rnd.nextInt(4);
        due[i] = s[i].min() + d[i] + rnd.nextInt(6);
      }
      IntVar late = new IntVar(store, "late", 0, n);
      AtomicTrail trail = new AtomicTrail(store);
      LateCount lc = new LateCount(s, d, due, late, rnd.nextBoolean());
      store.impose(lc);
      boolean consistent = store.consistency();
      for (int step = 0; consistent && step < 10; step++) {
        store.setLevel(store.level + 1);
        IntVar x = rnd.nextInt(3) == 0 ? late : s[rnd.nextInt(n)];
        int v = x.min() + rnd.nextInt(x.max() - x.min() + 1);
        try {
          switch (rnd.nextInt(4)) {
            case 0 -> x.domain.inMin(store.level, x, v);
            case 1 -> x.domain.inMax(store.level, x, v);
            case 2 -> x.domain.inComplement(store.level, x, v);
            default -> x.domain.in(store.level, x, v, v);
          }
          consistent = store.consistency();
        } catch (FailException _) {
          consistent = false;
        }
      }
      ExplanationChecker checker = new ExplanationChecker(trail);
      for (int e = 0; e < trail.size(); e++) {
        EntryList reason = new EntryList();
        if (trail.reason(e) == lc && lc.explain(trail, e, reason)) {
          assertNull(checker.checkReason(e, reason), "instance " + instance);
          checked++;
        }
      }
      EntryList reason = new EntryList();
      if (!consistent && lc.explainFailure(trail, reason)) {
        assertNull(checker.checkFailure(lc, reason), "failure, instance " + instance);
        failures++;
      }
      trail.detach();
    }
    assertTrue(checked > 300, "reasons checked: " + checked);
    assertTrue(failures > 20, "failures checked: " + failures);
  }
}
