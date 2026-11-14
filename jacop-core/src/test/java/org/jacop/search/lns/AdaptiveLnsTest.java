/*
 * AdaptiveLnsTest.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.search.lns;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** Tests of the neighbourhoods of {@link AdaptiveLns}. */
class AdaptiveLnsTest {

  private static final int N = 12;

  private final Store store = new Store();
  private final IntVar[] x = new IntVar[N];
  private final IntVar cost;

  AdaptiveLnsTest() {
    for (int i = 0; i < N; i++) {
      x[i] = new IntVar(store, "x" + i, 0, N - 1);
    }
    store.impose(new Alldifferent(x));
    // x[i] < x[i + 1] for the first half chains them in the graph
    for (int i = 0; i + 1 < N / 2; i++) {
      store.impose(new LinearInt(new IntVar[] {x[i], x[i + 1]}, new int[] {1, -1}, "<", 0));
    }
    cost = new IntVar(store, "cost", 0, 1000);
    IntVar[] terms = new IntVar[N + 1];
    int[] w = new int[N + 1];
    for (int i = 0; i < N; i++) {
      terms[i] = x[i];
      w[i] = i + 1;
    }
    terms[N] = cost;
    w[N] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    assertTrue(store.consistency());
  }

  /** Records the solution x[i] = i in the neighbourhoods and puts the store back at the root. */
  private AdaptiveLns withSolution(long seed) {
    AdaptiveLns lns = new AdaptiveLns(store, x, cost, new Random(seed));
    int level = store.level;
    store.setLevel(level + 1);
    for (int i = 0; i < N; i++) {
      x[i].domain.inValue(store.level, x[i], i);
    }
    assertTrue(store.consistency());
    lns.solution();
    store.removeLevel(level + 1);
    store.setLevel(level);
    return lns;
  }

  @Test
  void neighbourhoodsFixValidVariablesAndLeaveTheStore() {
    AdaptiveLns lns = withSolution(1);
    assertTrue(lns.ready());
    int level = store.level;
    for (int k = 0; k < 400; k++) {
      int[] fixed = lns.neighbourhood();
      assertEquals(level, store.level);
      Set<Integer> seen = new HashSet<>();
      for (int i : fixed) {
        assertTrue(seen.add(i), "fixed twice: " + i);
        assertEquals(i, lns.value(i));
        assertTrue(x[i].domain.contains(lns.value(i)));
      }
      assertTrue(fixed.length < N, "a neighbourhood fixes everything");
      for (IntVar v : x) {
        assertEquals(N, v.getSize() + (v.min() > 0 ? v.min() : 0) + (N - 1 - v.max()));
      }
      lns.outcome(k % 3 == 0 ? AdaptiveLns.Outcome.IMPROVED : AdaptiveLns.Outcome.LIMIT);
    }
    // every kind the model allows was used, the objective's terms included
    assertTrue(lns.usable(AdaptiveLns.Kind.OBJECTIVE));
    assertTrue(lns.usable(AdaptiveLns.Kind.CONSTRAINTS));
    assertFalse(lns.usable(AdaptiveLns.Kind.SCHEDULING));
    assertFalse(lns.usable(AdaptiveLns.Kind.PACKING));
    for (AdaptiveLns.Kind kind : AdaptiveLns.Kind.values()) {
      assertEquals(
          lns.usable(kind),
          !lns.statistics().contains(kind + " 0/"),
          kind + " " + lns.statistics());
    }
    assertEquals(400, lns.runs());
  }

  @Test
  void blocksRelaxWholeGroupsHeavyFirst() {
    AdaptiveLns lns = withSolution(3);
    assertFalse(lns.usable(AdaptiveLns.Kind.BLOCKS));
    // four groups of three; the last one weighs 30 times each other one
    IntVar[][] groups = new IntVar[4][3];
    for (int i = 0; i < N; i++) {
      groups[i / 3][i % 3] = x[i];
    }
    lns.addGroups(groups, new double[] {0.1, 0.1, 0.1, 3});
    assertTrue(lns.usable(AdaptiveLns.Kind.BLOCKS));
    int lastFree = 0;
    int runs = 200;
    for (int k = 0; k < runs; k++) {
      boolean[] free = relaxed(lns.neighbourhood(AdaptiveLns.Kind.BLOCKS), N);
      for (int g = 0; g < 4; g++) {
        // a group is relaxed as a whole or not at all
        assertEquals(free[3 * g], free[3 * g + 1]);
        assertEquals(free[3 * g], free[3 * g + 2]);
      }
      if (free[N - 1]) {
        lastFree++;
      }
      lns.outcome(AdaptiveLns.Outcome.LIMIT);
    }
    assertTrue(lastFree > runs * 3 / 4, "heavy group relaxed in " + lastFree + " runs");
  }

  @Test
  void neighbourhoodsGrowWhenRunsFinish() {
    AdaptiveLns lns = withSolution(2);
    int first = 0;
    for (int k = 0; k < 10; k++) {
      first += lns.neighbourhood().length;
      lns.outcome(AdaptiveLns.Outcome.LIMIT);
    }
    for (int k = 0; k < 200; k++) {
      lns.neighbourhood();
      lns.outcome(AdaptiveLns.Outcome.EXHAUSTED);
    }
    int last = 0;
    for (int k = 0; k < 10; k++) {
      last += lns.neighbourhood().length;
      lns.outcome(AdaptiveLns.Outcome.EXHAUSTED);
    }
    assertTrue(last < first, first + " " + last);
  }

  /** The variables a neighbourhood leaves free: those it does not fix. */
  private static boolean[] relaxed(int[] fixed, int n) {
    boolean[] free = new boolean[n];
    java.util.Arrays.fill(free, true);
    for (int i : fixed) {
      free[i] = false;
    }
    return free;
  }

  @Test
  void schedulingRelaxesTasksInATimeWindow() {
    // 12 unit tasks on a resource of capacity 1; the decision variables are the starts
    Store s = new Store();
    int n = 12;
    IntVar[] start = new IntVar[n];
    IntVar[] one = new IntVar[n];
    for (int i = 0; i < n; i++) {
      start[i] = new IntVar(s, "t" + i, 0, 2 * n);
      one[i] = new IntVar(s, 1, 1);
    }
    s.impose(new Cumulative(start, one, one, new IntVar(s, 1, 1)));
    IntVar c = new IntVar(s, "c", 0, 1000);
    AdaptiveLns lns = new AdaptiveLns(s, start, c, new Random(4));
    assertTrue(lns.usable(AdaptiveLns.Kind.SCHEDULING));
    // task i starts at 2 * (n - 1 - i)
    s.setLevel(s.level + 1);
    for (int i = 0; i < n; i++) {
      start[i].domain.inValue(s.level, start[i], 2 * (n - 1 - i));
    }
    assertTrue(s.consistency());
    lns.solution();
    s.removeLevel(s.level);
    s.setLevel(s.level - 1);
    for (int k = 0; k < 50; k++) {
      boolean[] free = relaxed(lns.neighbourhood(AdaptiveLns.Kind.SCHEDULING), n);
      // the relaxed tasks are consecutive in time
      int first = -1;
      int last = -1;
      int count = 0;
      for (int i = 0; i < n; i++) {
        if (free[i]) {
          first = first < 0 ? i : first;
          last = i;
          count++;
        }
      }
      assertTrue(count >= 2);
      assertEquals(last - first + 1, count, java.util.Arrays.toString(free));
      lns.outcome(AdaptiveLns.Outcome.EXHAUSTED);
    }
  }

  /**
   * The best solution given by values, as free search gives it the solution of LCG that the store
   * no longer admits, makes the same neighbourhoods as the same solution held by the store; a
   * solution that leaves a variable of the neighbourhoods without a value is not recorded.
   */
  @Test
  void solutionByValuesMakesTheSameNeighbourhoods() {
    AdaptiveLns held = withSolution(7);
    AdaptiveLns given = new AdaptiveLns(store, x, cost, new Random(7));
    assertFalse(given.solution(java.util.Arrays.copyOf(x, N - 1), new int[N - 1]));
    assertFalse(given.ready());
    int[] values = new int[N + 1];
    IntVar[] all = java.util.Arrays.copyOf(x, N + 1);
    all[N] = cost;
    for (int i = 0; i < N; i++) {
      values[i] = i;
      values[N] += (i + 1) * i;
    }
    assertTrue(given.solution(all, values));
    assertTrue(given.ready());
    for (AdaptiveLns.Kind kind :
        new AdaptiveLns.Kind[] {
          AdaptiveLns.Kind.RANDOM, AdaptiveLns.Kind.GRAPH, AdaptiveLns.Kind.OBJECTIVE
        }) {
      for (int k = 0; k < 10; k++) {
        assertEquals(
            java.util.Arrays.toString(held.neighbourhood(kind)),
            java.util.Arrays.toString(given.neighbourhood(kind)));
      }
    }
    for (int i = 0; i < N; i++) {
      assertEquals(held.value(i), given.value(i));
    }
  }

  /**
   * A shift neighbourhood relaxes the tasks of a window of time, bounds those after it from above
   * by their starts in the best solution and fixes those before it, so the best solution stays in
   * the neighbourhood and the schedule after the window can move to the left.
   */
  @Test
  void shiftBoundsTheTasksAfterTheWindow() {
    Store s = new Store();
    int n = 12;
    IntVar[] start = new IntVar[n];
    IntVar[] one = new IntVar[n];
    for (int i = 0; i < n; i++) {
      start[i] = new IntVar(s, "t" + i, 0, 2 * n);
      one[i] = new IntVar(s, 1, 1);
    }
    s.impose(new Cumulative(start, one, one, new IntVar(s, 1, 1)));
    IntVar c = new IntVar(s, "c", 0, 1000);
    AdaptiveLns lns = new AdaptiveLns(s, start, c, new Random(5));
    // task i starts at 2 * (n - 1 - i): later tasks have smaller indices
    int[] at = new int[n];
    for (int i = 0; i < n; i++) {
      at[i] = 2 * (n - 1 - i);
    }
    assertTrue(lns.solution(start, at));
    int bounds = 0;
    for (int k = 0; k < 50; k++) {
      int[] fixed = lns.neighbourhood(AdaptiveLns.Kind.SHIFT);
      int[] bounded = lns.upperBounded();
      boolean[] isFixed = new boolean[n];
      boolean[] isBounded = new boolean[n];
      for (int i : fixed) {
        isFixed[i] = true;
      }
      for (int i : bounded) {
        assertFalse(isFixed[i]);
        assertEquals(at[i], lns.value(i));
        isBounded[i] = true;
      }
      bounds += bounded.length;
      int windowFirst = Integer.MAX_VALUE;
      int windowLast = Integer.MIN_VALUE;
      for (int i = 0; i < n; i++) {
        if (!isFixed[i] && !isBounded[i]) {
          windowFirst = Math.min(windowFirst, at[i]);
          windowLast = Math.max(windowLast, at[i]);
        }
      }
      assertTrue(windowFirst <= windowLast);
      for (int i = 0; i < n; i++) {
        if (isFixed[i]) {
          assertTrue(at[i] < windowFirst);
        } else if (isBounded[i]) {
          assertTrue(at[i] > windowLast);
        }
      }
      lns.outcome(AdaptiveLns.Outcome.LIMIT);
    }
    assertTrue(bounds > 0);
    // the other kinds bound nothing
    lns.neighbourhood(AdaptiveLns.Kind.SCHEDULING);
    assertEquals(0, lns.upperBounded().length);
  }

  @Test
  void packingRelaxesRectanglesNearEachOther() {
    // 16 unit squares; the decision variables are their x and y origins
    Store s = new Store();
    int side = 4;
    int n = side * side;
    IntVar[][] rects = new IntVar[n][];
    IntVar[] xy = new IntVar[2 * n];
    for (int i = 0; i < n; i++) {
      IntVar localX = new IntVar(s, "x" + i, 0, 2 * side);
      IntVar y = new IntVar(s, "y" + i, 0, 2 * side);
      rects[i] = new IntVar[] {localX, y, new IntVar(s, 1, 1), new IntVar(s, 1, 1)};
      xy[2 * i] = localX;
      xy[2 * i + 1] = y;
    }
    s.impose(new Diffn(rects));
    IntVar c = new IntVar(s, "c", 0, 1000);
    AdaptiveLns lns = new AdaptiveLns(s, xy, c, new Random(5));
    assertTrue(lns.usable(AdaptiveLns.Kind.PACKING));
    // square i at (i % side, i / side)
    s.setLevel(s.level + 1);
    for (int i = 0; i < n; i++) {
      xy[2 * i].domain.inValue(s.level, xy[2 * i], i % side);
      xy[2 * i + 1].domain.inValue(s.level, xy[2 * i + 1], i / side);
    }
    assertTrue(s.consistency());
    lns.solution();
    s.removeLevel(s.level);
    s.setLevel(s.level - 1);
    for (int k = 0; k < 50; k++) {
      boolean[] free = relaxed(lns.neighbourhood(AdaptiveLns.Kind.PACKING), 2 * n);
      // a square is relaxed whole, and the relaxed squares fit in a box of side at most
      // ceil(sqrt(count)) + 1 cells
      int count = 0;
      int minX = side;
      int maxX = -1;
      int minY = side;
      int maxY = -1;
      for (int i = 0; i < n; i++) {
        assertEquals(free[2 * i], free[2 * i + 1], i + " " + java.util.Arrays.toString(free));
        if (free[2 * i]) {
          count++;
          minX = Math.min(minX, i % side);
          maxX = Math.max(maxX, i % side);
          minY = Math.min(minY, i / side);
          maxY = Math.max(maxY, i / side);
        }
      }
      if (count < n) {
        int box = (int) Math.ceil(Math.sqrt(count)) + 2;
        assertTrue(maxX - minX < box && maxY - minY < box, java.util.Arrays.toString(free));
      }
      lns.outcome(AdaptiveLns.Outcome.LIMIT);
    }
  }
}
