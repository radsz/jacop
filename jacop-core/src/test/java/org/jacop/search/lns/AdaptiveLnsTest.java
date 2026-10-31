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
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.LinearInt;
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
    // every kind was used, the objective's terms included
    for (AdaptiveLns.Kind kind : AdaptiveLns.Kind.values()) {
      assertTrue(!lns.statistics().contains(kind + " 0/"), lns.statistics());
    }
    assertEquals(400, lns.runs());
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
}
