/*
 * StockingCostTest.java
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

import java.util.Arrays;
import java.util.Random;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.GCC;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.StockingCost;
import org.jacop.constraints.XlteqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.junit.jupiter.api.Test;

/**
 * Checks of {@link StockingCost}: the examples of the CP 2014 paper, the strength of its bounds
 * against a brute-force solution of the relaxation, and optima of random lot sizing problems
 * against the decomposition. Solution sets of the constraint alone are compared with a brute-force
 * enumeration in {@link GlobalConstraintBruteForceTest}.
 */
class StockingCostTest {

  // -Dstockingcost.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("stockingcost.instances", 1000);

  @Test
  void costOfTwoOrdersDueTogether() {
    // Example 1 of the paper: the decomposition keeps H in 0..2
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x1", 1, 2), new IntVar(store, "x2", 1, 2)};
    IntVar h = new IntVar(store, "H", 0, 2);
    store.impose(new StockingCost(x, new int[] {2, 2}, h, 1));
    assertTrue(store.consistency());
    assertEquals(1, h.min());
  }

  @Test
  void minimaFollowTheFullPeriods() {
    // Example 3 of the paper with H at most 2: H opt is 1, x1 = 4 costs 4 (x2 and x3 move down)
    // and x2 = 1 costs 3
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x1", 1, 5), new IntVar(store, "x2", 1, 4), new IntVar(store, "x3", 1, 4)
    };
    IntVar h = new IntVar(store, "H", 0, 2);
    store.impose(new StockingCost(x, new int[] {5, 4, 4}, h, 1));
    assertTrue(store.consistency());
    assertEquals(1, h.min());
    assertEquals(5, x[0].min());
    assertEquals(2, x[1].min());
    assertEquals(2, x[2].min());
  }

  @Test
  void exampleFourOfThePaper() {
    Store store = new Store();
    IntVar[] x = new IntVar[5];
    int[] max = {3, 6, 7, 7, 8};
    for (int i = 0; i < 5; i++) {
      x[i] = new IntVar(store, "x" + i, 1, max[i]);
    }
    IntVar h = new IntVar(store, "H", 0, 4);
    store.impose(new StockingCost(x, max, h, 1));
    assertTrue(store.consistency());
    assertEquals(2, h.min());
    assertEquals(1, x[0].min());
    assertEquals(4, x[1].min());
    assertEquals(4, x[2].min());
    assertEquals(4, x[3].min());
    assertEquals(8, x[4].min());
  }

  @Test
  void producedOrdersUseTheirPeriod() {
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x1", 3, 3), new IntVar(store, "x2", 0, 3), new IntVar(store, "x3", 0, 4)
    };
    IntVar h = new IntVar(store, "H", 0, 100);
    store.impose(new StockingCost(x, new int[] {3, 3, 3}, h, 1));
    assertTrue(store.consistency());
    // x3 is cut to its due date, and neither x2 nor x3 can share period 3 with x1
    assertEquals(2, x[2].max());
    assertEquals(2, x[1].max());
    assertEquals(3, h.min());
  }

  @Test
  void rejectsBadArguments() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 0, 3)};
    IntVar h = new IntVar(store, 0, 3);
    assertThatThrownBy(() -> new StockingCost(x, new int[] {1, 2}, h, 1))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new StockingCost(x, new int[] {1}, h, 0))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new StockingCost(x, new int[] {1}, new int[] {-1}, h, 1))
        .isInstanceOf(IllegalArgumentException.class);
  }

  /**
   * A random state: orders with domains (some fixed), due dates, costs, capacity and cost bounds.
   */
  private record Instance(
      int[][] domains, int[] due, int[] h, int capacity, int costMin, int costMax) {

    static Instance random(Random random, boolean itemDependent) {
      int n = 1 + random.nextInt(4);
      int[][] domains = new int[n][];
      int[] due = new int[n];
      int[] h = new int[n];
      for (int i = 0; i < n; i++) {
        due[i] = 2 + random.nextInt(6);
        if (random.nextInt(5) == 0) {
          domains[i] = new int[] {random.nextInt(due[i] + 1)};
        } else {
          int lo = random.nextInt(5);
          int hi = lo + random.nextInt(6);
          domains[i] =
              java.util.stream.IntStream.rangeClosed(lo, hi)
                  .filter(v -> v == lo || random.nextInt(4) != 0)
                  .toArray();
        }
        h[i] = itemDependent ? random.nextInt(4) : 1;
      }
      int capacity = 1 + random.nextInt(2);
      int costMin = random.nextInt(3);
      return new Instance(domains, due, h, capacity, costMin, costMin + random.nextInt(4 * n + 1));
    }
  }

  /**
   * The optimum of the relaxation: free orders anywhere up to their maximum (and their due date),
   * produced orders at their period, at most capacity per period; MAX_VALUE if infeasible. Order
   * forced, if not negative, is put at period value.
   */
  private static long relaxed(
      int[] lo, int[] hi, int[] due, int[] h, int capacity, int forced, int value) {
    int n = lo.length;
    int[] low = new int[n];
    int[] high = new int[n];
    int bottom = Integer.MAX_VALUE;
    for (int i = 0; i < n; i++) {
      bottom = Math.min(bottom, lo[i]);
    }
    for (int i = 0; i < n; i++) {
      high[i] = Math.min(hi[i], due[i]);
      // n periods below every minimum are enough room for everything that moves down
      low[i] = lo[i] == hi[i] ? lo[i] : bottom - n;
      if (i == forced) {
        low[i] = value;
        high[i] = value;
      }
    }
    return search(0, new int[n], low, high, due, h, capacity);
  }

  private static long search(
      int i, int[] t, int[] low, int[] high, int[] due, int[] h, int capacity) {
    if (i == t.length) {
      long total = 0;
      for (int a = 0; a < t.length; a++) {
        int same = 0;
        for (int b = 0; b < t.length; b++) {
          same += t[a] == t[b] ? 1 : 0;
        }
        if (same > capacity) {
          return Long.MAX_VALUE;
        }
        total += (long) h[a] * (due[a] - t[a]);
      }
      return total;
    }
    long best = Long.MAX_VALUE;
    for (int v = high[i]; v >= low[i]; v--) {
      t[i] = v;
      best = Math.min(best, search(i + 1, t, low, high, due, h, capacity));
    }
    return best;
  }

  @Test
  void uniformCostReachesBoundsOfTheRelaxation() {
    checkBounds(false);
  }

  @Test
  void itemDependentCostBoundIsTheRelaxedOptimum() {
    checkBounds(true);
  }

  /**
   * At the fixpoint the minimum of H is the optimum of the relaxation; with equal costs every
   * minimum of x has a support in it within the maximum of H, and so does every maximum.
   */
  private static void checkBounds(boolean itemDependent) {
    Random random = new Random(itemDependent ? 11 : 7);
    int supported = 0;
    int checked = 0;
    for (int trial = 0; trial < INSTANCES; trial++) {
      Instance in = Instance.random(random, itemDependent);
      int n = in.due().length;
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i);
        for (int v : in.domains()[i]) {
          x[i].addDom(v, v);
        }
      }
      IntVar cost = new IntVar(store, "H", in.costMin(), in.costMax());
      store.impose(new StockingCost(x, in.due(), in.h(), cost, in.capacity()));
      boolean consistent = store.consistency();

      int[] lo = new int[n];
      int[] hi = new int[n];
      for (int i = 0; i < n; i++) {
        lo[i] = in.domains()[i][0];
        hi[i] = in.domains()[i][in.domains()[i].length - 1];
      }
      String what =
          Arrays.deepToString(in.domains())
              + " due="
              + Arrays.toString(in.due())
              + " h="
              + Arrays.toString(in.h())
              + " c="
              + in.capacity()
              + " H="
              + in.costMin()
              + ".."
              + in.costMax();
      if (!consistent) {
        continue;
      }
      for (int i = 0; i < n; i++) {
        lo[i] = x[i].min();
        hi[i] = x[i].max();
      }
      long optimum = relaxed(lo, hi, in.due(), in.h(), in.capacity(), -1, 0);
      assertEquals(Math.max(optimum, in.costMin()), cost.min(), "H min of " + what);
      for (int i = 0; i < n; i++) {
        if (x[i].singleton()) {
          continue;
        }
        for (int v : new int[] {x[i].min(), x[i].max()}) {
          checked++;
          if (relaxed(lo, hi, in.due(), in.h(), in.capacity(), i, v) <= cost.max()) {
            supported++;
          } else if (!itemDependent) {
            throw new AssertionError(
                "no support for x"
                    + i
                    + " = "
                    + v
                    + " in "
                    + what
                    + " after "
                    + Arrays.toString(x));
          }
        }
      }
    }
    assertTrue(checked > INSTANCES / 2, "too few free orders checked: " + checked);
    if (itemDependent) {
      // the bound is not exact, but it holds for most orders
      assertTrue(supported > checked * 0.8, supported + " of " + checked + " bounds supported");
    }
  }

  @Test
  void optimaMatchTheDecomposition() {
    Random random = new Random(3);
    int instances = Math.max(20, INSTANCES / 10);
    for (int trial = 0; trial < instances; trial++) {
      int n = 4 + random.nextInt(6);
      int horizon = n + random.nextInt(4);
      int capacity = random.nextInt(4) == 0 ? 2 : 1;
      int[] due = new int[n];
      int[] h = new int[n];
      boolean itemDependent = random.nextBoolean();
      for (int i = 0; i < n; i++) {
        due[i] = random.nextInt(horizon);
        h[i] = itemDependent ? random.nextInt(5) : 1;
      }
      long withConstraint = optimum(due, h, horizon, capacity, true, random.nextLong());
      long decomposed = optimum(due, h, horizon, capacity, false, 0);
      assertEquals(
          decomposed,
          withConstraint,
          "due=" + Arrays.toString(due) + " h=" + Arrays.toString(h) + " c=" + capacity);
    }
  }

  private static long optimum(
      int[] due, int[] h, int horizon, int capacity, boolean global, long seed) {
    int n = due.length;
    Store store = new Store();
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, -horizon, horizon);
      store.impose(new XlteqC(x[i], due[i]));
    }
    long most = 0;
    for (int i = 0; i < n; i++) {
      most += (long) h[i] * 2 * horizon;
    }
    IntVar cost = new IntVar(store, "H", 0, (int) most);
    if (capacity == 1) {
      store.impose(new Alldistinct(x));
    } else {
      IntVar[] counters = new IntVar[2 * horizon + 1];
      for (int t = 0; t < counters.length; t++) {
        counters[t] = new IntVar(store, 0, capacity);
      }
      store.impose(new GCC(x, counters));
    }
    IntVar[] vars = Arrays.copyOf(x, n + 1);
    vars[n] = cost;
    int[] weights = new int[n + 1];
    long constant = 0;
    for (int i = 0; i < n; i++) {
      weights[i] = -h[i];
      constant += (long) h[i] * due[i];
    }
    weights[n] = -1;
    // H = sum h * (due - x)
    store.impose(new LinearInt(vars, weights, "==", (int) -constant));
    if (global) {
      store.impose(new StockingCost(x, due, h, cost, capacity));
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select =
        global
            ? new SimpleSelect<>(x, new SmallestDomain<>(), new IndomainRandom<>((int) seed))
            : new SimpleSelect<>(x, null, new IndomainMax<>());
    search.setPrintInfo(false);
    assertTrue(search.labeling(store, select, cost));
    assertFalse(cost.min() < 0);
    return cost.value();
  }
}
