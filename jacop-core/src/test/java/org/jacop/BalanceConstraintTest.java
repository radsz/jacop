/*
 * BalanceConstraintTest.java
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

package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Arrays;
import java.util.Random;
import org.jacop.constraints.AbstractBalance;
import org.jacop.constraints.Deviation;
import org.jacop.constraints.Spread;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks the strength of {@link Deviation} and {@link Spread} at the nodes of random dives: every
 * bound of x has a support with the other variables in their integer intervals, the sum fixed and
 * the cost at most d.max, and d.min is at least the least cost of such an assignment (bounds(Z) of
 * the relaxation d &ge; cost). The least costs come from a dynamic program over the sums. Solution
 * sets are compared with brute force in {@link GlobalConstraintBruteForceTest}.
 */
class BalanceConstraintTest {

  /** Random instances per constraint; the {@code min} profile lowers it. */
  private static final int TRIALS = Integer.getInteger("balance.trials", 2000);

  private static final long NONE = Long.MAX_VALUE / 4;

  @Test
  void deviationIsBoundsConsistent() {
    dives(false, new Random(17));
  }

  @Test
  void spreadIsBoundsConsistent() {
    dives(true, new Random(18));
  }

  @Test
  void deviationProvesTheBalancedOptimumAtTheRoot() {
    // three loads in 0..10 with sum 10: the best is 3, 3, 4 with deviation |9-10|*2 + |12-10| = 4
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 10);
    }
    IntVar d = new IntVar(store, "d", 0, 100);
    store.impose(new Deviation(x, 10, d));
    assertThat(store.consistency()).isTrue();
    assertThat(d.min()).isEqualTo(4);

    // with d <= 4 every load is 3 or 4
    store.setLevel(1);
    d.domain.inMax(1, d, 4);
    assertThat(store.consistency()).isTrue();
    for (IntVar v : x) {
      assertThat(v.min()).isEqualTo(3);
      assertThat(v.max()).isEqualTo(4);
    }
  }

  @Test
  void spreadBoundsTheSumOfSquares() {
    // sum of squares of four values in 0..9 with sum 10: the best is 2, 2, 3, 3 with 26
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 9);
    }
    IntVar d = new IntVar(store, "d", 0, 1000);
    store.impose(new Spread(x, 1, 0, 10, d));
    assertThat(store.consistency()).isTrue();
    assertThat(d.min()).isEqualTo(26);

    // with d <= 30 a value 4 forces 4 + 2 + 2 + 2 = 28, and 5 needs at least 25 + 4 + 1 + 0
    store.setLevel(1);
    d.domain.inMax(1, d, 30);
    assertThat(store.consistency()).isTrue();
    for (IntVar v : x) {
      assertThat(v.min()).isEqualTo(1);
      assertThat(v.max()).isEqualTo(4);
    }
  }

  private static void dives(boolean squares, Random random) {
    for (int trial = 0; trial < TRIALS; trial++) {
      int n = 1 + random.nextInt(5);
      int s = -2 + random.nextInt(5 * n + 3);
      boolean mean = random.nextBoolean();
      int a = mean ? n : 1 + random.nextInt(4);
      int b = mean ? s : -4 + random.nextInt(16);

      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = variable(store, "x" + i, random, -2, 6);
      }
      int start = random.nextInt(squares ? 60 : 20);
      IntVar d = variable(store, "d", random, start, start + (squares ? 200 : 40));
      AbstractBalance c = squares ? new Spread(x, a, b, s, d) : new Deviation(x, a, b, s, d);
      String what = c.toString();
      store.impose(c);

      boolean ok = store.consistency();
      int level = 0;
      while (ok) {
        check(x, d, a, b, s, squares, what);
        if (level >= 8) {
          break;
        }
        // a random decision on one of x or d
        IntVar v = random.nextInt(n + 1) == n ? d : x[random.nextInt(n)];
        if (v.singleton()) {
          break;
        }
        level++;
        store.setLevel(level);
        int value = v.min() + random.nextInt(v.max() - v.min() + 1);
        try {
          decide(random.nextInt(4), v, value, level);
          ok = store.consistency();
        } catch (FailException e) {
          ok = false;
        }
      }
    }
  }

  private static void decide(int kind, IntVar v, int value, int level) {
    switch (kind) {
      case 0 -> v.domain.in(level, v, value, value);
      case 1 -> v.domain.inMax(level, v, Math.max(value, v.min()));
      case 2 -> v.domain.inMin(level, v, Math.min(value, v.max()));
      default -> {
        if (v.domain.contains(value)) {
          v.domain.inComplement(level, v, value);
        }
      }
    }
  }

  private static void check(
      IntVar[] x, IntVar d, int a, int b, int s, boolean squares, String what) {
    int n = x.length;
    long best = least(x, -1, 0, a, b, s, squares);
    assertThat((long) d.min()).as("d.min of %s", what).isGreaterThanOrEqualTo(best);
    for (int i = 0; i < n; i++) {
      for (int v : new int[] {x[i].min(), x[i].max()}) {
        long f = least(x, i, v, a, b, s, squares);
        assertThat(f)
            .as("support of x%d = %d in %s, %s", i, v, Arrays.toString(x), what)
            .isLessThanOrEqualTo(d.max());
      }
    }
  }

  /** Least cost over the integer intervals of x with sum s, x[fixed] = value when fixed >= 0. */
  private static long least(
      IntVar[] x, int fixed, int value, int a, int b, int s, boolean squares) {
    int offset = 2 * x.length * 10 + 10;
    long[] cost = new long[2 * offset + 1];
    Arrays.fill(cost, NONE);
    cost[offset] = 0;
    for (int i = 0; i < x.length; i++) {
      long[] next = new long[cost.length];
      Arrays.fill(next, NONE);
      int lo = i == fixed ? value : x[i].min();
      int hi = i == fixed ? value : x[i].max();
      for (int t = 0; t < cost.length; t++) {
        if (cost[t] == NONE) {
          continue;
        }
        for (int v = lo; v <= hi; v++) {
          int u = t + v;
          long e = (long) a * v - b;
          long g = squares ? e * e : Math.abs(e);
          if (u >= 0 && u < next.length && cost[t] + g < next[u]) {
            next[u] = cost[t] + g;
          }
        }
      }
      cost = next;
    }
    return cost[s + offset];
  }

  private static IntVar variable(Store store, String name, Random random, int lo, int hi) {
    IntervalDomain domain = new IntervalDomain();
    for (int v = lo; v <= hi; v++) {
      if (random.nextInt(4) != 0 || v == hi) {
        domain.unionAdapt(v, v);
      }
    }
    return new IntVar(store, name, domain);
  }
}
