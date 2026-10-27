/*
 * WeightedCompletionTest.java
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
import org.jacop.constraints.WeightedCompletion;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestMin;
import org.junit.jupiter.api.Test;

/**
 * Checks of {@link WeightedCompletion}: the pruning at the root against a reference that solves the
 * mean busy time relaxation in exact arithmetic for every start of every task, and optima of random
 * single machine problems against the weighted sum alone. Solution sets of the constraint alone are
 * compared with a brute-force enumeration in {@link GlobalConstraintBruteForceTest}.
 */
class WeightedCompletionTest {

  // -Dweightedcompletion.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("weightedcompletion.instances", 1000);

  @Test
  void boundOfTwoTasks() {
    // a (d 2, w 1) and b (d 1, w 3) released at 0: b first, cost 3 * 1 + 1 * 3 = 6
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 10);
    IntVar b = new IntVar(store, "b", 0, 10);
    IntVar c = new IntVar(store, "c", 0, 100);
    store.impose(
        new WeightedCompletion(new IntVar[] {a, b}, new int[] {2, 1}, new int[] {1, 3}, c));
    assertTrue(store.consistency());
    assertEquals(6, c.min());
  }

  @Test
  void startsAboveTheCostAreRemoved() {
    // with cost at most 6 only b = 0, a = 1 remains
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 10);
    IntVar b = new IntVar(store, "b", 0, 10);
    IntVar c = new IntVar(store, "c", 0, 6);
    store.impose(
        new WeightedCompletion(new IntVar[] {a, b}, new int[] {2, 1}, new int[] {1, 3}, c));
    assertTrue(store.consistency());
    assertEquals(1, a.value());
    assertEquals(0, b.value());
  }

  @Test
  void overlappingFixedTasksFail() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 0);
    IntVar b = new IntVar(store, "b", 1, 1);
    IntVar c = new IntVar(store, "c", 0, 100);
    store.impose(
        new WeightedCompletion(new IntVar[] {a, b}, new int[] {2, 1}, new int[] {1, 1}, c));
    assertFalse(store.consistency());
  }

  @Test
  void argumentsAreChecked() {
    Store store = new Store();
    IntVar[] s = {new IntVar(store, 0, 3)};
    IntVar c = new IntVar(store, 0, 9);
    assertThatThrownBy(() -> new WeightedCompletion(s, new int[] {1, 2}, new int[] {1}, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new WeightedCompletion(s, new int[] {-1}, new int[] {1}, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new WeightedCompletion(s, new int[] {1}, new int[] {-1}, c))
        .isInstanceOf(IllegalArgumentException.class);
  }

  /** Domains after the root propagation equal the exact fixpoint of the relaxation. */
  @Test
  void rootPruningMatchesExactReference() {
    Random random = new Random(7);
    for (int instance = 0; instance < INSTANCES; instance++) {
      int n = 1 + random.nextInt(6);
      int[] d = new int[n];
      int[] w = new int[n];
      int[][] dom = new int[n][];
      for (int i = 0; i < n; i++) {
        d[i] = random.nextInt(5);
        w[i] = random.nextInt(6);
        dom[i] = randomDomain(random, random.nextInt(8), 4 + random.nextInt(14));
      }
      int costMax = random.nextInt(4) == 0 ? 10000 : random.nextInt(25 * n * n + 1);

      Store store = new Store();
      IntVar[] s = new IntVar[n];
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i, domainOf(dom[i]));
      }
      IntVar c = new IntVar(store, "c", 0, costMax);
      store.impose(new WeightedCompletion(s, d, w, c));
      boolean consistent = store.consistency();

      Reference ref = new Reference(d, w, dom, costMax);
      boolean expected = ref.fixpoint();
      String description =
          "instance "
              + instance
              + " d="
              + Arrays.toString(d)
              + " w="
              + Arrays.toString(w)
              + " domains="
              + Arrays.deepToString(dom)
              + " cost<="
              + costMax;
      assertEquals(expected, consistent, description);
      if (expected) {
        for (int i = 0; i < n; i++) {
          assertEquals(
              Arrays.toString(ref.domains.get(i).stream().mapToInt(Integer::intValue).toArray()),
              Arrays.toString(values(s[i])),
              description + " s" + i);
        }
        assertEquals(ref.costMin, c.min(), description + " cost");
      }
    }
  }

  /** Optima of random single machine problems with and without the constraint agree. */
  @Test
  void optimaMatchTheWeightedSum() {
    Random random = new Random(11);
    int count = Math.max(20, INSTANCES / 10);
    for (int instance = 0; instance < count; instance++) {
      int n = 2 + random.nextInt(5);
      int[] d = new int[n];
      int[] w = new int[n];
      int[] r = new int[n];
      for (int i = 0; i < n; i++) {
        d[i] = 1 + random.nextInt(5);
        w[i] = random.nextInt(6);
        r[i] = random.nextInt(3 * n);
      }
      int with = optimum(d, w, r, true);
      int without = optimum(d, w, r, false);
      assertEquals(
          without,
          with,
          "d=" + Arrays.toString(d) + " w=" + Arrays.toString(w) + " r=" + Arrays.toString(r));
    }
  }

  private static int optimum(int[] d, int[] w, int[] r, boolean global) {
    int n = d.length;
    Store store = new Store();
    IntVar[] s = new IntVar[n];
    IntVar[] dv = new IntVar[n];
    IntVar[] one = new IntVar[n];
    int horizon = 0;
    for (int i = 0; i < n; i++) {
      horizon = Math.max(horizon, r[i]);
    }
    for (int i = 0; i < n; i++) {
      horizon += d[i];
    }
    int[] coefficients = new int[n + 1];
    IntVar[] terms = new IntVar[n + 1];
    int constant = 0;
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, r[i], horizon);
      dv[i] = new IntVar(store, d[i], d[i]);
      one[i] = new IntVar(store, 1, 1);
      terms[i] = s[i];
      coefficients[i] = w[i];
      constant += w[i] * d[i];
    }
    IntVar cost = new IntVar(store, "cost", 0, 1000000);
    terms[n] = cost;
    coefficients[n] = -1;
    store.impose(new LinearInt(terms, coefficients, "==", -constant));
    store.impose(new CumulativeUnary(s, dv, one, new IntVar(store, 1, 1)));
    if (global) {
      store.impose(new WeightedCompletion(s, d, w, cost));
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(s, new SmallestMin<>(), new IndomainMin<>());
    search.setPrintInfo(false);
    assertTrue(search.labeling(store, select, cost));
    return cost.value();
  }

  private static int[] randomDomain(Random random, int lo, int width) {
    List<Integer> values = new ArrayList<>();
    for (int v = lo; v <= lo + width; v++) {
      if (random.nextInt(5) != 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(lo);
    }
    // a third of the tasks are fixed
    if (random.nextInt(3) == 0) {
      return new int[] {values.get(random.nextInt(values.size()))};
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  private static IntDomain domainOf(int[] values) {
    IntervalDomain domain = new IntervalDomain();
    for (int v : values) {
      domain.unionAdapt(v, v);
    }
    return domain;
  }

  private static int[] values(IntVar v) {
    List<Integer> list = new ArrayList<>();
    for (int x = v.min(); x <= v.max(); x++) {
      if (v.domain.contains(x)) {
        list.add(x);
      }
    }
    return list.stream().mapToInt(Integer::intValue).toArray();
  }

  /**
   * The pruning of the constraint, computed in exact arithmetic with one unit of time at a time:
   * all bounds are scaled by 2 * L, L the least common multiple of the durations.
   */
  private static final class Reference {
    final int n;
    final int[] d;
    final int[] w;
    final List<List<Integer>> domains = new ArrayList<>();
    final long scale;
    long costMin = 0;
    final long costMax;

    Reference(int[] d, int[] w, int[][] dom, int costMax) {
      this.n = d.length;
      this.d = d;
      this.w = w;
      this.costMax = costMax;
      long l = 1;
      for (int p : d) {
        if (p > 0) {
          l = l / gcd(l, p) * p;
        }
      }
      this.scale = 2 * l;
      for (int[] values : dom) {
        List<Integer> list = new ArrayList<>();
        for (int v : values) {
          list.add(v);
        }
        domains.add(list);
      }
    }

    static long gcd(long a, long b) {
      return b == 0 ? a : gcd(b, a % b);
    }

    boolean fixed(int i) {
      return domains.get(i).size() == 1;
    }

    int min(int i) {
      return domains.get(i).get(0);
    }

    int max(int i) {
      return domains.get(i).get(domains.get(i).size() - 1);
    }

    /** It returns false on failure. */
    boolean fixpoint() {
      boolean changed = true;
      while (changed) {
        changed = false;
        for (int i = 0; i < n; i++) {
          for (int j = i + 1; j < n; j++) {
            if (fixed(i) && fixed(j) && overlap(i, min(i), j, min(j))) {
              return false;
            }
          }
        }
        long bound = scaledBound(-1, 0);
        long best = bound;
        for (int i = 0; i < n; i++) {
          if (fixed(i)) {
            continue;
          }
          if (d[i] == 0) {
            if (w[i] > 0) {
              long others = bound - scale * w[i] * min(i);
              List<Integer> kept = new ArrayList<>();
              for (int t : domains.get(i)) {
                if (others + scale * w[i] * t <= costMax * scale) {
                  kept.add(t);
                }
              }
              if (kept.isEmpty()) {
                return false;
              }
              changed |= kept.size() != domains.get(i).size();
              domains.set(i, kept);
            }
            continue;
          }
          List<Integer> kept = new ArrayList<>();
          long least = Long.MAX_VALUE;
          for (int t = min(i); t <= max(i); t++) {
            boolean clash = false;
            for (int j = 0; j < n; j++) {
              if (j != i && fixed(j) && overlap(i, t, j, min(j))) {
                clash = true;
              }
            }
            if (clash) {
              continue;
            }
            long g = scaledBound(i, t);
            if (g > costMax * scale) {
              continue;
            }
            least = Math.min(least, g);
            if (domains.get(i).contains(t)) {
              kept.add(t);
            }
          }
          if (kept.isEmpty()) {
            return false;
          }
          changed |= kept.size() != domains.get(i).size();
          domains.set(i, kept);
          best = Math.max(best, least);
        }
        long lower = Math.ceilDiv(best, scale);
        if (lower > costMax) {
          return false;
        }
        costMin = Math.max(costMin, lower);
      }
      return true;
    }

    boolean overlap(int i, int ti, int j, int tj) {
      return d[i] > 0 && d[j] > 0 && ti < tj + d[j] && tj < ti + d[i];
    }

    /** The bound with task i at t (none for i &lt; 0), times scale. */
    long scaledBound(int i, int t) {
      long total = 0;
      int horizon = 0;
      List<Integer> free = new ArrayList<>();
      boolean[] busy = new boolean[200];
      for (int j = 0; j < n; j++) {
        if (j == i) {
          total += scale * w[j] * (t + d[j]);
          for (int u = t; u < t + d[j]; u++) {
            busy[u] = true;
          }
        } else if (fixed(j)) {
          total += scale * w[j] * (min(j) + d[j]);
          for (int u = min(j); u < min(j) + d[j]; u++) {
            busy[u] = true;
          }
        } else if (d[j] == 0) {
          total += scale * w[j] * min(j);
        } else {
          free.add(j);
          horizon = Math.max(horizon, min(j));
        }
      }
      int[] remaining = new int[n];
      for (int j : free) {
        remaining[j] = d[j];
      }
      int left = free.size();
      for (int u = 0; left > 0; u++) {
        if (busy[u]) {
          continue;
        }
        int pick = -1;
        for (int j : free) {
          if (remaining[j] > 0
              && min(j) <= u
              && (pick < 0 || (long) w[j] * d[pick] > (long) w[pick] * d[j])) {
            pick = j;
          }
        }
        if (pick < 0) {
          continue;
        }
        // (w / d) * (u + 1/2) times 2 * L
        total += (long) w[pick] * (scale / 2 / d[pick]) * (2L * u + 1);
        if (--remaining[pick] == 0) {
          left--;
        }
      }
      // w * d / 2 times 2 * L
      for (int j : free) {
        total += (long) w[j] * d[j] * (scale / 2);
      }
      return total;
    }
  }
}
