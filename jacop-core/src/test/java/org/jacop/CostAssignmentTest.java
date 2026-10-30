/*
 * CostAssignmentTest.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.TreeSet;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.CostAlldifferent;
import org.jacop.constraints.CostGCC;
import org.jacop.constraints.GlobalCardinality;
import org.jacop.core.Domain;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/** Brute-force checks of {@link CostAlldifferent} and {@link CostGCC}. */
class CostAssignmentTest {

  // -Dcostassignment.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("costassignment.instances", 1000);

  /**
   * A random instance: n variables with values offset..offset+m-1 (and a few outside), costs, and
   * for the GCC the domains of the counters.
   */
  private record Instance(
      int n, int m, int offset, int[][] domains, int[][] costs, int[] costDomain, int[][] counts) {

    /** Every assignment allowed by the domains and the counts, with its cost appended. */
    List<int[]> solutions() {
      List<int[]> result = new ArrayList<>();
      enumerate(0, new int[n + 1], new int[m], result);
      return result;
    }

    private void enumerate(int i, int[] t, int[] used, List<int[]> result) {
      if (i == n) {
        long sum = 0;
        for (int k = 0; k < n; k++) {
          sum += costs[k][t[k] - offset];
        }
        for (int j = 0; j < m; j++) {
          if (counts == null ? used[j] > 1 : !contains(counts[j], used[j])) {
            return;
          }
        }
        if (costDomain == null || contains(costDomain, (int) sum)) {
          int[] s = t.clone();
          s[n] = (int) sum;
          result.add(s);
        }
        return;
      }
      for (int value : domains[i]) {
        int j = value - offset;
        if (j >= 0 && j < m && (counts != null || used[j] == 0)) {
          used[j]++;
          t[i] = value;
          enumerate(i + 1, t, used, result);
          used[j]--;
        }
      }
    }
  }

  private static boolean contains(int[] values, int v) {
    for (int x : values) {
      if (x == v) {
        return true;
      }
    }
    return false;
  }

  private static IntDomain domainOf(int[] values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v, v);
    }
    return d;
  }

  private static int[] interval(int lo, int hi) {
    int[] r = new int[hi - lo + 1];
    for (int k = 0; k < r.length; k++) {
      r[k] = lo + k;
    }
    return r;
  }

  private static Instance randomInstance(Random random, boolean gcc) {
    int n = 1 + random.nextInt(6);
    int m = gcc ? 1 + random.nextInt(5) : n + random.nextInt(4);
    int offset = random.nextInt(5) - 2;
    int range = 1 + random.nextInt(random.nextBoolean() ? 10 : 200);
    int shift = random.nextInt(4) == 0 ? -range / 2 : 0;
    int[][] costs = new int[n][m];
    for (int[] row : costs) {
      for (int j = 0; j < m; j++) {
        row[j] = random.nextInt(range) + shift;
      }
    }
    double density = 0.4 + 0.6 * random.nextDouble();
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      List<Integer> values = new ArrayList<>();
      // values outside offset..offset+m-1 are left to the constraint to remove
      for (int v = offset - 1; v <= offset + m; v++) {
        if (random.nextDouble() < density) {
          values.add(v);
        }
      }
      if (values.isEmpty()) {
        values.add(offset + random.nextInt(m));
      }
      domains[i] = values.stream().mapToInt(Integer::intValue).toArray();
    }
    int[][] counts = null;
    if (gcc) {
      counts = new int[m][];
      for (int j = 0; j < m; j++) {
        int lo = random.nextInt(3) == 0 ? random.nextInt(2) : 0;
        int hi = lo + random.nextInt(n + 1);
        counts[j] = interval(lo, hi);
      }
    }
    List<int[]> all = new Instance(n, m, offset, domains, costs, null, counts).solutions();
    return new Instance(n, m, offset, domains, costs, costDomain(random, all, n), counts);
  }

  // a cost domain near the cheapest or the dearest solution, often with holes
  private static int[] costDomain(Random random, List<int[]> all, int n) {
    if (all.isEmpty()) {
      return interval(-50, 50);
    }
    int min = Integer.MAX_VALUE;
    int max = Integer.MIN_VALUE;
    for (int[] s : all) {
      min = Math.min(min, s[n]);
      max = Math.max(max, s[n]);
    }
    int spread = max - min;
    int lo;
    int hi;
    switch (random.nextInt(4)) {
      case 0 -> {
        lo = min - random.nextInt(3);
        hi = min + random.nextInt(spread / 4 + 2);
      }
      case 1 -> {
        lo = max - random.nextInt(spread / 4 + 2);
        hi = max + random.nextInt(3);
      }
      case 2 -> {
        lo = min + random.nextInt(spread + 1);
        hi = lo + random.nextInt(spread / 3 + 1);
      }
      default -> {
        lo = min - 5;
        hi = max + 5;
      }
    }
    List<Integer> values = new ArrayList<>();
    boolean holes = random.nextInt(3) == 0;
    for (int v = lo; v <= hi; v++) {
      if (!holes || v == lo || v == hi || random.nextInt(3) != 0) {
        values.add(v);
      }
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  private static void post(
      Store store, Instance in, IntVar[] x, IntVar cost, boolean gcc, boolean structural) {
    if (gcc) {
      IntVar[] counters = new IntVar[in.m];
      for (int j = 0; j < in.m; j++) {
        counters[j] = new IntVar(store, "c" + j, domainOf(in.counts[j]));
      }
      if (structural) {
        int[] values = new int[in.m];
        for (int k = 0; k < in.m; k++) {
          values[k] = in.offset + k;
        }
        store.impose(new GlobalCardinality(x, values, counters));
      }
      store.impose(new CostGCC(x, in.costs, counters, cost, in.offset));
    } else {
      if (structural) {
        store.impose(new Alldistinct(x));
      }
      store.impose(new CostAlldifferent(x, in.costs, cost, in.offset));
    }
  }

  private static TreeSet<String> solve(
      Instance in, boolean gcc, boolean structural, Random random) {
    Store store = new Store();
    IntVar[] x = new IntVar[in.n];
    for (int i = 0; i < in.n; i++) {
      x[i] = new IntVar(store, "x" + i, domainOf(in.domains[i]));
    }
    IntVar cost = new IntVar(store, "cost", domainOf(in.costDomain));
    List<IntVar> vars = new ArrayList<>(Arrays.asList(x));
    vars.add(cost);
    try {
      post(store, in, x, cost, gcc, structural);
    } catch (FailException e) {
      return new TreeSet<>();
    }
    TreeSet<String> found = new TreeSet<>();
    if (!store.consistency()) {
      return found;
    }
    Collections.shuffle(vars, random);
    IntVar[] order = vars.toArray(new IntVar[0]);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);
    if (search.labeling(
        store, new SimpleSelect<>(order, null, new IndomainRandom<>(random.nextInt())))) {
      for (int s = 1; s <= search.getSolutionListener().solutionsNo(); s++) {
        Domain[] sol = search.getSolutionListener().getSolution(s);
        int[] t = new int[in.n + 1];
        for (int k = 0; k < order.length; k++) {
          int pos = order[k] == cost ? in.n : Arrays.asList(x).indexOf(order[k]);
          t[pos] = ((IntDomain) sol[k]).value();
        }
        found.add(Arrays.toString(t));
      }
    }
    return found;
  }

  private static void check(long seed, boolean gcc) {
    Random random = new Random(seed);
    for (int t = 0; t < INSTANCES; t++) {
      Instance in = randomInstance(random, gcc);
      TreeSet<String> expected = new TreeSet<>();
      for (int[] s : in.solutions()) {
        expected.add(Arrays.toString(s));
      }
      boolean structural = random.nextInt(4) != 0;
      assertEquals(
          expected,
          solve(in, gcc, structural, random),
          "instance "
              + t
              + " seed "
              + seed
              + " structural "
              + structural
              + " n="
              + in.n
              + " m="
              + in.m
              + " offset="
              + in.offset
              + " domains="
              + Arrays.deepToString(in.domains)
              + " costs="
              + Arrays.deepToString(in.costs)
              + " cost="
              + Arrays.toString(in.costDomain)
              + " counts="
              + Arrays.deepToString(in.counts));
    }
  }

  @Test
  void costAlldifferentMatchesBruteForce() {
    check(17, false);
  }

  @Test
  void costGccMatchesBruteForce() {
    check(23, true);
  }

  /** The minimum assignment is exact, so a cost bounded from above gets the optimum as its min. */
  @Test
  void costAlldifferentLowerBoundIsTheOptimum() {
    Random random = new Random(5);
    for (int t = 0; t < INSTANCES; t++) {
      int n = 1 + random.nextInt(6);
      int m = n + random.nextInt(4);
      int[][] costs = new int[n][m];
      for (int[] row : costs) {
        for (int j = 0; j < m; j++) {
          row[j] = random.nextInt(100) - 30;
        }
      }
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = interval(0, m - 1);
      }
      List<int[]> all = new Instance(n, m, 0, domains, costs, null, null).solutions();
      int min = all.stream().mapToInt(s -> s[n]).min().orElseThrow();
      int max = all.stream().mapToInt(s -> s[n]).max().orElseThrow();
      IntVar[] costVars = new IntVar[2];
      for (int k = 0; k < 2; k++) {
        Store store = new Store();
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, 0, m - 1);
        }
        costVars[k] =
            k == 0
                ? new IntVar(store, "cost", -10000, min + random.nextInt(2))
                : new IntVar(store, "cost", max - random.nextInt(2), 10000);
        store.impose(new CostAlldifferent(x, costs, costVars[k], 0));
        assertEquals(true, store.consistency(), "instance " + t);
      }
      assertEquals(min, costVars[0].min(), "instance " + t + " " + Arrays.deepToString(costs));
      assertEquals(max, costVars[1].max(), "instance " + t + " " + Arrays.deepToString(costs));
    }
  }
}
