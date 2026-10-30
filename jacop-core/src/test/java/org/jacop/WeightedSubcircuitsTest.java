/*
 * WeightedSubcircuitsTest.java
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
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.TreeSet;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.WeightedSubcircuits;
import org.jacop.constraints.XeqC;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.junit.jupiter.api.Test;

/** Brute-force checks of {@link WeightedSubcircuits} against an enumeration of the tours. */
class WeightedSubcircuitsTest {

  // -Dweightedsubcircuits.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("weightedsubcircuits.instances", 400);

  /**
   * A random instance: successor domains (values offset..offset+n-1), tour domains (0..k), costs
   * and the domains of the tour costs and of the cost; a null domain is unconstrained.
   */
  private record Instance(
      int n,
      int k,
      int offset,
      int[][] next,
      int[][] tours,
      int[][] costs,
      int[][] tourCosts,
      int[] costDomain) {

    /** Every solution: successors (from 0), tours, tour costs and cost. */
    List<int[]> solutions() {
      List<int[]> result = new ArrayList<>();
      enumerate(0, new int[n], new boolean[n], result);
      return result;
    }

    private void enumerate(int i, int[] succ, boolean[] usedValue, List<int[]> result) {
      if (i == n) {
        // the circuits of the permutation, each to a different tour
        int[] cycle = new int[n];
        Arrays.fill(cycle, -1);
        List<Integer> starts = new ArrayList<>();
        for (int s = 0; s < n; s++) {
          if (succ[s] != s && cycle[s] < 0) {
            int c = starts.size();
            starts.add(s);
            int v = s;
            do {
              cycle[v] = c;
              v = succ[v];
            } while (v != s);
          }
        }
        assignTours(
            0, starts.size(), new int[starts.size()], new boolean[k + 1], succ, cycle, result);
        return;
      }
      for (int value : next[i]) {
        int j = value - offset;
        if (j >= 0 && j < n && !usedValue[j]) {
          usedValue[j] = true;
          succ[i] = j;
          enumerate(i + 1, succ, usedValue, result);
          usedValue[j] = false;
        }
      }
    }

    private void assignTours(
        int c, int cycles, int[] tourOf, boolean[] used, int[] succ, int[] cycle, List<int[]> out) {
      if (c == cycles) {
        int[] t = new int[n];
        long[] sums = new long[k + 1];
        long total = 0;
        for (int i = 0; i < n; i++) {
          t[i] = cycle[i] < 0 ? 0 : tourOf[cycle[i]];
          if (!contains(tours[i], t[i])) {
            return;
          }
          sums[t[i]] += costs[i][succ[i]];
          total += costs[i][succ[i]];
        }
        for (int tv = 1; tv <= k; tv++) {
          if (tourCosts[tv - 1] != null && !contains(tourCosts[tv - 1], (int) sums[tv])) {
            return;
          }
        }
        if (costDomain != null && !contains(costDomain, (int) total)) {
          return;
        }
        int[] s = new int[2 * n + k + 1];
        for (int i = 0; i < n; i++) {
          s[i] = succ[i];
          s[n + i] = t[i];
        }
        for (int tv = 1; tv <= k; tv++) {
          s[2 * n + tv - 1] = (int) sums[tv];
        }
        s[2 * n + k] = (int) total;
        out.add(s);
        return;
      }
      for (int tv = 1; tv <= k; tv++) {
        if (!used[tv]) {
          used[tv] = true;
          tourOf[c] = tv;
          assignTours(c + 1, cycles, tourOf, used, succ, cycle, out);
          used[tv] = false;
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

  private static int[] range(int lo, int hi) {
    int[] values = new int[hi - lo + 1];
    for (int v = lo; v <= hi; v++) {
      values[v - lo] = v;
    }
    return values;
  }

  // a domain near the smallest or the largest value of the given ones, often with holes
  private static int[] domainNear(Random random, TreeSet<Integer> values) {
    if (values.isEmpty()) {
      return range(-5, 5);
    }
    int min = values.first();
    int max = values.last();
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
    List<Integer> result = new ArrayList<>();
    boolean holes = random.nextInt(3) == 0;
    for (int v = lo; v <= hi; v++) {
      if (!holes || v == lo || v == hi || random.nextInt(3) != 0) {
        result.add(v);
      }
    }
    return result.stream().mapToInt(Integer::intValue).toArray();
  }

  private static int[][] randomCosts(Random random, int n) {
    int range = 1 + random.nextInt(random.nextBoolean() ? 10 : 100);
    int shift = random.nextInt(4) == 0 ? -range / 2 : 0;
    boolean euclidean = random.nextBoolean();
    int[][] xy = new int[n][2];
    for (int[] p : xy) {
      p[0] = random.nextInt(range + 1);
      p[1] = random.nextInt(range + 1);
    }
    boolean penalties = random.nextBoolean();
    int[][] costs = new int[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i == j) {
          costs[i][j] = penalties ? random.nextInt(range) + shift : 0;
        } else if (euclidean) {
          costs[i][j] =
              (int) Math.round(Math.hypot((double) xy[i][0] - xy[j][0], xy[i][1] - xy[j][1]));
        } else {
          costs[i][j] = random.nextInt(range) + shift;
        }
      }
    }
    return costs;
  }

  private static Instance randomInstance(Random random, int n, int k) {
    int offset = random.nextInt(4) - 1;
    int[][] costs = randomCosts(random, n);
    int[][] next = new int[n][];
    double density = 0.4 + 0.6 * random.nextDouble();
    double self = random.nextDouble();
    for (int i = 0; i < n; i++) {
      List<Integer> values = new ArrayList<>();
      for (int v = offset - 1; v <= offset + n; v++) {
        if (v == offset + i ? random.nextDouble() < self : random.nextDouble() < density) {
          values.add(v);
        }
      }
      if (values.isEmpty()) {
        values.add(offset + i);
      }
      next[i] = values.stream().mapToInt(Integer::intValue).toArray();
    }
    int[][] tours = new int[n][];
    for (int i = 0; i < n; i++) {
      List<Integer> values = new ArrayList<>();
      for (int v = -1; v <= k + 1; v++) {
        if (random.nextInt(4) != 0) {
          values.add(v);
        }
      }
      if (values.isEmpty()) {
        values.add(0);
      }
      tours[i] = values.stream().mapToInt(Integer::intValue).toArray();
    }
    Instance free = new Instance(n, k, offset, next, tours, costs, new int[k][], null);
    List<int[]> all = free.solutions();
    int[][] tourCosts = new int[k][];
    for (int tv = 0; tv < k; tv++) {
      if (random.nextInt(3) != 0) {
        TreeSet<Integer> values = new TreeSet<>();
        for (int[] s : all) {
          values.add(s[2 * n + tv]);
        }
        tourCosts[tv] = domainNear(random, values);
      }
    }
    int[] costDomain = null;
    if (random.nextInt(3) != 0) {
      TreeSet<Integer> values = new TreeSet<>();
      for (int[] s : all) {
        values.add(s[2 * n + k]);
      }
      costDomain = domainNear(random, values);
    }
    return new Instance(n, k, offset, next, tours, costs, tourCosts, costDomain);
  }

  private record Variables(Store store, IntVar[] all, IntVar[] x, IntVar[] tourCost, IntVar cost) {}

  /** Filtering variants: 0 both (the default), 1 assignment only, 2 Steiner only, 3 none. */
  private static Variables post(Instance in, boolean withAlldistinct, int filtering) {
    Store store = new Store();
    int n = in.n;
    IntVar[] x = new IntVar[n];
    IntVar[] t = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, domainOf(in.next[i]));
      t[i] = new IntVar(store, "t" + i, domainOf(in.tours[i]));
    }
    IntVar[] tc = new IntVar[in.k];
    for (int tv = 0; tv < in.k; tv++) {
      int[] d = in.tourCosts[tv] == null ? range(-2000, 2000) : in.tourCosts[tv];
      tc[tv] = new IntVar(store, "c" + (tv + 1), domainOf(d));
    }
    IntVar cost =
        new IntVar(
            store, "cost", domainOf(in.costDomain == null ? range(-4000, 4000) : in.costDomain));
    WeightedSubcircuits c = new WeightedSubcircuits(x, t, in.costs, tc, cost, in.offset);
    switch (filtering) {
      case 1 -> c.setFiltering(true, false);
      case 2 -> c.setFiltering(false, true);
      case 3 -> c.setFiltering(false, false);
      default -> {
        // both relaxations
      }
    }
    if (withAlldistinct) {
      store.impose(new Alldistinct(x));
    }
    store.impose(c);
    IntVar[] all = new IntVar[2 * n + in.k + 1];
    System.arraycopy(x, 0, all, 0, n);
    System.arraycopy(t, 0, all, n, n);
    System.arraycopy(tc, 0, all, 2 * n, in.k);
    all[2 * n + in.k] = cost;
    return new Variables(store, all, x, tc, cost);
  }

  private static TreeSet<String> solve(Variables v, Random random) {
    TreeSet<String> found = new TreeSet<>();
    if (!v.store.consistency()) {
      return found;
    }
    List<IntVar> shuffled = new ArrayList<>(Arrays.asList(v.all));
    Collections.shuffle(shuffled, random);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            shuffled.toArray(new IntVar[0]), null, new IndomainRandom<>(random.nextInt()));
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);
    if (search.labeling(v.store, select)) {
      int count = search.getSolutionListener().solutionsNo();
      for (int s = 1; s <= count; s++) {
        Domain[] sol = search.getSolutionListener().getSolution(s);
        int[] t = new int[v.all.length];
        for (int q = 0; q < v.all.length; q++) {
          t[q] = ((IntDomain) sol[shuffled.indexOf(v.all[q])]).value();
        }
        found.add(Arrays.toString(t));
      }
    }
    return found;
  }

  private static TreeSet<String> expected(Instance in) {
    TreeSet<String> result = new TreeSet<>();
    for (int[] s : in.solutions()) {
      int[] t = s.clone();
      for (int i = 0; i < in.n; i++) {
        t[i] += in.offset;
      }
      result.add(Arrays.toString(t));
    }
    return result;
  }

  private static String describe(Instance in) {
    return "n="
        + in.n
        + " k="
        + in.k
        + " offset="
        + in.offset
        + " next="
        + Arrays.deepToString(in.next)
        + " tours="
        + Arrays.deepToString(in.tours)
        + " costs="
        + Arrays.deepToString(in.costs)
        + " tourCosts="
        + Arrays.deepToString(in.tourCosts)
        + " cost="
        + Arrays.toString(in.costDomain);
  }

  @Test
  void allSolutionsMatchBruteForce() {
    Random random = new Random(61);
    for (int t = 0; t < INSTANCES; t++) {
      boolean withAlldistinct = random.nextInt(4) != 0;
      int n = 1 + random.nextInt(withAlldistinct ? 6 : 5);
      int k = 1 + random.nextInt(3);
      Instance in = randomInstance(random, n, k);
      int filtering = random.nextInt(4);
      assertEquals(
          expected(in),
          solve(post(in, withAlldistinct, filtering), random),
          "instance "
              + t
              + " alldistinct "
              + withAlldistinct
              + " filtering "
              + filtering
              + ": "
              + describe(in));
    }
  }

  // minimisation of the cost with a bound on the cost of each tour, against an enumeration
  @Test
  void minimumCostMatchesBruteForce() {
    Random random = new Random(62);
    for (int t = 0; t < 300; t++) {
      int n = 3 + random.nextInt(5);
      int k = 1 + random.nextInt(3);
      Instance in = randomInstance(random, n, k);
      in = new Instance(n, k, 1, wideNext(n), in.tours, in.costs, in.tourCosts, range(-4000, 4000));
      int best = Integer.MAX_VALUE;
      for (int[] s : in.solutions()) {
        best = Math.min(best, s[2 * n + k]);
      }
      int filtering = random.nextInt(3);
      Variables v = post(in, true, filtering);
      Integer optimum = null;
      if (v.store.consistency()) {
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        IntVar[] decisions = Arrays.copyOf(v.all, 2 * n);
        if (search.labeling(
            v.store,
            new SimpleSelect<>(decisions, new SmallestDomain<>(), new IndomainMin<>()),
            v.cost)) {
          optimum = search.getCostValue();
        }
      }
      assertEquals(
          best == Integer.MAX_VALUE ? null : Integer.valueOf(best),
          optimum,
          "instance " + t + " filtering " + filtering + ": " + describe(in));
    }
  }

  /**
   * Pruning by the assignment bound fixed the last successors, but the tour costs and the cost were
   * not revised again, so the search stopped with cost 14..15 and reported 14 as the optimum.
   */
  @Test
  void costIsFixedWhenTheAssignmentBoundFixesTheLastSuccessors() {
    int n = 4;
    Instance in =
        new Instance(
            n,
            1,
            1,
            wideNext(n),
            new int[][] {{0, 1}, {1}, {1, 2}, {-1, 0, 1, 2}},
            new int[][] {{4, 0, 2, 4}, {5, 2, 0, 4}, {2, 3, 1, 4}, {3, 0, 0, 5}},
            new int[][] {{9, 10}},
            range(-4000, 4000));
    Variables v = post(in, true, 0);
    assertTrue(v.store.consistency());
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    assertTrue(
        search.labeling(
            v.store,
            new SimpleSelect<>(
                Arrays.copyOf(v.all, 2 * n), new SmallestDomain<>(), new IndomainMin<>()),
            v.cost));
    // the only solution: tour 0 -> 2 -> 1 -> 0 of length 10, node 3 left out at cost 5
    assertEquals(15, search.getCostValue());
  }

  private static int[][] wideNext(int n) {
    int[][] next = new int[n][];
    for (int i = 0; i < n; i++) {
      next[i] = range(1, n);
    }
    return next;
  }

  @Test
  void twoToursAgreeWithADecompositionOnLargerInstances() {
    // two tours from depots 0 and 1, each at most `limit` long, visiting at least `visits` nodes
    // with the least total length: the same optimum as a decomposition with element constraints
    Random random = new Random(63);
    for (int t = 0; t < 8; t++) {
      int n = 8 + random.nextInt(2);
      int[][] costs = randomCosts(random, n);
      for (int i = 0; i < n; i++) {
        costs[i][i] = 0;
        for (int j = 0; j < n; j++) {
          costs[i][j] = Math.abs(costs[i][j]);
        }
      }
      int visits = 4 + random.nextInt(n - 4);
      assertEquals(optimum(n, costs, visits, false), optimum(n, costs, visits, true), "t " + t);
    }
  }

  private static int optimum(int n, int[][] costs, int visits, boolean withConstraint) {
    Store store = new Store();
    IntVar[] x = new IntVar[n];
    IntVar[] t = new IntVar[n];
    IntVar[] arc = new IntVar[n];
    IntVar[] out = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 1, n);
      t[i] = new IntVar(store, "t" + i, i < 2 ? i + 1 : 0, i < 2 ? i + 1 : 2);
      arc[i] = new IntVar(store, "a" + i, 0, 1000);
      store.impose(new ElementInteger(x[i], costs[i], arc[i], 0));
      out[i] = new IntVar(store, "o" + i, 0, 1);
      store.impose(new Reified(new XeqC(x[i], i + 1), out[i]));
    }
    for (int i = 0; i < n; i++) {
      // decomposition of the tours: x[i] = i iff t[i] = 0, and t[x[i]] = t[i]
      store.impose(new Reified(new XeqC(t[i], 0), out[i]));
      store.impose(new org.jacop.constraints.ElementVariable(x[i], t, t[i]));
    }
    store.impose(new Alldistinct(x));
    store.impose(new org.jacop.constraints.SumInt(out, "<=", new IntVar(store, 0, n - visits)));
    IntVar cost = new IntVar(store, "cost", 0, 100000);
    IntVar[] tc = {new IntVar(store, "c1", 0, 100000), new IntVar(store, "c2", 0, 100000)};
    if (withConstraint) {
      store.impose(new WeightedSubcircuits(x, t, costs, tc, cost));
    } else {
      // each tour is one circuit: Subcircuit on each tour's successors, the others pointing to
      // themselves
      for (int tv = 1; tv <= 2; tv++) {
        IntVar[] y = new IntVar[n];
        for (int i = 0; i < n; i++) {
          y[i] = new IntVar(store, "y" + tv + "_" + i, 1, n);
          IntVar in = new IntVar(store, 0, 1);
          store.impose(new Reified(new XeqC(t[i], tv), in));
          store.impose(
              new org.jacop.constraints.IfThenElse(
                  new XeqC(in, 1),
                  new org.jacop.constraints.XeqY(y[i], x[i]),
                  new XeqC(y[i], i + 1)));
        }
        store.impose(new org.jacop.constraints.Subcircuit(y));
      }
      int[] ones = new int[n + 1];
      Arrays.fill(ones, 1);
      ones[n] = -1;
      IntVar[] all = Arrays.copyOf(arc, n + 1);
      all[n] = cost;
      store.impose(new SumWeight(all, ones, 0));
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    IntVar[] decisions = Arrays.copyOf(x, 2 * n);
    System.arraycopy(t, 0, decisions, n, n);
    assertTrue(
        search.labeling(
            store,
            new SimpleSelect<>(decisions, new SmallestDomain<>(), new IndomainMin<>()),
            cost));
    return search.getCostValue();
  }

  @Test
  void steinerBoundLimitsTheCostOfEachTour() {
    // tour 1 holds nodes 0 and 1, which are 100 apart: it costs at least 200, while the
    // assignment pairs each of them with a cheap neighbour
    int[][] costs = {
      {0, 100, 2, 100},
      {100, 0, 100, 2},
      {2, 100, 0, 100},
      {100, 2, 100, 0}
    };
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    IntVar[] t = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 4);
      t[i] = new IntVar(store, "t" + i, i < 2 ? 1 : 0, i < 2 ? 1 : 2);
    }
    IntVar[] tc = {new IntVar(store, "c1", 0, 300), new IntVar(store, "c2", 0, 300)};
    IntVar cost = new IntVar(store, "cost", 0, 1000);
    store.impose(new WeightedSubcircuits(x, t, costs, tc, cost));
    assertTrue(store.consistency());
    assertEquals(200, tc[0].min());
    assertEquals(200, cost.min());
  }

  @Test
  void aPathMustCloseWhenNoOtherNodeCanJoinItsTour() {
    // x0 = 2, x1 = 3 is a path 0-1-2 of tour 1, and node 3 cannot be in tour 1
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, 2, 2),
      new IntVar(store, 3, 3),
      new IntVar(store, 1, 4),
      new IntVar(store, 1, 4)
    };
    IntVar[] t = {
      new IntVar(store, 1, 1),
      new IntVar(store, 0, 2),
      new IntVar(store, 0, 2),
      new IntVar(store, 0, 0)
    };
    IntVar[] tc = {new IntVar(store, -100, 100), new IntVar(store, -100, 100)};
    IntVar cost = new IntVar(store, -100, 100);
    store.impose(new WeightedSubcircuits(x, t, new int[4][4], tc, cost));
    assertTrue(store.consistency());
    assertEquals(1, x[2].value());
    assertEquals(1, t[2].value());
  }

  @Test
  void twoCircuitsCannotShareATour() {
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, 2, 2),
      new IntVar(store, 1, 1),
      new IntVar(store, 4, 4),
      new IntVar(store, 3, 3)
    };
    IntVar[] t = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      t[i] = new IntVar(store, 1, 1);
    }
    IntVar[] tc = {new IntVar(store, -100, 100)};
    IntVar cost = new IntVar(store, -100, 100);
    store.impose(new WeightedSubcircuits(x, t, new int[4][4], tc, cost));
    assertFalse(store.consistency());
  }

  @Test
  void argumentsAreValidated() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 1, 2), new IntVar(store, 1, 2)};
    IntVar[] t = {new IntVar(store, 0, 1), new IntVar(store, 0, 1)};
    IntVar[] tc = {new IntVar(store, 0, 10)};
    IntVar cost = new IntVar(store, 0, 10);
    assertThatThrownBy(() -> new WeightedSubcircuits(x, t, new int[][] {{0, 1}}, tc, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new WeightedSubcircuits(x, new IntVar[] {t[0]}, new int[2][2], tc, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new WeightedSubcircuits(x, t, new int[2][2], new IntVar[0], cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new WeightedSubcircuits(x, x, new int[2][2], tc, cost))
        .isInstanceOf(IllegalArgumentException.class);
  }
}
