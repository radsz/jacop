/*
 * CircuitCostTest.java
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
import java.util.TreeSet;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.CircuitCost;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XneqC;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.junit.jupiter.api.Test;

/** Brute-force checks of {@link CircuitCost} against an enumeration of the circuits. */
class CircuitCostTest {

  // -Dcircuitcost.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("circuitcost.instances", 1000);

  /** A random instance: successor domains (values offset..offset+n-1), costs, cost domain. */
  private record Instance(int n, int offset, int[][] domains, int[][] costs, int[] costDomain) {

    /** The cost of every circuit in the domains, as successor arrays mapped to their cost. */
    List<int[]> circuits() {
      List<int[]> result = new ArrayList<>();
      int[] next = new int[n];
      boolean[] usedValue = new boolean[n];
      enumerate(0, next, usedValue, result);
      return result;
    }

    private void enumerate(int i, int[] next, boolean[] usedValue, List<int[]> result) {
      if (i == n) {
        int node = 0;
        int steps = 0;
        do {
          node = next[node];
          steps++;
        } while (node != 0 && steps <= n);
        if (steps == n && node == 0) {
          int[] solution = Arrays.copyOf(next, n + 1);
          long sum = 0;
          for (int k = 0; k < n; k++) {
            sum += costs[k][next[k]];
          }
          solution[n] = (int) sum;
          if (costDomain == null || contains(costDomain, solution[n])) {
            result.add(solution);
          }
        }
        return;
      }
      for (int value : domains[i]) {
        int j = value - offset;
        if (j >= 0 && j < n && !usedValue[j]) {
          usedValue[j] = true;
          next[i] = j;
          enumerate(i + 1, next, usedValue, result);
          usedValue[j] = false;
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

  private static Instance randomInstance(Random random, int n, boolean symmetric) {
    int offset = random.nextInt(5) - 2;
    int[][] costs = new int[n][n];
    int range = 1 + random.nextInt(random.nextBoolean() ? 10 : 200);
    int shift = random.nextInt(4) == 0 ? -range / 2 : 0;
    for (int i = 0; i < n; i++) {
      for (int j = symmetric ? i : 0; j < n; j++) {
        costs[i][j] = random.nextInt(range) + shift;
        if (symmetric) {
          costs[j][i] = costs[i][j];
        }
      }
    }
    int[][] domains = new int[n][];
    double density = 0.4 + 0.6 * random.nextDouble();
    for (int i = 0; i < n; i++) {
      List<Integer> values = new ArrayList<>();
      // values outside offset..offset+n-1 and the self loop are left to the constraint to remove
      for (int v = offset - 1; v <= offset + n; v++) {
        if (random.nextDouble() < density || v == offset + (i + 1) % n && random.nextBoolean()) {
          values.add(v);
        }
      }
      if (values.isEmpty()) {
        values.add(offset + (i + 1) % n);
      }
      domains[i] = values.stream().mapToInt(Integer::intValue).toArray();
    }
    List<int[]> all = new Instance(n, offset, domains, costs, null).circuits();
    return new Instance(n, offset, domains, costs, costDomain(random, all, range, shift, n));
  }

  // A cost domain near the cheapest or the dearest circuit, often with holes, so that the bounds
  // and the reduced costs prune. Without circuits any small domain does.
  private static int[] costDomain(Random random, List<int[]> all, int range, int shift, int n) {
    int lo;
    int hi;
    if (all.isEmpty()) {
      lo = n * shift;
      hi = lo + random.nextInt(n * range + 1);
    } else {
      int min = Integer.MAX_VALUE;
      int max = Integer.MIN_VALUE;
      for (int[] c : all) {
        min = Math.min(min, c[n]);
        max = Math.max(max, c[n]);
      }
      int spread = max - min;
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

  private record Variables(Store store, IntVar[] x, IntVar cost, CircuitCost constraint) {}

  /** Filtering variants: 0 default, 1 assignment only, 2 1-tree only, 3 both, 4 none. */
  private static Variables post(Instance in, boolean withCircuit, int filtering) {
    Store store = new Store();
    IntVar[] x = new IntVar[in.n];
    for (int i = 0; i < in.n; i++) {
      x[i] = new IntVar(store, "x" + i, domainOf(in.domains[i]));
    }
    IntVar cost = new IntVar(store, "cost", domainOf(in.costDomain));
    CircuitCost c = new CircuitCost(x, in.costs, cost, in.offset);
    switch (filtering) {
      case 1 -> c.setFiltering(true, false);
      case 2 -> c.setFiltering(false, true);
      case 3 -> c.setFiltering(true, true);
      case 4 -> c.setFiltering(false, false);
      default -> {
        // the default: assignment, and the 1-tree for symmetric costs
      }
    }
    if (withCircuit) {
      store.impose(new Circuit(x, in.offset));
    }
    store.impose(c);
    return new Variables(store, x, cost, c);
  }

  private static TreeSet<String> solve(Variables v, Random random) {
    TreeSet<String> found = new TreeSet<>();
    if (!v.store.consistency()) {
      return found;
    }
    IntVar[] vars = Arrays.copyOf(v.x, v.x.length + 1);
    vars[v.x.length] = v.cost;
    List<IntVar> shuffled = new ArrayList<>(Arrays.asList(vars));
    java.util.Collections.shuffle(shuffled, random);
    IntVar[] order = shuffled.toArray(new IntVar[0]);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(order, null, new IndomainRandom<>(random.nextInt()));
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);
    search.setSolutionListener(search.getSolutionListener());
    if (search.labeling(v.store, select)) {
      int count = search.getSolutionListener().solutionsNo();
      for (int s = 1; s <= count; s++) {
        org.jacop.core.Domain[] sol = search.getSolutionListener().getSolution(s);
        int[] t = new int[vars.length];
        for (int k = 0; k < vars.length; k++) {
          // solutions are recorded in the order of the labelled variables
          int pos = shuffled.indexOf(vars[k]);
          t[k] = ((IntDomain) sol[pos]).value();
        }
        found.add(key(t, v.x.length, 0));
      }
    }
    return found;
  }

  private static String key(int[] t, int n, int offsetOfSuccessors) {
    int[] copy = Arrays.copyOf(t, n + 1);
    for (int k = 0; k < n; k++) {
      copy[k] -= offsetOfSuccessors;
    }
    return Arrays.toString(copy);
  }

  private static TreeSet<String> expected(Instance in) {
    TreeSet<String> result = new TreeSet<>();
    for (int[] c : in.circuits()) {
      int[] t = Arrays.copyOf(c, in.n + 1);
      for (int k = 0; k < in.n; k++) {
        t[k] += in.offset;
      }
      result.add(Arrays.toString(t));
    }
    return result;
  }

  private static void checkAllSolutions(long seed, int instances, int maxN, boolean symmetric) {
    Random random = new Random(seed);
    for (int t = 0; t < instances; t++) {
      boolean withCircuit = random.nextInt(4) != 0;
      // without Circuit the search enumerates the assignments, so keep those instances smaller
      int n = 2 + random.nextInt((withCircuit ? maxN : maxN - 1) - 1);
      Instance in = randomInstance(random, n, symmetric);
      TreeSet<String> expected = expected(in);
      int filtering = random.nextInt(5);
      TreeSet<String> found = solve(post(in, withCircuit, filtering), random);
      assertEquals(
          expected,
          found,
          "instance "
              + t
              + " seed "
              + seed
              + " circuit "
              + withCircuit
              + " filtering "
              + filtering
              + ": "
              + describe(in));
    }
  }

  private static String describe(Instance in) {
    return "n="
        + in.n
        + " offset="
        + in.offset
        + " domains="
        + Arrays.deepToString(in.domains)
        + " costs="
        + Arrays.deepToString(in.costs)
        + " cost="
        + Arrays.toString(in.costDomain);
  }

  @Test
  void allSolutionsAsymmetricMatchBruteForce() {
    checkAllSolutions(11, INSTANCES, 7, false);
  }

  @Test
  void allSolutionsSymmetricMatchBruteForce() {
    checkAllSolutions(12, INSTANCES, 7, true);
  }

  // minimisation with the cost bound tightened after every solution, as branch and bound does
  private static void checkOptimum(long seed, int instances, int minN, int maxN, boolean sym) {
    Random random = new Random(seed);
    for (int t = 0; t < instances; t++) {
      int n = minN + random.nextInt(maxN - minN + 1);
      Instance in = randomInstance(random, n, sym);
      in = new Instance(in.n, in.offset, in.domains, in.costs, wide());
      int best = Integer.MAX_VALUE;
      for (int[] c : in.circuits()) {
        best = Math.min(best, c[n]);
      }
      int filtering = random.nextInt(4);
      Variables v = post(in, true, filtering);
      boolean consistent = v.store.consistency();
      Integer optimum = null;
      if (consistent) {
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        SelectChoicePoint<IntVar> select =
            new SimpleSelect<>(v.x, new SmallestDomain<>(), new IndomainMin<>());
        if (search.labeling(v.store, select, v.cost)) {
          optimum = search.getCostValue();
        }
      }
      String what = "instance " + t + " filtering " + filtering + ": " + describe(in);
      if (best == Integer.MAX_VALUE) {
        assertEquals(null, optimum, what);
      } else {
        assertEquals(Integer.valueOf(best), optimum, what);
      }
    }
  }

  private static int[] wide() {
    int[] values = new int[4001];
    for (int k = 0; k < values.length; k++) {
      values[k] = k - 2000;
    }
    return values;
  }

  @Test
  void minimumCostMatchesBruteForce() {
    checkOptimum(21, 300, 4, 9, false);
    checkOptimum(22, 300, 4, 9, true);
  }

  @Test
  void rootBoundsAreTheAssignmentAndCircuitBoundsOnACompleteGraph() {
    // the cheapest circuit of this symmetric instance is 1-2-3-4-5-1 of cost 5; its assignment
    // relaxation picks two 2-cycles and the 1-tree reaches the optimum
    int n = 5;
    int[][] costs = new int[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        int d = Math.abs(i - j);
        costs[i][j] = i == j ? 0 : d == 1 || d == n - 1 ? 1 : 10;
      }
    }
    Store store = new Store();
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 1, n);
    }
    IntVar cost = new IntVar(store, "cost", 0, 1000);
    store.impose(new CircuitCost(x, costs, cost));
    assertTrue(store.consistency());
    assertEquals(5, cost.min());
    assertEquals(50, cost.max());

    // with the cost at most 5 only the two directions of the ring remain
    cost.domain.inMax(store.level, cost, 5);
    assertTrue(store.consistency());
    for (int i = 0; i < n; i++) {
      assertEquals(2, x[i].getSize(), x[i].toString());
    }
  }

  @Test
  void oneTreeBoundIsCloseToTheOptimumOnEuclideanInstances() {
    // the Lagrangian penalties close most of the gap of the plain 1-tree; with the penalties left
    // at zero the bound was 10-15% below the optimum
    Random random = new Random(41);
    for (int t = 0; t < 10; t++) {
      int n = 9;
      int[][] xy = new int[n][2];
      for (int[] p : xy) {
        p[0] = random.nextInt(1000);
        p[1] = random.nextInt(1000);
      }
      int[][] costs = new int[n][n];
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
          costs[i][j] =
              (int)
                  Math.round(
                      Math.hypot((double) xy[i][0] - xy[j][0], (double) xy[i][1] - xy[j][1]));
        }
        domains[i] = java.util.stream.IntStream.rangeClosed(1, n).toArray();
      }
      int best = Integer.MAX_VALUE;
      for (int[] c : new Instance(n, 1, domains, costs, null).circuits()) {
        best = Math.min(best, c[n]);
      }
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 1, n);
      }
      IntVar cost = new IntVar(store, "cost", 0, best);
      CircuitCost c = new CircuitCost(x, costs, cost);
      c.setFiltering(false, true);
      store.impose(c);
      assertTrue(store.consistency());
      assertTrue(cost.min() >= 0.97 * best, "bound " + cost.min() + " optimum " + best);
    }
  }

  @Test
  void costIsFixedWhenTheCircuitIs() {
    int[][] costs = {{0, 3, 5}, {2, 0, 4}, {6, 1, 0}};
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 2, 2), new IntVar(store, 3, 3), new IntVar(store, 1, 1)};
    IntVar cost = new IntVar(store, -100, 100);
    store.impose(new CircuitCost(x, costs, cost));
    assertTrue(store.consistency());
    assertEquals(3 + 4 + 6, cost.value());

    // two cycles are not a circuit, even without the Circuit constraint
    Store store2 = new Store();
    IntVar[] y = {
      new IntVar(store2, 2, 2),
      new IntVar(store2, 1, 1),
      new IntVar(store2, 4, 4),
      new IntVar(store2, 3, 3)
    };
    IntVar cost2 = new IntVar(store2, -100, 100);
    int[][] costs2 = new int[4][4];
    store2.impose(new CircuitCost(y, costs2, cost2));
    assertFalse(store2.consistency());
  }

  @Test
  void singleVariableHasNoCircuit() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 1, 1)};
    IntVar cost = new IntVar(store, 0, 10);
    store.impose(new CircuitCost(x, new int[][] {{0}}, cost));
    assertFalse(store.consistency());
  }

  @Test
  void decompositionAgreesOnLargerInstances() {
    // the same optimum as Circuit with a sum of element costs, on instances too large to enumerate
    Random random = new Random(31);
    for (int t = 0; t < 12; t++) {
      int n = 10 + random.nextInt(3);
      boolean sym = t % 2 == 0;
      Instance in = randomInstance(random, n, sym);
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = new int[n];
        for (int j = 0; j < n; j++) {
          domains[i][j] = in.offset + j;
        }
      }
      in = new Instance(n, in.offset, domains, in.costs, wide());
      assertEquals(optimumByDecomposition(in), optimumWith(in), describe(in));
    }
  }

  private static int optimumWith(Instance in) {
    Variables v = post(in, true, 0);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    assertTrue(
        search.labeling(
            v.store, new SimpleSelect<>(v.x, new SmallestDomain<>(), new IndomainMin<>()), v.cost));
    return search.getCostValue();
  }

  private static int optimumByDecomposition(Instance in) {
    Store store = new Store();
    int n = in.n;
    IntVar[] x = new IntVar[n];
    IntVar[] arc = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, in.offset, in.offset + n - 1);
      store.impose(new XneqC(x[i], in.offset + i));
      int[] row = in.costs[i];
      arc[i] = new IntVar(store, "a" + i, -2000, 2000);
      store.impose(new org.jacop.constraints.ElementInteger(x[i], row, arc[i], in.offset - 1));
    }
    store.impose(new Circuit(x, in.offset));
    IntVar cost = new IntVar(store, "cost", -100000, 100000);
    int[] ones = new int[n + 1];
    Arrays.fill(ones, 1);
    ones[n] = -1;
    IntVar[] all = Arrays.copyOf(arc, n + 1);
    all[n] = cost;
    store.impose(new SumWeight(all, ones, 0));
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    Search<IntVar> s = search;
    assertTrue(
        s.labeling(
            store, new SimpleSelect<>(x, new SmallestDomain<>(), new IndomainMin<>()), cost));
    return search.getCostValue();
  }

  @Test
  void argumentsAreValidated() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 1, 2), new IntVar(store, 1, 2)};
    IntVar cost = new IntVar(store, 0, 10);
    assertThatThrownBy(() -> new CircuitCost(x, new int[][] {{0, 1}}, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new CircuitCost(x, new int[][] {{0, 1}, {1}}, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new CircuitCost(new IntVar[] {x[0], x[0]}, new int[2][2], cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new CircuitCost(new IntVar[] {x[0], cost}, new int[2][2], cost))
        .isInstanceOf(IllegalArgumentException.class);
  }
}
