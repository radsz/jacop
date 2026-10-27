/*
 * SubcircuitCostTest.java
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
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SubcircuitCost;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XneqC;
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

/** Brute-force checks of {@link SubcircuitCost} against an enumeration of the subcircuits. */
class SubcircuitCostTest {

  // -Dsubcircuitcost.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("subcircuitcost.instances", 1000);

  /** A random instance: successor domains (values offset..offset+n-1), costs, cost domain. */
  private record Instance(int n, int offset, int[][] domains, int[][] costs, int[] costDomain) {

    /** Every subcircuit in the domains, as its successors (from 0) followed by its cost. */
    List<int[]> subcircuits() {
      List<int[]> result = new ArrayList<>();
      enumerate(0, new int[n], new boolean[n], result);
      return result;
    }

    private void enumerate(int i, int[] next, boolean[] usedValue, List<int[]> result) {
      if (i == n) {
        if (isSubcircuit(next)) {
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

  // a permutation is a subcircuit when the nodes that do not point to themselves form one cycle
  private static boolean isSubcircuit(int[] next) {
    int n = next.length;
    int start = -1;
    int inCircuit = 0;
    for (int k = 0; k < n; k++) {
      if (next[k] != k) {
        start = k;
        inCircuit++;
      }
    }
    if (start < 0) {
      return true;
    }
    int node = start;
    int steps = 0;
    do {
      node = next[node];
      steps++;
    } while (node != start && steps <= n);
    return steps == inCircuit;
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

  /**
   * Random costs: uniform, possibly negative, or rounded Euclidean distances (where the Steiner
   * bound is strongest). The diagonal is 0, or a random penalty for leaving the node out.
   */
  private static int[][] randomCosts(Random random, int n, int range, int shift) {
    int[][] costs = new int[n][n];
    boolean euclidean = random.nextBoolean();
    int[][] xy = new int[n][2];
    for (int[] p : xy) {
      p[0] = random.nextInt(range + 1);
      p[1] = random.nextInt(range + 1);
    }
    int diagonal = random.nextInt(3);
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i == j) {
          costs[i][j] = diagonal == 0 ? 0 : random.nextInt(range) + (diagonal == 1 ? 0 : shift);
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

  private static Instance randomInstance(Random random, int n, boolean oneBased) {
    int offset = oneBased ? 1 : random.nextInt(5) - 2;
    int range = 1 + random.nextInt(random.nextBoolean() ? 10 : 200);
    int shift = random.nextInt(4) == 0 ? -range / 2 : 0;
    int[][] costs = randomCosts(random, n, range, shift);
    int[][] domains = new int[n][];
    double density = 0.4 + 0.6 * random.nextDouble();
    double self = random.nextDouble();
    for (int i = 0; i < n; i++) {
      List<Integer> values = new ArrayList<>();
      // values outside offset..offset+n-1 are left to the constraint to remove
      for (int v = offset - 1; v <= offset + n; v++) {
        boolean keep = v == offset + i ? random.nextDouble() < self : random.nextDouble() < density;
        if (keep) {
          values.add(v);
        }
      }
      if (values.isEmpty()) {
        values.add(offset + i);
      }
      domains[i] = values.stream().mapToInt(Integer::intValue).toArray();
    }
    List<int[]> all = new Instance(n, offset, domains, costs, null).subcircuits();
    return new Instance(n, offset, domains, costs, costDomain(random, all, range, shift, n));
  }

  // A cost domain near the cheapest or the dearest subcircuit, often with holes, so that the
  // bounds and the reduced costs prune. Without subcircuits any small domain does.
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

  private record Variables(Store store, IntVar[] x, IntVar cost) {}

  /** Filtering variants: 0 both (the default), 1 assignment only, 2 Steiner only, 3 none. */
  private static Variables post(Instance in, boolean withSubcircuit, int filtering) {
    Store store = new Store();
    IntVar[] x = new IntVar[in.n];
    for (int i = 0; i < in.n; i++) {
      x[i] = new IntVar(store, "x" + i, domainOf(in.domains[i]));
    }
    IntVar cost = new IntVar(store, "cost", domainOf(in.costDomain));
    SubcircuitCost c = new SubcircuitCost(x, in.costs, cost, in.offset);
    switch (filtering) {
      case 1 -> c.setFiltering(true, false);
      case 2 -> c.setFiltering(false, true);
      case 3 -> c.setFiltering(false, false);
      default -> {
        // the default: both relaxations
      }
    }
    if (withSubcircuit) {
      store.impose(new Subcircuit(x));
    }
    store.impose(c);
    return new Variables(store, x, cost);
  }

  private static TreeSet<String> solve(Variables v, Random random) {
    TreeSet<String> found = new TreeSet<>();
    if (!v.store.consistency()) {
      return found;
    }
    IntVar[] vars = Arrays.copyOf(v.x, v.x.length + 1);
    vars[v.x.length] = v.cost;
    List<IntVar> shuffled = new ArrayList<>(Arrays.asList(vars));
    Collections.shuffle(shuffled, random);
    IntVar[] order = shuffled.toArray(new IntVar[0]);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(order, null, new IndomainRandom<>(random.nextInt()));
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);
    if (search.labeling(v.store, select)) {
      int count = search.getSolutionListener().solutionsNo();
      for (int s = 1; s <= count; s++) {
        Domain[] sol = search.getSolutionListener().getSolution(s);
        int[] t = new int[vars.length];
        for (int k = 0; k < vars.length; k++) {
          // solutions are recorded in the order of the labelled variables
          t[k] = ((IntDomain) sol[shuffled.indexOf(vars[k])]).value();
        }
        found.add(Arrays.toString(t));
      }
    }
    return found;
  }

  private static TreeSet<String> expected(Instance in) {
    TreeSet<String> result = new TreeSet<>();
    for (int[] c : in.subcircuits()) {
      int[] t = Arrays.copyOf(c, in.n + 1);
      for (int k = 0; k < in.n; k++) {
        t[k] += in.offset;
      }
      result.add(Arrays.toString(t));
    }
    return result;
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
  void allSolutionsMatchBruteForce() {
    Random random = new Random(51);
    for (int t = 0; t < INSTANCES; t++) {
      // Subcircuit numbers the nodes from 1; without it the search enumerates the assignments
      boolean withSubcircuit = random.nextInt(4) != 0;
      int n = 1 + random.nextInt(withSubcircuit ? 7 : 6);
      Instance in = randomInstance(random, n, withSubcircuit);
      int filtering = random.nextInt(4);
      TreeSet<String> found = solve(post(in, withSubcircuit, filtering), random);
      assertEquals(
          expected(in),
          found,
          "instance "
              + t
              + " subcircuit "
              + withSubcircuit
              + " filtering "
              + filtering
              + ": "
              + describe(in));
    }
  }

  private static int[] wide() {
    int[] values = new int[8001];
    for (int k = 0; k < values.length; k++) {
      values[k] = k - 4000;
    }
    return values;
  }

  // minimisation with the cost bound tightened after every solution, as branch and bound does
  @Test
  void minimumCostMatchesBruteForce() {
    Random random = new Random(52);
    for (int t = 0; t < 400; t++) {
      int n = 3 + random.nextInt(6);
      Instance in = randomInstance(random, n, true);
      in = new Instance(in.n, in.offset, in.domains, in.costs, wide());
      int best = Integer.MAX_VALUE;
      for (int[] c : in.subcircuits()) {
        best = Math.min(best, c[n]);
      }
      int filtering = random.nextInt(3);
      Integer optimum = optimumWith(in, filtering);
      String what = "instance " + t + " filtering " + filtering + ": " + describe(in);
      assertEquals(best == Integer.MAX_VALUE ? null : Integer.valueOf(best), optimum, what);
    }
  }

  private static Integer optimumWith(Instance in, int filtering) {
    Variables v = post(in, true, filtering);
    if (!v.store.consistency()) {
      return null;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(v.x, new SmallestDomain<>(), new IndomainMin<>());
    return search.labeling(v.store, select, v.cost) ? search.getCostValue() : null;
  }

  @Test
  void decompositionAgreesOnLargerInstances() {
    // the same optimum as Subcircuit with a sum of element costs, on instances too large to
    // enumerate, with a depot that must be visited and a quota of visited nodes
    Random random = new Random(53);
    for (int t = 0; t < 12; t++) {
      int n = 9 + random.nextInt(3);
      int range = 100;
      int[][] costs = randomCosts(random, n, range, 0);
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = java.util.stream.IntStream.rangeClosed(1, n).toArray();
      }
      Instance in = new Instance(n, 1, domains, costs, wide());
      int visits = 2 + random.nextInt(n - 2);
      assertEquals(
          optimum(in, visits, false), optimum(in, visits, true), describe(in) + " " + visits);
    }
  }

  // the cheapest subcircuit through node 0 that leaves at most n - visits nodes out
  private static int optimum(Instance in, int visits, boolean withCost) {
    Store store = new Store();
    int n = in.n;
    IntVar[] x = new IntVar[n];
    IntVar[] arc = new IntVar[n];
    IntVar[] out = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 1, n);
      arc[i] = new IntVar(store, "a" + i, -4000, 4000);
      store.impose(new ElementInteger(x[i], in.costs[i], arc[i], 0));
      out[i] = new IntVar(store, "o" + i, 0, 1);
      store.impose(
          new org.jacop.constraints.Reified(new org.jacop.constraints.XeqC(x[i], i + 1), out[i]));
    }
    store.impose(new XneqC(x[0], 1));
    store.impose(new org.jacop.constraints.SumInt(out, "<=", new IntVar(store, 0, n - visits)));
    store.impose(new Subcircuit(x));
    IntVar cost = new IntVar(store, "cost", -100000, 100000);
    int[] ones = new int[n + 1];
    Arrays.fill(ones, 1);
    ones[n] = -1;
    IntVar[] all = Arrays.copyOf(arc, n + 1);
    all[n] = cost;
    store.impose(new SumWeight(all, ones, 0));
    if (withCost) {
      store.impose(new SubcircuitCost(x, in.costs, cost));
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    assertTrue(
        search.labeling(
            store, new SimpleSelect<>(x, new SmallestDomain<>(), new IndomainMin<>()), cost));
    return search.getCostValue();
  }

  @Test
  void steinerBoundIsStrongerThanTheAssignmentWhenRequiredNodesAreFarApart() {
    // two required nodes 0 and 1 far apart, each with a cheap optional neighbour: the assignment
    // pairs each required node with its neighbour (cost 8), while a subcircuit through both
    // needs the long arcs between them (cost at least 200)
    int[][] costs = {
      {0, 100, 2, 100},
      {100, 0, 100, 2},
      {2, 100, 0, 100},
      {100, 2, 100, 0}
    };
    for (int filtering = 1; filtering <= 2; filtering++) {
      Store store = new Store();
      IntVar[] x = new IntVar[4];
      for (int i = 0; i < 4; i++) {
        x[i] = new IntVar(store, "x" + i, 1, 4);
      }
      store.impose(new XneqC(x[0], 1));
      store.impose(new XneqC(x[1], 2));
      IntVar cost = new IntVar(store, "cost", 0, 300);
      SubcircuitCost c = new SubcircuitCost(x, costs, cost);
      c.setFiltering(filtering == 1, filtering == 2);
      store.impose(c);
      assertTrue(store.consistency());
      assertEquals(filtering == 1 ? 8 : 200, cost.min(), "filtering " + filtering);
    }
  }

  @Test
  void costIncludesThePenaltiesOfTheNodesLeftOut() {
    int[][] costs = {{0, 3, 5}, {2, 7, 4}, {6, 1, 9}};
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 2, 2), new IntVar(store, 1, 1), new IntVar(store, 3, 3)};
    IntVar cost = new IntVar(store, -100, 100);
    store.impose(new SubcircuitCost(x, costs, cost));
    assertTrue(store.consistency());
    assertEquals(3 + 2 + 9, cost.value());

    // two cycles are not a subcircuit, even without the Subcircuit constraint
    Store store2 = new Store();
    IntVar[] y = {
      new IntVar(store2, 2, 2),
      new IntVar(store2, 1, 1),
      new IntVar(store2, 4, 4),
      new IntVar(store2, 3, 3)
    };
    IntVar cost2 = new IntVar(store2, -100, 100);
    store2.impose(new SubcircuitCost(y, new int[4][4], cost2));
    assertFalse(store2.consistency());
  }

  @Test
  void leavingANodeOutIsPrunedWhenItsPenaltyIsTooHigh() {
    // leaving node 2 out costs 50; visiting it costs at most 3 more than the tour 0-1-0
    int[][] costs = {{0, 1, 2}, {1, 0, 2}, {2, 2, 50}};
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 3);
    }
    store.impose(new XneqC(x[0], 1));
    IntVar cost = new IntVar(store, "cost", 0, 10);
    store.impose(new SubcircuitCost(x, costs, cost));
    assertTrue(store.consistency());
    assertFalse(x[2].domain.contains(3), x[2].toString());
  }

  @Test
  void argumentsAreValidated() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 1, 2), new IntVar(store, 1, 2)};
    IntVar cost = new IntVar(store, 0, 10);
    assertThatThrownBy(() -> new SubcircuitCost(x, new int[][] {{0, 1}}, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new SubcircuitCost(x, new int[][] {{0, 1}, {1}}, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new SubcircuitCost(new IntVar[] {x[0], x[0]}, new int[2][2], cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new SubcircuitCost(new IntVar[] {x[0], cost}, new int[2][2], cost))
        .isInstanceOf(IllegalArgumentException.class);
  }
}
