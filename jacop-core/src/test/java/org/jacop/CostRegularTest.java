/*
 * CostRegularTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2026 Radoslaw Szymanek
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
import static org.assertj.core.api.Assertions.assertThatThrownBy;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.jacop.constraints.regular.CostRegular;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link CostRegular}: all solutions of random instances against a brute-force enumeration
 * and against the decomposition, the pruning reached at the root, minimization and argument checks.
 */
class CostRegularTest {

  /** A random cost automaton and the domains of its variables, the last one being the cost. */
  private record Instance(
      int n,
      int[][] delta,
      int firstValue,
      int[] finals,
      int[][][] costs,
      int[][] domains,
      boolean layered) {

    Integer costOf(int[] word) {
      int q = 0;
      int sum = 0;
      for (int i = 0; i < n; i++) {
        int j = word[i] - firstValue;
        if (j < 0 || j >= delta[q].length || delta[q][j] < 0) {
          return null;
        }
        sum += costs[i][q][j];
        q = delta[q][j];
      }
      for (int f : finals) {
        if (f == q) {
          return sum;
        }
      }
      return null;
    }

    CostRegular constraint(IntVar[] x) {
      IntVar[] word = Arrays.copyOf(x, n);
      if (layered) {
        return new CostRegular(word, delta, firstValue, 0, finals, costs, x[n]);
      }
      return new CostRegular(
          word,
          delta,
          firstValue,
          0,
          finals,
          n == 0 ? new int[delta.length][delta[0].length] : costs[0],
          x[n]);
    }

    @Override
    public String toString() {
      return "delta="
          + Arrays.deepToString(delta)
          + " firstValue="
          + firstValue
          + " finals="
          + Arrays.toString(finals)
          + " costs="
          + Arrays.deepToString(costs)
          + " domains="
          + Arrays.deepToString(domains);
    }
  }

  private static Instance randomInstance(Random random, int maxN, boolean wideCost) {
    return randomInstance(random, 0, maxN, 4, 4, wideCost);
  }

  private static Instance randomInstance(
      Random random, int minN, int maxN, int maxStates, int maxSymbols, boolean wideCost) {
    int n = minN + random.nextInt(maxN - minN + 1);
    int states = 1 + random.nextInt(maxStates);
    int symbols = 2 + random.nextInt(maxSymbols - 1);
    int firstValue = random.nextInt(4) - 1;
    int[][] delta = RandomAutomata.transitions(random, states, symbols);
    int[] finals = RandomAutomata.finals(random, states);
    boolean layered = random.nextBoolean();
    int[][][] costs = new int[n][][];
    int[][] shared = RandomAutomata.costs(random, states, symbols, 7);
    for (int i = 0; i < n; i++) {
      costs[i] = layered ? RandomAutomata.costs(random, states, symbols, 7) : shared;
    }
    int[][] domains = new int[n + 1][];
    for (int i = 0; i < n; i++) {
      domains[i] = RandomAutomata.subset(random, firstValue - 1, firstValue + symbols);
    }
    domains[n] =
        wideCost ? RandomAutomata.range(-1000, 1000) : RandomAutomata.subset(random, -6, 3 * n + 4);
    return new Instance(n, delta, firstValue, finals, costs, domains, layered);
  }

  private static Set<List<Integer>> bruteForce(Instance instance) {
    Set<List<Integer>> solutions = new HashSet<>();
    enumerate(instance, new int[instance.n()], 0, solutions);
    return solutions;
  }

  private static void enumerate(
      Instance instance, int[] word, int i, Set<List<Integer>> solutions) {
    if (i == word.length) {
      Integer c = instance.costOf(word);
      if (c != null && Arrays.binarySearch(instance.domains()[instance.n()], c) >= 0) {
        List<Integer> solution = new ArrayList<>(Arrays.stream(word).boxed().toList());
        solution.add(c);
        solutions.add(solution);
      }
      return;
    }
    for (int v : instance.domains()[i]) {
      word[i] = v;
      enumerate(instance, word, i + 1, solutions);
    }
  }

  /** All solutions with the constraint or its decomposition, the cost labelled first or last. */
  private static Set<List<Integer>> solveAll(
      Instance instance, boolean decomposition, boolean costFirst, int valueOrder, int seed) {
    Store store = new Store();
    IntVar[] x = RandomAutomata.variables(store, instance.domains());
    CostRegular c = instance.constraint(x);
    if (decomposition) {
      store.imposeDecomposition(c);
    } else {
      store.impose(c);
    }
    IntVar[] order = x.clone();
    if (costFirst) {
      order[0] = x[x.length - 1];
      System.arraycopy(x, 0, order, 1, x.length - 1);
    }
    return RandomAutomata.solveAll(
        store, x, order, () -> c.satisfied() || decomposition, valueOrder, seed);
  }

  @Test
  void allSolutionsMatchBruteForceAndDecomposition() {
    Random random = new Random(20261020);
    for (int trial = 0; trial < 1500; trial++) {
      Instance instance = randomInstance(random, 6, random.nextInt(5) == 0);
      Set<List<Integer>> expected = bruteForce(instance);
      boolean costFirst = random.nextBoolean();
      int valueOrder = trial % 3;
      int seed = random.nextInt();
      assertThat(solveAll(instance, false, costFirst, valueOrder, seed))
          .as("trial %d native %s", trial, instance)
          .isEqualTo(expected);
      if (trial % 5 == 0) {
        assertThat(solveAll(instance, true, costFirst, valueOrder, seed))
            .as("trial %d decomposition %s", trial, instance)
            .isEqualTo(expected);
      }
    }
  }

  /** Longer words with more states exercise the incremental updates deeper in the search. */
  @Test
  void longerWordsMatchBruteForce() {
    Random random = new Random(5);
    for (int trial = 0; trial < 300; trial++) {
      Instance instance = randomInstance(random, 7, 9, 6, 3, false);
      Set<List<Integer>> expected = bruteForce(instance);
      assertThat(solveAll(instance, false, random.nextBoolean(), trial % 3, random.nextInt()))
          .as("trial %d native %s", trial, instance)
          .isEqualTo(expected);
    }
  }

  /**
   * Random dives of decisions on the word and on the cost, with backtracking: after every
   * propagation the domains must be the same as those reached by a new constraint posted on the
   * current domains, so the incremental updates reach the same fixpoint as a computation from
   * scratch.
   */
  @Test
  void incrementalPropagationEqualsFromScratch() {
    Random random = new Random(17);
    for (int trial = 0; trial < 400; trial++) {
      Instance instance = randomInstance(random, 4, 10, 6, 4, random.nextBoolean());
      Store store = new Store();
      IntVar[] x = RandomAutomata.variables(store, instance.domains());
      store.impose(instance.constraint(x));
      if (!store.consistency()) {
        continue;
      }
      for (int step = 0; step < 40; step++) {
        RandomAutomata.randomBacktrack(store, random);
        store.setLevel(store.level + 1);
        IntVar v = x[random.nextInt(x.length)];
        if (v.singleton()) {
          continue;
        }
        boolean consistent;
        try {
          RandomAutomata.randomDecision(store, v, random);
          consistent = store.consistency();
        } catch (FailException e) {
          consistent = false;
        }
        String where = "trial " + trial + " step " + step + " " + instance;
        int[][] current = new int[x.length][];
        if (consistent) {
          for (int i = 0; i < x.length; i++) {
            current[i] = values(x[i].dom()).stream().mapToInt(Integer::intValue).toArray();
          }
        }
        if (!consistent) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          continue;
        }
        Store fresh = new Store();
        IntVar[] y = RandomAutomata.variables(fresh, current);
        fresh.impose(instance.constraint(y));
        assertTrue(fresh.consistency(), where);
        for (int i = 0; i < x.length; i++) {
          assertEquals(values(y[i].dom()), values(x[i].dom()), where + " variable " + i);
        }
      }
    }
  }

  /**
   * With the cost unconstrained, the constraint reaches generalized arc consistency on the word and
   * narrows the cost to the cheapest and the most expensive accepted word.
   */
  @Test
  void rootPruningWithFreeCostIsExact() {
    Random random = new Random(7);
    for (int trial = 0; trial < 1000; trial++) {
      Instance instance = randomInstance(random, 6, true);
      Set<List<Integer>> solutions = bruteForce(instance);
      Store store = new Store();
      IntVar[] x = RandomAutomata.variables(store, instance.domains());
      store.impose(instance.constraint(x));
      boolean consistent = store.consistency();
      assertEquals(!solutions.isEmpty(), consistent, "trial " + trial + " " + instance);
      if (!consistent) {
        continue;
      }
      for (int i = 0; i < x.length; i++) {
        Set<Integer> projection = new TreeSet<>();
        for (List<Integer> s : solutions) {
          projection.add(s.get(i));
        }
        if (i < instance.n()) {
          assertEquals(
              projection, values(x[i].dom()), "trial " + trial + " x" + i + " " + instance);
        } else {
          assertEquals(
              ((TreeSet<Integer>) projection).first(),
              x[i].min(),
              "trial " + trial + " " + instance);
          assertEquals(
              ((TreeSet<Integer>) projection).last(),
              x[i].max(),
              "trial " + trial + " " + instance);
        }
      }
    }
  }

  /** Every value left at the root lies on an accepted word whose cost is within the cost bounds. */
  @Test
  void rootPruningRespectsCostBounds() {
    Random random = new Random(11);
    for (int trial = 0; trial < 1000; trial++) {
      Instance instance = randomInstance(random, 6, false);
      Store store = new Store();
      IntVar[] x = RandomAutomata.variables(store, instance.domains());
      // the cost as an interval, so a word within the bounds supports its values
      IntVar costVar = x[instance.n()];
      int lo = costVar.min();
      int hi = costVar.max();
      instance.domains()[instance.n()] = RandomAutomata.range(lo, hi);
      x[instance.n()] = new IntVar(store, "c", lo, hi);
      store.impose(instance.constraint(x));
      Set<List<Integer>> solutions = bruteForce(instance);
      boolean consistent = store.consistency();
      assertEquals(!solutions.isEmpty(), consistent, "trial " + trial + " " + instance);
      if (!consistent) {
        continue;
      }
      // values of the word: the shortest-and-longest path filter keeps a value when some word with
      // it is not too expensive and some word with it is not too cheap; every solution value stays
      for (List<Integer> s : solutions) {
        for (int i = 0; i < x.length; i++) {
          assertTrue(x[i].dom().contains(s.get(i)), "trial " + trial + " " + instance);
        }
      }
      // the cost bounds are those of some accepted words
      int min = solutions.stream().mapToInt(s -> s.get(instance.n())).min().getAsInt();
      int max = solutions.stream().mapToInt(s -> s.get(instance.n())).max().getAsInt();
      assertTrue(x[instance.n()].min() <= min && x[instance.n()].max() >= max);
    }
  }

  @Test
  void minimizesCost() {
    Random random = new Random(3);
    for (int trial = 0; trial < 300; trial++) {
      Instance instance = randomInstance(random, 7, true);
      if (instance.n() == 0) {
        continue;
      }
      Set<List<Integer>> solutions = bruteForce(instance);
      Store store = new Store();
      IntVar[] x = RandomAutomata.variables(store, instance.domains());
      store.impose(instance.constraint(x));
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean result =
          store.consistency()
              && search.labeling(
                  store,
                  new SimpleSelect<>(Arrays.copyOf(x, instance.n()), null, new IndomainMax<>()),
                  x[instance.n()]);
      assertEquals(!solutions.isEmpty(), result, "trial " + trial + " " + instance);
      if (result) {
        int min = solutions.stream().mapToInt(s -> s.get(instance.n())).min().getAsInt();
        assertEquals(min, search.getCostValue(), "trial " + trial + " " + instance);
      }
    }
  }

  /** Shifts D, E, N, O (1..4): a night is followed by a night or a day off, costs per shift. */
  @Test
  void prunesByCost() {
    int[][] delta = {
      {0, 0, 1, 0}, // after D, E or O
      {-1, -1, 1, 0} // after N
    };
    int[][] costs = {
      {3, 4, 6, 0},
      {3, 4, 5, 0}
    };
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 4);
    }
    IntVar cost = new IntVar(store, "cost", 0, 5);
    store.impose(new CostRegular(x, delta, 1, 0, new int[] {0, 1}, costs, cost));
    assertTrue(store.consistency());
    // a night costs 6 after a day shift or a day off, too much for 5
    for (IntVar v : x) {
      assertEquals(Set.of(1, 2, 4), values(v.dom()), v.toString());
    }
    // the bounds are path costs: no word costs 5, but paths of cost 5 and more remain
    assertEquals(0, cost.min());
    assertEquals(5, cost.max());

    store.setLevel(store.level + 1);
    x[0].domain.in(store.level, x[0], 2, 2);
    assertTrue(store.consistency());
    // an evening costs 4, so the other days are off
    for (int i = 1; i < 4; i++) {
      assertTrue(x[i].singleton(4), x[i].toString());
    }
    assertTrue(cost.singleton(4));
    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
    assertEquals(Set.of(1, 2, 4), values(x[1].dom()));
    assertEquals(0, cost.min());

    // the restored graph propagates again after backtracking
    store.setLevel(store.level + 1);
    x[3].domain.in(store.level, x[3], 1, 1);
    assertTrue(store.consistency());
    assertTrue(x[0].singleton(4) && x[1].singleton(4) && x[2].singleton(4));
    assertTrue(cost.singleton(3));
  }

  @Test
  void failsWithoutAcceptedWord() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x0", 0, 1), new IntVar(store, "x1", 0, 1)};
    IntVar cost = new IntVar(store, "cost", -10, 10);
    // only words of length 1 are accepted
    int[][] delta = {{1, 1}, {-1, -1}};
    store.impose(new CostRegular(x, delta, 0, 0, new int[] {1}, new int[2][2], cost));
    assertFalse(store.consistency());
  }

  @Test
  void emptyWord() {
    Store store = new Store();
    IntVar cost = new IntVar(store, "cost", -10, 10);
    store.impose(
        new CostRegular(
            new IntVar[0], new int[][] {{0}}, 0, 0, new int[] {0}, new int[][] {{1}}, cost));
    assertTrue(store.consistency());
    assertTrue(cost.singleton(0));

    Store rejecting = new Store();
    IntVar c = new IntVar(rejecting, "cost", -10, 10);
    rejecting.impose(
        new CostRegular(new IntVar[0], new int[][] {{0}}, 0, 0, new int[0], new int[][] {{1}}, c));
    assertFalse(rejecting.consistency());
  }

  @Test
  void largeCostsDoNotOverflow() {
    Store store = new Store();
    IntVar[] x = new IntVar[5];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    IntVar cost = new IntVar(store, "cost", IntDomain.MIN_INT, IntDomain.MAX_INT);
    int big = IntDomain.MAX_INT;
    store.impose(
        new CostRegular(
            x, new int[][] {{0, 0}}, 0, 0, new int[] {0}, new int[][] {{0, big}}, cost));
    assertTrue(store.consistency());
    assertEquals(0, cost.min());
    assertEquals(IntDomain.MAX_INT, cost.max());
    store.setLevel(1);
    x[0].domain.in(1, x[0], 1, 1);
    x[1].domain.in(1, x[1], 1, 1);
    assertFalse(store.consistency());
  }

  @Test
  void rejectsInvalidArguments() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x0", 0, 1)};
    IntVar cost = new IntVar(store, "cost", 0, 10);
    int[][] delta = {{0, 0}};
    int[][] costs = {{0, 0}};
    assertThatThrownBy(() -> new CostRegular(x, delta, 0, 1, new int[] {0}, costs, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new CostRegular(x, delta, 0, 0, new int[] {2}, costs, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new CostRegular(x, new int[][] {{0, 3}}, 0, 0, new int[] {0}, costs, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new CostRegular(x, delta, 0, 0, new int[] {0}, new int[][] {{0}}, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new CostRegular(x, delta, 0, 0, new int[] {0}, new int[][][] {costs, costs}, cost))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new CostRegular(x, delta, 0, 0, new int[] {0}, costs, x[0]))
        .isInstanceOf(IllegalArgumentException.class);
  }

  private static Set<Integer> values(IntDomain d) {
    Set<Integer> result = new TreeSet<>();
    for (var e = d.valueEnumeration(); e.hasMoreElements(); ) {
      result.add(e.nextElement());
    }
    return result;
  }
}
