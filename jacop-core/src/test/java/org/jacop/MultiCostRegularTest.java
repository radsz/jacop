/*
 * MultiCostRegularTest.java
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
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.regular.CostRegular;
import org.jacop.constraints.regular.MultiCostRegular;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link MultiCostRegular}: all solutions of random instances against a brute-force
 * enumeration and against the decomposition into one CostRegular per resource, soundness and
 * strength of the pruning in random dives, the pruning only the joint reasoning reaches, and
 * argument checks.
 */
class MultiCostRegularTest {

  /** A random automaton with costs per resource and the domains of the word and of the costs. */
  private record Instance(
      int n,
      int resources,
      int[][] delta,
      int firstValue,
      int[] finals,
      int[][][][] costs,
      int[][] domains,
      boolean layered) {

    /** The costs of the word per resource, or null if the automaton rejects it. */
    int[] costOf(int[] word) {
      int q = 0;
      int[] sum = new int[resources];
      for (int i = 0; i < n; i++) {
        int j = word[i] - firstValue;
        if (j < 0 || j >= delta[q].length || delta[q][j] < 0) {
          return null;
        }
        for (int r = 0; r < resources; r++) {
          sum[r] += costs[r][i][q][j];
        }
        q = delta[q][j];
      }
      for (int f : finals) {
        if (f == q) {
          return sum;
        }
      }
      return null;
    }

    MultiCostRegular constraint(IntVar[] x, boolean lagrangian) {
      IntVar[] word = Arrays.copyOf(x, n);
      IntVar[] cost = Arrays.copyOfRange(x, n, n + resources);
      MultiCostRegular c;
      if (layered || n == 0) {
        c = new MultiCostRegular(word, delta, firstValue, 0, finals, costs, cost);
      } else {
        int[][][] shared = new int[resources][][];
        for (int r = 0; r < resources; r++) {
          shared[r] = costs[r][0];
        }
        c = new MultiCostRegular(word, delta, firstValue, 0, finals, shared, cost);
      }
      return c.setLagrangian(lagrangian);
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

  private static Instance randomInstance(
      Random random, int minN, int maxN, int maxStates, int maxSymbols) {
    int n = minN + random.nextInt(maxN - minN + 1);
    int resources = 2 + random.nextInt(2);
    int states = 1 + random.nextInt(maxStates);
    int symbols = 2 + random.nextInt(maxSymbols - 1);
    int firstValue = random.nextInt(4) - 1;
    int[][] delta = RandomAutomata.transitions(random, states, symbols);
    int[] finals = RandomAutomata.finals(random, states);
    boolean layered = random.nextBoolean();
    int[][][][] costs = new int[resources][n][][];
    for (int r = 0; r < resources; r++) {
      int[][] shared = RandomAutomata.costs(random, states, symbols, 5);
      for (int i = 0; i < n; i++) {
        costs[r][i] = layered ? RandomAutomata.costs(random, states, symbols, 5) : shared;
      }
    }
    int[][] domains = new int[n + resources][];
    for (int i = 0; i < n; i++) {
      domains[i] = RandomAutomata.subset(random, firstValue - 1, firstValue + symbols);
    }
    for (int r = 0; r < resources; r++) {
      domains[n + r] = RandomAutomata.range(-100, 100);
    }
    Instance free = new Instance(n, resources, delta, firstValue, finals, costs, domains, layered);
    // windows inside the costs of the accepted words make the resources conflict
    Set<List<Integer>> words = bruteForce(free, domains);
    for (int r = 0; r < resources; r++) {
      int lo = 0;
      int hi = 0;
      if (!words.isEmpty()) {
        final int k = n + r;
        lo = words.stream().mapToInt(s -> s.get(k)).min().getAsInt();
        hi = words.stream().mapToInt(s -> s.get(k)).max().getAsInt();
      }
      int a = lo + random.nextInt(hi - lo + 1);
      int b = lo + random.nextInt(hi - lo + 1);
      domains[n + r] =
          random.nextInt(6) == 0
              ? RandomAutomata.range(-100, 100)
              : RandomAutomata.subset(random, Math.min(a, b) - 1, Math.max(a, b) + 1);
    }
    return new Instance(n, resources, delta, firstValue, finals, costs, domains, layered);
  }

  /** All solutions within the given domains, as the word followed by the costs. */
  private static Set<List<Integer>> bruteForce(Instance instance, int[][] domains) {
    Set<List<Integer>> solutions = new HashSet<>();
    enumerate(instance, domains, new int[instance.n()], 0, solutions);
    return solutions;
  }

  private static void enumerate(
      Instance instance, int[][] domains, int[] word, int i, Set<List<Integer>> solutions) {
    if (i == word.length) {
      int[] c = instance.costOf(word);
      if (c == null) {
        return;
      }
      for (int r = 0; r < c.length; r++) {
        if (Arrays.binarySearch(domains[instance.n() + r], c[r]) < 0) {
          return;
        }
      }
      List<Integer> solution = new ArrayList<>(Arrays.stream(word).boxed().toList());
      for (int v : c) {
        solution.add(v);
      }
      solutions.add(solution);
      return;
    }
    for (int v : domains[i]) {
      word[i] = v;
      enumerate(instance, domains, word, i + 1, solutions);
    }
  }

  /** Mode 0: joint reasoning, 1: without the relaxation, 2: decomposition. */
  private static Set<List<Integer>> solveAll(
      Instance instance, int mode, boolean costsFirst, int valueOrder, int seed) {
    Store store = new Store();
    IntVar[] x = RandomAutomata.variables(store, instance.domains());
    MultiCostRegular c = instance.constraint(x, mode == 0);
    if (mode == 2) {
      store.imposeDecomposition(c);
    } else {
      store.impose(c);
    }
    IntVar[] order = x.clone();
    if (costsFirst) {
      int n = instance.n();
      System.arraycopy(x, n, order, 0, instance.resources());
      System.arraycopy(x, 0, order, instance.resources(), n);
    }
    return RandomAutomata.solveAll(
        store, x, order, () -> c.satisfied() || mode == 2, valueOrder, seed);
  }

  @Test
  void allSolutionsMatchBruteForceAndDecomposition() {
    Random random = new Random(20261027);
    int trials = Integer.getInteger("multicostregular.trials", 1500);
    for (int trial = 0; trial < trials; trial++) {
      Instance instance = randomInstance(random, 0, 6, 4, 4);
      Set<List<Integer>> expected = bruteForce(instance, instance.domains());
      boolean costsFirst = random.nextBoolean();
      int valueOrder = trial % 3;
      int seed = random.nextInt();
      assertThat(solveAll(instance, 0, costsFirst, valueOrder, seed))
          .as("trial %d joint %s", trial, instance)
          .isEqualTo(expected);
      assertThat(solveAll(instance, 1, costsFirst, valueOrder, seed))
          .as("trial %d separate %s", trial, instance)
          .isEqualTo(expected);
      if (trial % 5 == 0) {
        assertThat(solveAll(instance, 2, costsFirst, valueOrder, seed))
            .as("trial %d decomposition %s", trial, instance)
            .isEqualTo(expected);
      }
    }
  }

  /** Longer words with more states exercise the relaxation deeper in the search. */
  @Test
  void longerWordsMatchBruteForce() {
    Random random = new Random(5);
    int trials = Integer.getInteger("multicostregular.trials", 1500) / 5;
    for (int trial = 0; trial < trials; trial++) {
      Instance instance = randomInstance(random, 7, 9, 6, 3);
      Set<List<Integer>> expected = bruteForce(instance, instance.domains());
      assertThat(solveAll(instance, 0, random.nextBoolean(), trial % 3, random.nextInt()))
          .as("trial %d joint %s", trial, instance)
          .isEqualTo(expected);
    }
  }

  /**
   * Random dives of decisions with backtracking: after every propagation no solution within the
   * domains before the decision is lost, and every domain is within the domain the decomposition
   * reaches from the same domains.
   */
  @Test
  void divesKeepSolutionsAndAreAtLeastAsStrongAsDecomposition() {
    Random random = new Random(17);
    int trials = Integer.getInteger("multicostregular.trials", 1500) / 4;
    for (int trial = 0; trial < trials; trial++) {
      Instance instance = randomInstance(random, 3, 8, 5, 3);
      Store store = new Store();
      IntVar[] x = RandomAutomata.variables(store, instance.domains());
      store.impose(instance.constraint(x, true));
      boolean rootConsistent;
      try {
        rootConsistent = store.consistency();
      } catch (FailException e) {
        rootConsistent = false;
      }
      if (!rootConsistent) {
        assertTrue(bruteForce(instance, instance.domains()).isEmpty(), "root failure " + instance);
        continue;
      }
      for (int step = 0; step < 30; step++) {
        RandomAutomata.randomBacktrack(store, random);
        store.setLevel(store.level + 1);
        IntVar v = x[random.nextInt(x.length)];
        if (v.singleton()) {
          continue;
        }
        String where = "trial " + trial + " step " + step + " " + instance;
        boolean consistent;
        int[][] decided;
        try {
          RandomAutomata.randomDecision(store, v, random);
          decided = current(x);
          consistent = store.consistency();
        } catch (FailException e) {
          decided = null;
          consistent = false;
        }
        if (decided != null) {
          Set<List<Integer>> solutions = bruteForce(instance, decided);
          if (!consistent) {
            assertTrue(solutions.isEmpty(), "wrong failure " + where);
          } else {
            for (List<Integer> s : solutions) {
              for (int i = 0; i < x.length; i++) {
                assertTrue(x[i].domain.contains(s.get(i)), "lost solution " + s + " " + where);
              }
            }
            Store reference = new Store();
            IntVar[] y = RandomAutomata.variables(reference, decided);
            reference.imposeDecomposition(instance.constraint(y, false));
            assertTrue(reference.consistency(), "decomposition failed alone " + where);
            for (int i = 0; i < x.length; i++) {
              assertTrue(
                  y[i].dom().contains(x[i].dom()), "weaker than decomposition x" + i + " " + where);
            }
          }
        }
        if (!consistent) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
      }
    }
  }

  private static int[][] current(IntVar[] x) {
    int[][] result = new int[x.length][];
    for (int i = 0; i < x.length; i++) {
      Set<Integer> values = new TreeSet<>();
      for (var e = x[i].dom().valueEnumeration(); e.hasMoreElements(); ) {
        values.add(e.nextElement());
      }
      result[i] = values.stream().mapToInt(Integer::intValue).toArray();
    }
    return result;
  }

  /**
   * Words of length 5 over {0, 1} with at most two 0s and at most two 1s: each count alone is
   * satisfiable, so separate cost regular constraints accept the root, while the relaxation proves
   * that no word exists.
   */
  @Test
  void relaxationDetectsConflictOfResources() {
    int[][] delta = {{0, 0}};
    int[][][] costs = {{{1, 0}}, {{0, 1}}};
    for (boolean lagrangian : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar[] x = new IntVar[5];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
      }
      IntVar zeros = new IntVar(store, "zeros", 0, 2);
      IntVar ones = new IntVar(store, "ones", 0, 2);
      store.impose(
          new MultiCostRegular(x, delta, 0, 0, new int[] {0}, costs, new IntVar[] {zeros, ones})
              .setLagrangian(lagrangian));
      boolean consistent;
      try {
        consistent = store.consistency();
      } catch (FailException e) {
        consistent = false;
      }
      assertThat(consistent).as("lagrangian %s", lagrangian).isEqualTo(!lagrangian);
    }
  }

  /**
   * Words of length 4 over {0, 1} with at most one 1: separate cost regular constraints leave the
   * number of 0s at 0..4, while the relaxation of the bound on the 1s raises its minimum to 3.
   */
  @Test
  void relaxationNarrowsCostBounds() {
    int[][] delta = {{0, 0}};
    int[][][] costs = {{{0, 1}}, {{1, 0}}};
    for (boolean lagrangian : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar[] x = new IntVar[4];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
      }
      IntVar ones = new IntVar(store, "ones", 0, 1);
      IntVar zeros = new IntVar(store, "zeros", 0, 4);
      store.impose(
          new MultiCostRegular(x, delta, 0, 0, new int[] {0}, costs, new IntVar[] {ones, zeros})
              .setLagrangian(lagrangian));
      assertTrue(store.consistency());
      assertThat(zeros.min()).as("lagrangian %s", lagrangian).isEqualTo(lagrangian ? 3 : 0);
    }
  }

  /** Cost regular constraints over the same word and automaton are merged, the others kept. */
  @Test
  void mergeGroupsCostRegularsOverTheSameWordAndAutomaton() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    IntVar[] y = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
      y[i] = new IntVar(store, "y" + i, 0, 1);
    }
    IntVar[] c = new IntVar[4];
    for (int k = 0; k < c.length; k++) {
      c[k] = new IntVar(store, "c" + k, 0, 3);
    }
    int[][] delta = {{0, 0}};
    Constraint other = new XneqY(x[0], y[0]);
    List<Constraint> constraints =
        List.of(
            new CostRegular(x, delta, 0, 0, new int[] {0}, new int[][] {{0, 1}}, c[0]),
            other,
            new CostRegular(y, delta, 0, 0, new int[] {0}, new int[][] {{0, 1}}, c[1]),
            new CostRegular(
                x.clone(), new int[][] {{0, 0}}, 0, 0, new int[] {0}, new int[][] {{1, 0}}, c[2]),
            new CostRegular(x, delta, 1, 0, new int[] {0}, new int[][] {{1, 0}}, c[3]));
    List<Constraint> merged = MultiCostRegular.merge(constraints);
    assertThat(merged).hasSize(4);
    assertThat(merged.get(0)).isInstanceOf(MultiCostRegular.class);
    assertThat(((MultiCostRegular) merged.get(0)).cost).containsExactly(c[0], c[2]);
    assertThat(merged.subList(1, 4)).containsExactly(other, constraints.get(2), constraints.get(4));
    assertThat(MultiCostRegular.merge(List.of(other))).containsExactly(other);
  }

  @Test
  void zeroLengthWordHasZeroCosts() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", -3, 3);
    IntVar b = new IntVar(store, "b", -3, 3);
    store.impose(
        new MultiCostRegular(
            new IntVar[0],
            new int[][] {{0}},
            0,
            0,
            new int[] {0},
            new int[][][] {{{1}}, {{2}}},
            new IntVar[] {a, b}));
    assertTrue(store.consistency());
    assertThat(a.value()).isZero();
    assertThat(b.value()).isZero();
  }

  @Test
  void argumentsAreChecked() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 0, 1), new IntVar(store, 0, 1)};
    IntVar c = new IntVar(store, 0, 10);
    int[][] delta = {{0, 0}};
    int[][][] costs = {{{0, 1}}};
    assertThatThrownBy(
            () -> new MultiCostRegular(x, delta, 0, 0, new int[] {0}, costs, new IntVar[0]))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new MultiCostRegular(x, delta, 0, 0, new int[] {0}, costs, new IntVar[] {c, c}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new MultiCostRegular(x, delta, 0, 1, new int[] {0}, costs, new IntVar[] {c}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new MultiCostRegular(x, delta, 0, 0, new int[] {1}, costs, new IntVar[] {c}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new MultiCostRegular(
                    x, delta, 0, 0, new int[] {0}, new int[][][] {{{0}}}, new IntVar[] {c}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new MultiCostRegular(x, delta, 0, 0, new int[] {0}, costs, new IntVar[] {x[0]}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThat(IntDomain.MAX_INT).isPositive();
  }
}
