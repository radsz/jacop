/*
 * GlobalCardinalityTest.java
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
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiConsumer;
import java.util.stream.IntStream;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.GCC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.Indomain;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Checks the global cardinality constraints GCC, CountValues and CountValuesBounds against a
 * brute-force enumeration of all assignments and against a decomposition into one Count (or
 * CountBounds) constraint per value. GCC implements the bound consistency algorithm of Katriel and
 * Thiel, so it is also checked that every bound left by its fixpoint has a support.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class GlobalCardinalityTest {

  /**
   * A random model over a pool of variables. The counted variables and the counters are taken from
   * the pool, so a variable may be both counted and a counter, and a counter may count two values.
   * Side constraints relate pool variables, so the constraint is also woken during search by
   * changes it did not cause.
   *
   * @param domains the domains of the pool variables.
   * @param x the pool index of each counted variable.
   * @param counters the pool index of the counter of each value, empty if there are no counters.
   * @param values the counted values.
   * @param side side constraints {kind, a, b, constant} over pool indices.
   */
  private record Model(int[][] domains, int[] x, int[] counters, int[] values, int[][] side) {

    Model withoutSide() {
      return new Model(domains, x, counters, values, new int[0][]);
    }

    @Override
    public String toString() {
      return "domains="
          + Arrays.deepToString(domains)
          + " x="
          + Arrays.toString(x)
          + " counters="
          + Arrays.toString(counters)
          + " values="
          + Arrays.toString(values)
          + " side="
          + Arrays.deepToString(side);
    }
  }

  /** Imposes a global cardinality constraint of the model on the pool variables. */
  private interface Imposer {
    void impose(Store store, IntVar[] pool, Model model);
  }

  @Test
  void gccFindsTheSolutionsOfBruteForce() {
    Random random = new Random(1);
    for (int trial = 0; trial < 3000; trial++) {
      assertSolutions(
          gccModel(random, false, false), trial, random, GlobalCardinalityTest::imposeGcc);
    }
  }

  @Test
  void gccWithZeroCountersFindsTheSolutionsOfBruteForce() {
    // a counter for every value between the smallest and the largest value of the variables; the
    // counters of the values no variable can take must be zero
    Random random = new Random(2);
    for (int trial = 0; trial < 2000; trial++) {
      assertSolutions(
          gccModel(random, true, false), trial, random, GlobalCardinalityTest::imposeGcc);
    }
  }

  @Test
  void gccWithSharedVariablesFindsTheSolutionsOfBruteForce() {
    Random random = new Random(3);
    for (int trial = 0; trial < 3000; trial++) {
      assertSolutions(
          gccModel(random, false, true), trial, random, GlobalCardinalityTest::imposeGcc);
    }
  }

  @Test
  void gccHasTheSolutionCountOfTheDecomposition() {
    // larger instances than brute force can enumerate, compared with a Count per value
    Random random = new Random(4);
    for (int trial = 0; trial < 150; trial++) {
      int n = 5 + random.nextInt(4);
      int lo = random.nextInt(5) - 2;
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = randomSubset(random, lo, lo + 2 + random.nextInt(3), random.nextInt(40));
      }
      int[] values = union(domains, range(0, n - 1));
      Model model = withCounters(random, domains, values, side(random, n + values.length, 4));
      long expected = countSolutions(model, 0, 0, GlobalCardinalityTest::imposeCountDecomposition);
      int seed = random.nextInt();
      assertThat(countSolutions(model, 1, seed, GlobalCardinalityTest::imposeGcc))
          .as("trial %d %s seed %d", trial, model, seed)
          .isEqualTo(expected);
    }
  }

  @Test
  void gccAndCountValuesSolveMagicSequences() {
    // x[i] is the number of occurrences of i in x, so x is counted and counts at the same time
    long[] expected = {0, 0, 0, 2, 1, 0, 1, 1, 1, 1, 1, 1};
    for (int n = 1; n <= expected.length; n++) {
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = range(0, n - 1);
      }
      Model model =
          new Model(domains, range(0, n - 1), range(0, n - 1), range(0, n - 1), new int[0][]);
      assertThat(countSolutions(model, 0, 0, GlobalCardinalityTest::imposeGcc))
          .as("GCC n=%d", n)
          .isEqualTo(expected[n - 1]);
      assertThat(countSolutions(model, 0, 0, GlobalCardinalityTest::imposeCountValues))
          .as("CountValues n=%d", n)
          .isEqualTo(expected[n - 1]);
    }
  }

  @Test
  void gccIsBoundsConsistent() {
    // After propagation the minimum and the maximum of every variable must have a support in which
    // every counted variable takes a counted value between its bounds and every counter a value
    // between its bounds.
    Random random = new Random(5);
    for (int trial = 0; trial < 3000; trial++) {
      Model model = gccModel(random, false, false).withoutSide();
      Store store = new Store();
      IntVar[] pool = pool(store, model);
      imposeGcc(store, pool, model);
      if (!store.consistency()) {
        assertThat(bruteForce(model)).as("trial %d %s", trial, model).isEmpty();
        continue;
      }
      int[][] bounds = new int[pool.length][];
      for (int i = 0; i < pool.length; i++) {
        bounds[i] = new int[] {pool[i].min(), pool[i].max()};
      }
      for (int i = 0; i < pool.length; i++) {
        for (int bound : bounds[i]) {
          assertThat(hasBoundSupport(model, bounds, i, bound))
              .as(
                  "trial %d %s: bound %d of p%d in %s",
                  trial, model, bound, i, Arrays.deepToString(bounds))
              .isTrue();
        }
      }
    }
  }

  @Test
  void gccRemainsCorrectWhenSearchedTwice() {
    // a second search over the same store starts from the state restored by the first one
    Random random = new Random(6);
    for (int trial = 0; trial < 500; trial++) {
      Model model = gccModel(random, random.nextBoolean(), false).withoutSide();
      Set<List<Integer>> expected = bruteForce(model);
      Store store = new Store();
      IntVar[] pool = pool(store, model);
      imposeGcc(store, pool, model);
      if (!store.consistency()) {
        assertThat(expected).as("trial %d %s", trial, model).isEmpty();
        continue;
      }
      for (int round = 0; round < 2; round++) {
        assertThat(search(store, pool, random.nextInt(6), random.nextInt()))
            .as("trial %d round %d %s", trial, round, model)
            .isEqualTo(expected);
      }
    }
  }

  @Test
  void countValuesFindsTheSolutionsOfBruteForce() {
    Random random = new Random(7);
    for (int trial = 0; trial < 3000; trial++) {
      assertSolutions(
          countValuesModel(random), trial, random, GlobalCardinalityTest::imposeCountValues);
    }
  }

  @Test
  void countValuesHasTheSolutionCountOfTheDecomposition() {
    Random random = new Random(8);
    for (int trial = 0; trial < 3000; trial++) {
      Model model = countValuesModel(random);
      long expected = countSolutions(model, 0, 0, GlobalCardinalityTest::imposeCountDecomposition);
      int seed = random.nextInt();
      assertThat(countSolutions(model, 1, seed, GlobalCardinalityTest::imposeCountValues))
          .as("trial %d %s seed %d", trial, model, seed)
          .isEqualTo(expected);
    }
  }

  /**
   * Bit set domains whose bounds hold many counted values, so that CountValues walks the runs of
   * the domains instead of looking up every counted value.
   */
  @Test
  void countValuesOnWideDomainsHasTheSolutionCountOfTheDecomposition() {
    Random random = new Random(10);
    for (int trial = 0; trial < 200; trial++) {
      int n = 1 + random.nextInt(3);
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = randomSubset(random, 0, 199, 93 + random.nextInt(6));
      }
      int[] values =
          random.nextBoolean()
              ? range(random.nextInt(40), 100 + random.nextInt(100))
              : randomSubset(random, -10, 209, random.nextInt(60));
      // counters that mostly allow every count, so that most models have solutions
      int m = values.length;
      int[][] all = Arrays.copyOf(domains, n + m);
      int[] counters = new int[m];
      for (int j = 0; j < m; j++) {
        all[n + j] = random.nextInt(20) == 0 ? new int[] {random.nextInt(n + 1)} : range(0, n);
        counters[j] = n + j;
      }
      Model model = new Model(all, range(0, n - 1), counters, values, side(random, n, 1));
      long expected =
          countSolutions(
              model, 0, 0, (store, pool) -> imposeCountDecomposition(store, pool, model), true);
      int seed = random.nextInt();
      assertThat(
              countSolutions(
                  model,
                  1 + random.nextInt(5),
                  seed,
                  (store, pool) -> imposeCountValues(store, pool, model),
                  true))
          .as("trial %d %s seed %d", trial, model, seed)
          .isEqualTo(expected);
    }
  }

  @Test
  void countValuesBoundsHasTheSolutionCountOfTheDecomposition() {
    Random random = new Random(9);
    for (int trial = 0; trial < 3000; trial++) {
      Model withCounters = countValuesModel(random);
      int n = withCounters.x().length;
      int m = withCounters.values().length;
      // the counters are replaced by fixed bounds, so the pool holds just the counted variables
      Model model =
          new Model(
              Arrays.copyOf(withCounters.domains(), n),
              withCounters.x(),
              new int[0],
              withCounters.values(),
              side(random, n, random.nextInt(3)));
      int[] lb = new int[m];
      int[] ub = new int[m];
      for (int j = 0; j < m; j++) {
        lb[j] = random.nextBoolean() ? 0 : random.nextInt(n + 1);
        ub[j] = lb[j] + random.nextInt(n + 1 - lb[j]);
      }
      long expected =
          countSolutions(
              model,
              0,
              0,
              (store, pool) -> {
                for (int j = 0; j < m; j++) {
                  store.impose(
                      new CountBounds(select(pool, model.x()), model.values()[j], lb[j], ub[j]));
                }
              });
      int seed = random.nextInt();
      assertThat(
              countSolutions(
                  model,
                  1,
                  seed,
                  (store, pool) ->
                      store.impose(
                          new CountValuesBounds(select(pool, model.x()), lb, ub, model.values()))))
          .as(
              "trial %d %s lb=%s ub=%s seed %d",
              trial, model, Arrays.toString(lb), Arrays.toString(ub), seed)
          .isEqualTo(expected);
    }
  }

  @Test
  void countValuesRejectsRepeatedValues() {
    // A repeated value made the scan move a variable twice to the decided part of the list (an
    // ArrayIndexOutOfBoundsException or a lost variable) and made the counters add up to more than
    // the number of variables.
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x0", 0, 2), new IntVar(store, "x1", 0, 2)};
    IntVar[] c = {new IntVar(store, "c0", 0, 2), new IntVar(store, "c1", 0, 2)};

    assertThatThrownBy(() -> new CountValues(x, c, new int[] {1, 1}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new CountValuesBounds(x, new int[] {0, 0}, new int[] {2, 2}, new int[] {1, 1}))
        .isInstanceOf(IllegalArgumentException.class);
  }

  // ------------------------------------------------------------------ models

  /**
   * A random GCC model. Without sharing, the pool holds the counted variables followed by one
   * counter per value. With sharing, counted variables and counters are drawn from one pool, and
   * only singleton variables may be counted more than once.
   */
  private static Model gccModel(Random random, boolean zeroCounters, boolean shared) {
    int n = 1 + random.nextInt(5);
    if (!shared) {
      int lo = random.nextInt(5) - 2;
      int hi = lo + random.nextInt(4);
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = randomSubset(random, lo, hi, random.nextInt(50));
      }
      int[] values = union(domains, range(0, n - 1));
      if (zeroCounters) {
        values = range(values[0], values[values.length - 1]);
      }
      return withCounters(random, domains, values, side(random, n, random.nextInt(3)));
    }

    int poolSize = 2 + random.nextInt(4);
    int[][] domains = new int[poolSize][];
    for (int i = 0; i < poolSize; i++) {
      domains[i] =
          random.nextInt(5) == 0
              ? new int[] {random.nextInt(4)}
              : randomSubset(random, 0, 3, random.nextInt(40));
    }
    List<Integer> x = new ArrayList<>();
    for (int k = 0; k < n; k++) {
      int i = random.nextInt(poolSize);
      if (domains[i].length == 1 || !x.contains(i)) {
        x.add(i);
      }
    }
    int[] xs = x.stream().mapToInt(Integer::intValue).toArray();
    int[] values = union(domains, xs);
    int[] counters = new int[values.length];
    for (int j = 0; j < counters.length; j++) {
      counters[j] = random.nextInt(poolSize);
    }
    return new Model(domains, xs, counters, values, side(random, poolSize, random.nextInt(2)));
  }

  /** A model counting the given values of the variables, with one new counter per value. */
  private static Model withCounters(Random random, int[][] domains, int[] values, int[][] side) {
    int n = domains.length;
    int m = values.length;
    int[][] all = Arrays.copyOf(domains, n + m);
    int[] counters = new int[m];
    for (int j = 0; j < m; j++) {
      int min = random.nextInt(3) == 0 ? random.nextInt(n + 1) : 0;
      int max = random.nextInt(3) == 0 ? min + random.nextInt(n + 1 - min) : n;
      all[n + j] = randomSubset(random, min, max, random.nextInt(3) == 0 ? 30 : 0);
      counters[j] = n + j;
    }
    return new Model(all, range(0, n - 1), counters, values, side);
  }

  /** A CountValues model: the values need not be sorted and need not occur in any domain. */
  private static Model countValuesModel(Random random) {
    int n = 1 + random.nextInt(5);
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] = randomSubset(random, 0, 4, random.nextInt(50));
    }
    List<Integer> candidates = new ArrayList<>();
    for (int v = -1; v <= 5; v++) {
      candidates.add(v);
    }
    Collections.shuffle(candidates, random);
    int[] values =
        candidates.subList(0, 1 + random.nextInt(4)).stream().mapToInt(Integer::intValue).toArray();
    return withCounters(
        random, domains, values, side(random, n + values.length, random.nextInt(3)));
  }

  /** Random side constraints over the pool indices below size. */
  private static int[][] side(Random random, int size, int count) {
    if (size < 2) {
      return new int[0][];
    }
    int[][] side = new int[count][];
    for (int k = 0; k < count; k++) {
      int a = random.nextInt(size);
      int b = (a + 1 + random.nextInt(size - 1)) % size;
      side[k] = new int[] {random.nextInt(3), a, b, random.nextInt(7)};
    }
    return side;
  }

  // ------------------------------------------------------------- constraints

  private static void imposeGcc(Store store, IntVar[] pool, Model model) {
    store.impose(new GCC(select(pool, model.x()), select(pool, model.counters())));
  }

  private static void imposeCountValues(Store store, IntVar[] pool, Model model) {
    store.impose(
        new CountValues(select(pool, model.x()), select(pool, model.counters()), model.values()));
  }

  private static void imposeCountDecomposition(Store store, IntVar[] pool, Model model) {
    IntVar[] x = select(pool, model.x());
    for (int j = 0; j < model.values().length; j++) {
      store.impose(new Count(x, pool[model.counters()[j]], model.values()[j]));
    }
  }

  // ------------------------------------------------------------------ solving

  private static void assertSolutions(Model model, int trial, Random random, Imposer imposer) {
    Set<List<Integer>> expected = bruteForce(model);
    int order = random.nextInt(6);
    int seed = random.nextInt();
    Store store = new Store();
    IntVar[] pool = pool(store, model);
    imposer.impose(store, pool, model);
    imposeSide(store, pool, model);
    Set<List<Integer>> found = store.consistency() ? search(store, pool, order, seed) : Set.of();
    assertThat(found)
        .as("trial %d %s order %d seed %d", trial, model, order, seed)
        .isEqualTo(expected);
  }

  private static long countSolutions(
      Model model, int order, int seed, BiConsumer<Store, IntVar[]> imposer) {
    return countSolutions(model, order, seed, imposer, false);
  }

  private static long countSolutions(
      Model model, int order, int seed, BiConsumer<Store, IntVar[]> imposer, boolean bitSets) {
    Store store = new Store();
    IntVar[] pool = pool(store, model, bitSets);
    imposer.accept(store, pool);
    imposeSide(store, pool, model);
    if (!store.consistency()) {
      return 0;
    }
    return search(store, pool, order, seed).size();
  }

  private static long countSolutions(Model model, int order, int seed, Imposer imposer) {
    return countSolutions(model, order, seed, (store, pool) -> imposer.impose(store, pool, model));
  }

  private static IntVar[] pool(Store store, Model model) {
    return pool(store, model, false);
  }

  /**
   * The pool variables, with interval domains, or with bit set domains (from the bounds, as the
   * FlatZinc front end creates them) when bitSets is true.
   */
  private static IntVar[] pool(Store store, Model model, boolean bitSets) {
    IntVar[] pool = new IntVar[model.domains().length];
    for (int i = 0; i < pool.length; i++) {
      int[] values = model.domains()[i];
      IntervalDomain domain = new IntervalDomain();
      for (int v : values) {
        domain.unionAdapt(v, v);
      }
      if (bitSets) {
        pool[i] = new IntVar(store, "p" + i, values[0], values[values.length - 1]);
        pool[i].domain.in(store.level, pool[i], domain);
      } else {
        pool[i] = new IntVar(store, "p" + i, domain);
      }
    }
    return pool;
  }

  private static void imposeSide(Store store, IntVar[] pool, Model model) {
    for (int[] s : model.side()) {
      switch (s[0]) {
        case 0 -> store.impose(new XneqY(pool[s[1]], pool[s[2]]));
        case 1 -> store.impose(new XltY(pool[s[1]], pool[s[2]]));
        default -> store.impose(new XplusYeqC(pool[s[1]], pool[s[2]], s[3]));
      }
    }
  }

  /**
   * Finds all solutions over the pool. Even orders label the pool in its order, odd orders in a
   * random order; the value order is minimum, maximum or random.
   */
  private static Set<List<Integer>> search(Store store, IntVar[] pool, int order, int seed) {
    List<IntVar> vars = new ArrayList<>(Arrays.asList(pool));
    if (order % 2 == 1) {
      Collections.shuffle(vars, new Random(seed));
    }
    Indomain<IntVar> indomain =
        switch (order / 2 % 3) {
          case 0 -> new IndomainMin<>();
          case 1 -> new IndomainMax<>();
          default -> new IndomainRandom<>(seed);
        };
    List<List<Integer>> found = new ArrayList<>();
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setAssignSolution(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            found.add(Arrays.stream(pool).map(IntVar::value).toList());
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(vars.toArray(new IntVar[0]), null, indomain));
    Set<List<Integer>> solutions = new HashSet<>(found);
    assertThat(found).as("no solution is found twice").hasSameSizeAs(solutions);
    return solutions;
  }

  // ------------------------------------------------------------- brute force

  private static Set<List<Integer>> bruteForce(Model model) {
    Set<List<Integer>> solutions = new HashSet<>();
    enumerate(model, model.domains(), new int[model.domains().length], 0, -1, 0, solutions);
    return solutions;
  }

  /**
   * Whether some solution has the variable equal to value when every variable ranges over its
   * bounds, and a counted variable only over the counted values between its bounds.
   */
  private static boolean hasBoundSupport(Model model, int[][] bounds, int variable, int value) {
    Set<Integer> counted = new HashSet<>();
    for (int v : model.values()) {
      counted.add(v);
    }
    Set<Integer> xs = new HashSet<>();
    for (int i : model.x()) {
      xs.add(i);
    }
    int[][] domains = new int[bounds.length][];
    for (int i = 0; i < bounds.length; i++) {
      boolean isCounted = xs.contains(i);
      domains[i] =
          Arrays.stream(range(bounds[i][0], bounds[i][1]))
              .filter(v -> !isCounted || counted.contains(v))
              .toArray();
    }
    Set<List<Integer>> solutions = new HashSet<>();
    enumerate(model, domains, new int[domains.length], 0, variable, value, solutions);
    return !solutions.isEmpty();
  }

  /** Enumerates the solutions; with a fixed variable it stops at the first one. */
  private static void enumerate(
      Model model,
      int[][] domains,
      int[] assignment,
      int i,
      int fixed,
      int fixedValue,
      Set<List<Integer>> solutions) {
    if (i == assignment.length) {
      if (satisfies(model, assignment)) {
        solutions.add(Arrays.stream(assignment).boxed().toList());
      }
      return;
    }
    for (int v : domains[i]) {
      if (i == fixed && v != fixedValue) {
        continue;
      }
      assignment[i] = v;
      enumerate(model, domains, assignment, i + 1, fixed, fixedValue, solutions);
      if (fixed >= 0 && !solutions.isEmpty()) {
        return;
      }
    }
  }

  private static boolean satisfies(Model model, int[] assignment) {
    if (model.counters().length > 0) {
      for (int j = 0; j < model.values().length; j++) {
        int count = 0;
        for (int i : model.x()) {
          if (assignment[i] == model.values()[j]) {
            count++;
          }
        }
        if (assignment[model.counters()[j]] != count) {
          return false;
        }
      }
    }
    for (int[] s : model.side()) {
      int a = assignment[s[1]];
      int b = assignment[s[2]];
      boolean holds =
          switch (s[0]) {
            case 0 -> a != b;
            case 1 -> a < b;
            default -> a + b == s[3];
          };
      if (!holds) {
        return false;
      }
    }
    return true;
  }

  // ----------------------------------------------------------------- helpers

  private static IntVar[] select(IntVar[] pool, int[] indexes) {
    return Arrays.stream(indexes).mapToObj(i -> pool[i]).toArray(IntVar[]::new);
  }

  /** The sorted union of the domains at the given indexes. */
  private static int[] union(int[][] domains, int[] indexes) {
    Set<Integer> union = new TreeSet<>();
    for (int i : indexes) {
      for (int v : domains[i]) {
        union.add(v);
      }
    }
    return union.stream().mapToInt(Integer::intValue).toArray();
  }

  private static int[] range(int lo, int hi) {
    return IntStream.rangeClosed(lo, hi).toArray();
  }

  /** A random non-empty subset of lo..hi, leaving out each value with the given percentage. */
  private static int[] randomSubset(Random random, int lo, int hi, int holePercent) {
    List<Integer> values = new ArrayList<>();
    for (int v = lo; v <= hi; v++) {
      if (random.nextInt(100) >= holePercent) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(lo + random.nextInt(hi - lo + 1));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }
}
