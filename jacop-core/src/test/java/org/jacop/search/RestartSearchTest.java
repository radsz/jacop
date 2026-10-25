/*
 * RestartSearchTest.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with Section 7 of the GNU Affero General Public License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.search;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.Supplier;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.restart.Calculator;
import org.jacop.search.restart.ConstantCalculator;
import org.jacop.search.restart.CustomReport;
import org.jacop.search.restart.GeometricCalculator;
import org.jacop.search.restart.LinearCalculator;
import org.jacop.search.restart.LubyCalculator;
import org.jacop.search.restart.RestartSearch;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link RestartSearch}: the optimum and the satisfiability it reports on random small
 * instances against a brute-force enumeration, with restart limits small enough that most runs end
 * at their fail limit.
 */
class RestartSearchTest {

  private static final int N = 6;
  private static final int MAX_VALUE = 4;

  /** A random instance: binary constraints between six variables and a weighted-sum cost. */
  private record Instance(int[][] neq, int[][] lt, int[] weights) {

    @Override
    public String toString() {
      return "neq "
          + Arrays.deepToString(neq)
          + ", lt "
          + Arrays.deepToString(lt)
          + ", weights "
          + Arrays.toString(weights);
    }

    static Instance random(Random rnd) {
      List<int[]> neq = new ArrayList<>();
      List<int[]> lt = new ArrayList<>();
      for (int i = 0; i < N; i++) {
        for (int j = i + 1; j < N; j++) {
          int r = rnd.nextInt(10);
          if (r < 5) {
            neq.add(new int[] {i, j});
          } else if (r < 6) {
            lt.add(rnd.nextBoolean() ? new int[] {i, j} : new int[] {j, i});
          }
        }
      }
      int[] weights = new int[N];
      for (int i = 0; i < N; i++) {
        weights[i] = rnd.nextInt(7) - 2;
      }
      return new Instance(neq.toArray(new int[0][]), lt.toArray(new int[0][]), weights);
    }

    boolean satisfied(int[] x) {
      for (int[] c : neq) {
        if (x[c[0]] == x[c[1]]) {
          return false;
        }
      }
      for (int[] c : lt) {
        if (x[c[0]] >= x[c[1]]) {
          return false;
        }
      }
      return true;
    }

    int cost(int[] x) {
      int sum = 0;
      for (int i = 0; i < N; i++) {
        sum += weights[i] * x[i];
      }
      return sum;
    }

    /** The minimum cost over all solutions, or null when there is none. */
    Integer bruteForceOptimum() {
      Integer best = null;
      int[] x = new int[N];
      int total = (int) Math.pow(MAX_VALUE + 1, N);
      for (int k = 0; k < total; k++) {
        int code = k;
        for (int i = 0; i < N; i++) {
          x[i] = code % (MAX_VALUE + 1);
          code /= MAX_VALUE + 1;
        }
        if (satisfied(x) && (best == null || cost(x) < best)) {
          best = cost(x);
        }
      }
      return best;
    }
  }

  /** A model of an instance in a fresh store. */
  private static final class Model {
    final Store store = new Store();
    final IntVar[] x = new IntVar[N];
    final IntVar cost;

    Model(Instance instance) {
      for (int i = 0; i < N; i++) {
        x[i] = new IntVar(store, "x" + i, 0, MAX_VALUE);
      }
      for (int[] c : instance.neq()) {
        store.impose(new XneqY(x[c[0]], x[c[1]]));
      }
      for (int[] c : instance.lt()) {
        store.impose(new XltY(x[c[0]], x[c[1]]));
      }
      cost = new IntVar(store, "cost", -1000, 1000);
      IntVar[] terms = new IntVar[N + 1];
      int[] coefficients = new int[N + 1];
      for (int i = 0; i < N; i++) {
        terms[i] = x[i];
        coefficients[i] = instance.weights()[i];
      }
      terms[N] = cost;
      coefficients[N] = -1;
      store.impose(new LinearInt(terms, coefficients, "==", 0));
    }

    RestartSearch<IntVar> restartSearch(Calculator calculator, boolean optimize) {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      SelectChoicePoint<IntVar> select = new SimpleSelect<>(x, null, new IndomainMin<>());
      return optimize
          ? new RestartSearch<>(store, search, select, calculator, cost)
          : new RestartSearch<>(store, search, select, calculator);
    }
  }

  private static List<Supplier<Calculator>> calculators() {
    // A constant limit is left out: with a limit of a few failures it never completes a proof.
    return List.of(
        () -> new LubyCalculator(1),
        () -> new LinearCalculator(1),
        () -> new GeometricCalculator(1.5, 1));
  }

  @Test
  void optimumMatchesBruteForceWhenRunsEndAtTheirFailLimit() {
    // RestartSearch stopped after the first run that ended at its fail limit without a better
    // solution, and reported the last solution as the optimum.
    Random rnd = new Random(20261024);
    int improvedAfterARestart = 0;
    for (int k = 0; k < 150; k++) {
      Instance instance = Instance.random(rnd);
      Integer optimum = instance.bruteForceOptimum();
      for (Supplier<Calculator> calculator : calculators()) {
        Model model = new Model(instance);
        if (!model.store.consistency()) {
          assertNull(optimum, "root failure on a satisfiable instance " + instance);
          continue;
        }
        RestartSearch<IntVar> search = model.restartSearch(calculator.get(), true);
        boolean found = search.labeling();
        assertEquals(optimum != null, found, "satisfiability of " + instance);
        if (optimum != null) {
          assertEquals(optimum.intValue(), search.getIntCost(), "optimum of " + instance);
          if (search.restarts() > 0) {
            improvedAfterARestart++;
          }
        }
        assertFalse(search.restartsLimitReached());
      }
    }
    assertTrue(improvedAfterARestart > 100, "too few instances needed a restart");
  }

  @Test
  void satisfiabilityMatchesBruteForce() {
    Random rnd = new Random(7);
    for (int k = 0; k < 150; k++) {
      Instance instance = Instance.random(rnd);
      boolean satisfiable = instance.bruteForceOptimum() != null;
      for (Supplier<Calculator> calculator : calculators()) {
        Model model = new Model(instance);
        if (!model.store.consistency()) {
          assertFalse(satisfiable, "root failure on a satisfiable instance " + instance);
          continue;
        }
        // An unsatisfiable instance used to be reported as solved.
        assertEquals(
            satisfiable,
            model.restartSearch(calculator.get(), false).labeling(),
            "satisfiability of " + instance);
      }
    }
  }

  @Test
  void restartLimitMakesTheSearchIncomplete() {
    Random rnd = new Random(11);
    int limited = 0;
    for (int k = 0; k < 50; k++) {
      Instance instance = Instance.random(rnd);
      Model model = new Model(instance);
      if (!model.store.consistency()) {
        continue;
      }
      RestartSearch<IntVar> search = model.restartSearch(new LubyCalculator(1), true);
      search.setRestartsLimit(1);
      search.labeling();
      if (search.restartsLimitReached()) {
        limited++;
        Integer optimum = instance.bruteForceOptimum();
        assertTrue(optimum != null && search.getIntCost() >= optimum, "cost of " + instance);
      }
    }
    assertTrue(limited > 10, "too few instances reached the restart limit");
  }

  @Test
  void unproductiveRestartsDoNotImposeTheCostBoundAgain() {
    // Every restart that found no better solution imposed the same cost bound again, so the
    // store kept growing with the number of restarts.
    Random rnd = new Random(3);
    int checked = 0;
    for (int k = 0; k < 50; k++) {
      Model model = new Model(Instance.random(rnd));
      if (!model.store.consistency()) {
        continue;
      }
      int before = model.store.numberConstraints();
      int[] solutions = {0};
      RestartSearch<IntVar> search = model.restartSearch(new LubyCalculator(1), true);
      search.addReporter(
          new CustomReport(model.x) {
            @Override
            public void report() {
              solutions[0]++;
            }
          });
      search.labeling();
      if (search.restarts() > solutions[0]) {
        checked++;
        assertTrue(model.store.numberConstraints() - before <= solutions[0]);
      }
    }
    assertTrue(checked > 10, "too few instances had restarts without a better solution");
  }

  /** The number of failures of a search that is not restarted, with the given cost or none. */
  private static long failuresWithoutRestart(Instance instance, boolean optimize) {
    Model model = new Model(instance);
    model.store.consistency();
    long[] failures = {0};
    Calculator unlimited =
        new ConstantCalculator(Integer.MAX_VALUE) {
          @Override
          public void newLimit() {
            failures[0] = getNumberFails();
            super.newLimit();
          }
        };
    model.restartSearch(unlimited, optimize).labeling();
    return failures[0];
  }

  @Test
  void runThatEndsAtExactlyItsFailLimitCompletesTheSearch() {
    // A run that explored its whole tree with as many failures as the fail limit was taken as cut
    // by the limit, so a constant limit restarted the same finished search for ever.
    Random rnd = new Random(31);
    int checked = 0;
    for (int k = 0; k < 100; k++) {
      Instance instance = Instance.random(rnd);
      Integer optimum = instance.bruteForceOptimum();
      for (boolean optimize : new boolean[] {false, true}) {
        Model model = new Model(instance);
        if (!model.store.consistency()) {
          continue;
        }
        long failures = failuresWithoutRestart(instance, optimize);
        if (failures == 0 || (!optimize && optimum != null)) {
          continue;
        }
        RestartSearch<IntVar> search =
            model.restartSearch(new ConstantCalculator((int) failures), optimize);
        search.setRestartsLimit(5);
        boolean found = search.labeling();
        assertFalse(search.restartsLimitReached(), "restarted a finished search of " + instance);
        assertEquals(0, search.restarts(), "restarts of " + instance);
        assertEquals(optimum != null, found, "satisfiability of " + instance);
        if (optimize && optimum != null) {
          assertEquals(optimum.intValue(), search.getIntCost(), "optimum of " + instance);
        }
        checked++;
      }
    }
    assertTrue(checked > 50, "too few instances checked: " + checked);
  }

  @Test
  void runMayHaveAsManyFailuresAsItsLimit() {
    // A limit of zero refused the root node of every run, so the search restarted for ever
    // without exploring anything.
    Calculator calculator = new ConstantCalculator(0);
    assertTrue(calculator.executeAfterConsistency(true));
    assertFalse(calculator.executeAfterConsistency(false));
    assertFalse(calculator.pointsExhausted(), "a failed node is not cut by the limit");
    assertFalse(calculator.executeAfterConsistency(true));
    assertTrue(calculator.pointsExhausted());
    calculator.newLimit();
    assertFalse(calculator.pointsExhausted());
    assertTrue(calculator.executeAfterConsistency(true));
  }

  private static long[] limits(Calculator calculator, int n) {
    long[] limits = new long[n];
    for (int i = 0; i < n; i++) {
      limits[i] = calculator.getFailLimit();
      calculator.newLimit();
    }
    return limits;
  }

  @Test
  void geometricLimitsAreScaleTimesPowersOfTheBase() {
    // The power of the base was rounded down before it was scaled, so restart_geometric(1.5, 100)
    // gave 100, 100, 200, 300, 500 and a base of 1.1 kept the first limit for eight runs.
    assertArrayEquals(
        new long[] {100, 150, 225, 337, 506, 759}, limits(new GeometricCalculator(1.5, 100), 6));
    assertArrayEquals(
        new long[] {10, 11, 12, 13, 14, 16, 17, 19}, limits(new GeometricCalculator(1.1, 10), 8));
    long[] huge = limits(new GeometricCalculator(10, 1000), 40);
    for (int i = 1; i < huge.length; i++) {
      assertTrue(huge[i] >= huge[i - 1], "limits must not overflow: " + Arrays.toString(huge));
    }
    assertArrayEquals(new long[] {3, 3, 6, 3, 3, 6, 12, 3}, limits(new LubyCalculator(3), 8));
    assertArrayEquals(new long[] {2, 4, 6, 8}, limits(new LinearCalculator(2), 4));
  }
}
