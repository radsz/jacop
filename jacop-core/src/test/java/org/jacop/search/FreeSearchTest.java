/*
 * FreeSearchTest.java
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

package org.jacop.search;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.free.DomWdeg;
import org.jacop.search.free.FreeSearch;
import org.jacop.search.free.FreeSearch.Status;
import org.jacop.search.free.IndomainLastSolution;
import org.jacop.search.free.LastConflict;
import org.jacop.search.free.SearchMonitor;
import org.jacop.search.restart.Calculator;
import org.jacop.search.restart.GeometricCalculator;
import org.jacop.search.restart.LubyCalculator;
import org.junit.jupiter.api.Test;

/**
 * Differential tests of {@link FreeSearch}: on random small instances, the satisfiability, the
 * number of solutions and the optimum must match a brute-force enumeration, for several branchings
 * and restart policies, and every solution reported must satisfy the instance.
 */
class FreeSearchTest {

  private static final int N = 6;
  private static final int MAX_VALUE = 4;
  private static final int INSTANCES = 120;

  /**
   * A random instance on six variables x with values 0..4: disequalities, orderings, one
   * all-different, one linear inequality, and Booleans b[i] equal to (x[i] == eq[i]). The cost is a
   * weighted sum of x and b.
   */
  private record Instance(
      int[][] neq, int[][] lt, int[] alldiff, int[] linear, int linearBound, int[] eq, int[] w) {

    static Instance random(Random rnd) {
      List<int[]> neq = new ArrayList<>();
      List<int[]> lt = new ArrayList<>();
      for (int i = 0; i < N; i++) {
        for (int j = i + 1; j < N; j++) {
          int r = rnd.nextInt(12);
          if (r < 3) {
            neq.add(new int[] {i, j});
          } else if (r < 4) {
            lt.add(rnd.nextBoolean() ? new int[] {i, j} : new int[] {j, i});
          }
        }
      }
      int[] alldiff = new int[3];
      for (int k = 0; k < 3; k++) {
        alldiff[k] = (rnd.nextInt(N / 3)) * 3 + k;
      }
      int[] linear = new int[N];
      for (int i = 0; i < N; i++) {
        linear[i] = rnd.nextInt(5) - 1;
      }
      int[] eq = new int[N];
      int[] w = new int[2 * N];
      for (int i = 0; i < N; i++) {
        eq[i] = rnd.nextInt(MAX_VALUE + 1);
      }
      for (int i = 0; i < 2 * N; i++) {
        w[i] = rnd.nextInt(9) - 3;
      }
      return new Instance(
          neq.toArray(new int[0][]),
          lt.toArray(new int[0][]),
          alldiff,
          linear,
          rnd.nextInt(25),
          eq,
          w);
    }

    boolean satisfied(int[] x, int[] b) {
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
      for (int k = 0; k < alldiff.length; k++) {
        for (int l = k + 1; l < alldiff.length; l++) {
          if (x[alldiff[k]] == x[alldiff[l]]) {
            return false;
          }
        }
      }
      int sum = 0;
      for (int i = 0; i < N; i++) {
        sum += linear[i] * x[i];
        if (b[i] != (x[i] == eq[i] ? 1 : 0)) {
          return false;
        }
      }
      return sum <= linearBound;
    }

    int cost(int[] x, int[] b) {
      int sum = 0;
      for (int i = 0; i < N; i++) {
        sum += w[i] * x[i] + w[N + i] * b[i];
      }
      return sum;
    }

    /** Enumerates x; b is determined by x. Returns {count, min cost, max cost}. */
    int[] bruteForce() {
      int count = 0;
      int min = Integer.MAX_VALUE;
      int max = Integer.MIN_VALUE;
      int[] x = new int[N];
      int[] b = new int[N];
      int total = (int) Math.pow(MAX_VALUE + 1, N);
      for (int k = 0; k < total; k++) {
        int code = k;
        for (int i = 0; i < N; i++) {
          x[i] = code % (MAX_VALUE + 1);
          code /= MAX_VALUE + 1;
          b[i] = x[i] == eq[i] ? 1 : 0;
        }
        if (satisfied(x, b)) {
          count++;
          min = Math.min(min, cost(x, b));
          max = Math.max(max, cost(x, b));
        }
      }
      return new int[] {count, min, max};
    }
  }

  /** A model of an instance in a fresh store. */
  private static final class Model {
    final Store store = new Store();
    final IntVar[] x = new IntVar[N];
    final BooleanVar[] b = new BooleanVar[N];
    final IntVar cost;
    final Instance instance;

    Model(Instance instance) {
      this.instance = instance;
      for (int i = 0; i < N; i++) {
        x[i] = new IntVar(store, "x" + i, 0, MAX_VALUE);
        b[i] = new BooleanVar(store, "b" + i);
        store.impose(new Reified(new XeqC(x[i], instance.eq()[i]), b[i]));
      }
      for (int[] c : instance.neq()) {
        store.impose(new XneqY(x[c[0]], x[c[1]]));
      }
      for (int[] c : instance.lt()) {
        store.impose(new XltY(x[c[0]], x[c[1]]));
      }
      IntVar[] all = new IntVar[3];
      for (int k = 0; k < 3; k++) {
        all[k] = x[instance.alldiff()[k]];
      }
      store.impose(new Alldifferent(all));
      store.impose(new LinearInt(x, instance.linear(), "<=", instance.linearBound()));
      cost = new IntVar(store, "cost", -1000, 1000);
      IntVar[] terms = new IntVar[2 * N + 1];
      int[] coefficients = new int[2 * N + 1];
      for (int i = 0; i < N; i++) {
        terms[i] = x[i];
        terms[N + i] = b[i];
      }
      System.arraycopy(instance.w(), 0, coefficients, 0, 2 * N);
      terms[2 * N] = cost;
      coefficients[2 * N] = -1;
      store.impose(new LinearInt(terms, coefficients, "==", 0));
    }

    int[] values(Var[] vars) {
      int[] v = new int[vars.length];
      for (int i = 0; i < vars.length; i++) {
        assertTrue(vars[i].singleton(), "unfixed variable in a solution: " + vars[i]);
        v[i] = ((IntVar) vars[i]).value();
      }
      return v;
    }

    /** Checks that the store is in a solution state; returns its x and b values as one key. */
    List<Integer> checkSolution() {
      int[] xv = values(x);
      int[] bv = values(b);
      assertTrue(instance.satisfied(xv, bv), "wrong solution " + Arrays.toString(xv) + instance);
      assertEquals(instance.cost(xv, bv), cost.value());
      List<Integer> key = new ArrayList<>();
      Arrays.stream(xv).forEach(key::add);
      Arrays.stream(bv).forEach(key::add);
      return key;
    }
  }

  /** A branching and the monitors it needs. */
  private record Branching(SelectChoicePoint<? extends Var> select, SearchMonitor... monitors) {

    FreeSearch.Builder builder(Store store) {
      FreeSearch.Builder builder = FreeSearch.builder(store, select);
      for (SearchMonitor m : monitors) {
        builder.monitor(m);
      }
      return builder;
    }
  }

  /**
   * The branchings tested: plain variables, weighted heuristics, constraint choices, and dom/wdeg
   * with last conflict and phase saving.
   */
  private static List<Function<Model, Branching>> branchings() {
    return List.of(
        m -> new Branching(new SimpleSelect<>(concat(m), null, new IndomainMin<>())),
        m ->
            new Branching(
                new SimpleSelect<>(concat(m), new AfcMaxDeg<>(m.store), new IndomainMax<>())),
        m ->
            new Branching(
                new SequenceSelect(
                    List.of(
                        new SplitSelect<>(
                            m.x, new MostConstrainedDynamic<>(), new IndomainMiddle<>()),
                        new SimpleSelect<>(m.b, null, new IndomainMin<>())))),
        m ->
            new Branching(
                new SequenceSelect(
                    List.of(
                        new SimpleSelect<>(m.b, new WeightedDegree<>(), new IndomainMax<>()),
                        new SimpleSelect<>(m.x, new SmallestDomain<>(), new IndomainRandom<>(7))))),
        // nested sequences of selections of different sizes
        m ->
            new Branching(
                new SequenceSelect(
                    List.of(
                        new SequenceSelect(
                            List.of(
                                new SimpleSelect<>(
                                    Arrays.copyOfRange(m.x, 0, 2), null, new IndomainMin<>()),
                                new SimpleSelect<>(
                                    Arrays.copyOfRange(m.x, 2, N),
                                    new SmallestDomain<>(),
                                    new IndomainMax<>()))),
                        new SimpleSelect<>(m.b, null, new IndomainMin<>())))),
        m -> {
          IndomainLastSolution phase = new IndomainLastSolution(concat(m), new IndomainMax<>());
          DomWdeg domWdeg = new DomWdeg(concat(m), phase);
          LastConflict lc = new LastConflict(domWdeg, phase, 2);
          return new Branching(lc, phase, domWdeg, lc);
        });
  }

  private static IntVar[] concat(Model m) {
    IntVar[] all = new IntVar[2 * N];
    System.arraycopy(m.x, 0, all, 0, N);
    System.arraycopy(m.b, 0, all, N, N);
    return all;
  }

  /** The restart policies tested; null is no restarts. */
  private static List<Supplier<Calculator>> restartPolicies() {
    return Arrays.asList(
        () -> null,
        () -> new LubyCalculator(1),
        () -> new LubyCalculator(3),
        () -> new GeometricCalculator(1.5, 1));
  }

  @Test
  void satisfiabilityMatchesBruteForce() {
    Random rnd = new Random(1);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      boolean sat = instance.bruteForce()[0] > 0;
      for (var branching : branchings()) {
        for (Supplier<Calculator> restarts : restartPolicies()) {
          Model model = new Model(instance);
          int[] found = {0};
          FreeSearch search =
              branching
                  .apply(model)
                  .builder(model.store)
                  .restarts(restarts.get())
                  .onSolution(
                      s -> {
                        model.checkSolution();
                        found[0]++;
                      })
                  .build();
          Status status = search.solve();
          assertEquals(sat ? Status.SATISFIED : Status.UNSATISFIABLE, status, instance.toString());
          assertEquals(sat ? 1 : 0, found[0]);
        }
      }
    }
  }

  @Test
  void allSolutionsMatchBruteForce() {
    Random rnd = new Random(2);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int count = instance.bruteForce()[0];
      for (var branching : branchings()) {
        Model model = new Model(instance);
        Set<List<Integer>> solutions = new HashSet<>();
        FreeSearch search =
            branching
                .apply(model)
                .builder(model.store)
                .allSolutions(true)
                // ignored: restarts would find the same solutions again
                .restarts(new LubyCalculator(1))
                .onSolution(s -> assertTrue(solutions.add(model.checkSolution())))
                .build();
        Status status = search.solve();
        assertEquals(count > 0 ? Status.OPTIMAL : Status.UNSATISFIABLE, status);
        assertEquals(count, solutions.size(), instance.toString());
        assertEquals(count, search.getSolutions());
      }
    }
  }

  @Test
  void optimumMatchesBruteForce() {
    Random rnd = new Random(3);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int[] reference = instance.bruteForce();
      for (boolean maximize : new boolean[] {false, true}) {
        for (var branching : branchings()) {
          for (Supplier<Calculator> restarts : restartPolicies()) {
            for (boolean restartOnSolution : new boolean[] {false, true}) {
              Model model = new Model(instance);
              List<Integer> costs = new ArrayList<>();
              FreeSearch.Builder builder =
                  branching
                      .apply(model)
                      .builder(model.store)
                      .restarts(restarts.get())
                      .restartOnSolution(restartOnSolution)
                      .record(model.x)
                      .onSolution(
                          s -> {
                            model.checkSolution();
                            costs.add(model.cost.value());
                          });
              FreeSearch search =
                  (maximize ? builder.maximize(model.cost) : builder.minimize(model.cost)).build();
              Status status = search.solve();
              String context = instance + (maximize ? " max" : " min");
              if (reference[0] == 0) {
                assertEquals(Status.UNSATISFIABLE, status, context);
                continue;
              }
              assertEquals(Status.OPTIMAL, status, context);
              int optimum = maximize ? reference[2] : reference[1];
              assertEquals(optimum, search.getCostValue(), context);
              assertEquals(optimum, (int) costs.getLast(), context);
              for (int i = 1; i < costs.size(); i++) {
                assertTrue(
                    maximize ? costs.get(i) > costs.get(i - 1) : costs.get(i) < costs.get(i - 1),
                    "objective does not improve: " + costs + " " + context);
              }
              // the store is back at its initial state, and the solution can be imposed again
              assertTrue(!model.x[0].singleton() || model.x[0].min() == model.x[0].max());
              assertTrue(search.assignSolution());
            }
          }
        }
      }
    }
  }

  @Test
  void alternatingBranchingsKeepTheOptimum() {
    Random rnd = new Random(5);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int[] reference = instance.bruteForce();
      for (FreeSearch.Alternation when : FreeSearch.Alternation.values()) {
        Model model = new Model(instance);
        IndomainLastSolution phase = new IndomainLastSolution(concat(model), new IndomainMin<>());
        DomWdeg domWdeg = new DomWdeg(concat(model), phase);
        // the alternative labels x only; the main branching completes it
        SelectChoicePoint<? extends Var> alternative =
            new SequenceSelect(
                List.of(new SimpleSelect<>(model.x, null, new IndomainMax<>()), domWdeg));
        FreeSearch search =
            FreeSearch.builder(model.store, domWdeg)
                .monitor(phase)
                .monitor(domWdeg)
                .alternateWith(alternative, when)
                .restarts(new LubyCalculator(1))
                .restartOnSolution(true)
                .minimize(model.cost)
                .onSolution(s -> model.checkSolution())
                .build();
        Status status = search.solve();
        if (reference[0] == 0) {
          assertEquals(Status.UNSATISFIABLE, status);
        } else {
          assertEquals(Status.OPTIMAL, status, instance.toString());
          assertEquals(reference[1], search.getCostValue(), instance.toString());
        }
      }
    }
  }

  @Test
  void failuresUnderTheAlternativeBranchingAreNotLearned() {
    // three pairwise different variables with two values: no solution, found only after failures
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    for (int i = 0; i < x.length; i++) {
      for (int j = i + 1; j < x.length; j++) {
        store.impose(new XneqY(x[i], x[j]));
      }
    }
    int[] seen = new int[1];
    SearchMonitor counter =
        new SearchMonitor() {
          @Override
          public void onFailure(Constraint failed, Var decision) {
            seen[0]++;
          }
        };
    FreeSearch search =
        FreeSearch.builder(store, new SimpleSelect<>(x, null, new IndomainMin<>()))
            .alternateWith(
                new SimpleSelect<>(x, null, new IndomainMax<>()),
                FreeSearch.Alternation.UNTIL_FIRST_SOLUTION)
            .monitor(counter)
            .build();
    assertEquals(Status.UNSATISFIABLE, search.solve());
    assertTrue(search.getFailures() > 0);
    assertEquals(0, seen[0]);
  }

  @Test
  void limitsStopTheSearchWithoutAProof() {
    Random rnd = new Random(4);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      Model model = new Model(instance);
      FreeSearch search =
          FreeSearch.builder(
                  model.store, new SimpleSelect<>(concat(model), null, new IndomainMin<>()))
              .minimize(model.cost)
              .failLimit(2)
              .onSolution(s -> model.checkSolution())
              .build();
      Status status = search.solve();
      if (search.limitReached()) {
        assertTrue(status == Status.UNKNOWN || status == Status.SATISFIED);
        assertEquals(search.getSolutions() > 0 ? Status.SATISFIED : Status.UNKNOWN, status);
      } else {
        assertTrue(status == Status.OPTIMAL || status == Status.UNSATISFIABLE);
      }
    }
  }

  @Test
  void deepSearchDoesNotUseTheJavaStack() throws InterruptedException {
    // a recursive search needs several stack frames per decision; 5000 decisions do not fit in a
    // 128 KB thread stack
    int n = 5000;
    Status[] status = new Status[1];
    int[] depth = new int[1];
    Thread thread =
        new Thread(
            null,
            () -> {
              Store store = new Store();
              IntVar[] x = new IntVar[n];
              for (int i = 0; i < n; i++) {
                x[i] = new IntVar(store, 0, 1);
              }
              FreeSearch search =
                  FreeSearch.builder(store, new InputOrderSelect<>(store, x, new IndomainMax<>()))
                      .build();
              status[0] = search.solve();
              depth[0] = search.getMaxDepth();
            },
            "deep-search",
            128 * 1024);
    thread.start();
    thread.join();
    assertEquals(Status.SATISFIED, status[0]);
    assertEquals(n, depth[0]);
  }
}
