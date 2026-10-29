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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.free.DomWdeg;
import org.jacop.search.free.FreeSearch;
import org.jacop.search.free.FreeSearch.Status;
import org.jacop.search.free.IndomainBoundImpact;
import org.jacop.search.free.IndomainLastSolution;
import org.jacop.search.free.LastConflict;
import org.jacop.search.free.ReliabilityPseudoCost;
import org.jacop.search.free.RestartNoGoods;
import org.jacop.search.free.SearchMonitor;
import org.jacop.search.lns.AdaptiveLns;
import org.jacop.search.restart.Calculator;
import org.jacop.search.restart.GeometricCalculator;
import org.jacop.search.restart.LubyCalculator;
import org.jacop.search.restart.RestartHook;
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
        },
        m -> {
          IndomainLastSolution phase = new IndomainLastSolution(concat(m), new IndomainMin<>());
          DomWdeg cacd = new DomWdeg(concat(m), phase, DomWdeg.Weighting.CACD);
          return new Branching(cacd, phase, cacd);
        },
        m -> {
          IndomainLastSolution phase = new IndomainLastSolution(concat(m), new IndomainMin<>());
          DomWdeg chs = new DomWdeg(concat(m), phase, DomWdeg.Weighting.CHS);
          LastConflict lc = new LastConflict(chs, phase, 1);
          return new Branching(lc, phase, chs, lc);
        },
        m -> {
          IndomainLastSolution phase = new IndomainLastSolution(concat(m), new IndomainMin<>());
          DomWdeg domWdeg = new DomWdeg(concat(m), phase);
          ReliabilityPseudoCost pscost =
              new ReliabilityPseudoCost(m.store, domWdeg, phase, m.cost, 2, 3, 0.01d);
          LastConflict lc = new LastConflict(pscost, phase, 1);
          return new Branching(lc, phase, domWdeg, pscost, lc);
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
          for (boolean nogoods : new boolean[] {false, true}) {
            Model model = new Model(instance);
            int[] found = {0};
            FreeSearch search =
                branching
                    .apply(model)
                    .builder(model.store)
                    .restarts(restarts.get())
                    .nogoodsFromRestarts(nogoods)
                    .onSolution(
                        s -> {
                          model.checkSolution();
                          found[0]++;
                        })
                    .build();
            Status status = search.solve();
            assertEquals(
                sat ? Status.SATISFIED : Status.UNSATISFIABLE, status, instance.toString());
            assertEquals(sat ? 1 : 0, found[0]);
          }
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
  void allSolutionsDistinctOnSomeVariablesMatchBruteForce() {
    Random rnd = new Random(6);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      // the distinct values of x0..x2 over all solutions
      Set<List<Integer>> expected = new HashSet<>();
      int total = (int) Math.pow(MAX_VALUE + 1, N);
      int[] x = new int[N];
      int[] b = new int[N];
      for (int code = 0; code < total; code++) {
        int c = code;
        for (int i = 0; i < N; i++) {
          x[i] = c % (MAX_VALUE + 1);
          c /= MAX_VALUE + 1;
          b[i] = x[i] == instance.eq()[i] ? 1 : 0;
        }
        if (instance.satisfied(x, b)) {
          expected.add(List.of(x[0], x[1], x[2]));
        }
      }
      Model model = new Model(instance);
      IntVar[] shown = Arrays.copyOfRange(model.x, 0, 3);
      IntVar[] rest = Arrays.copyOfRange(concat(model), 3, 2 * N);
      List<List<Integer>> found = new ArrayList<>();
      FreeSearch search =
          FreeSearch.builder(
                  model.store,
                  new SequenceSelect(
                      List.of(
                          new SimpleSelect<>(shown, new SmallestDomain<>(), new IndomainMax<>()),
                          new SimpleSelect<>(rest, null, new IndomainMin<>()))))
              .allSolutions(true)
              .distinctOn(shown)
              .onSolution(
                  s -> {
                    model.checkSolution();
                    found.add(List.of(shown[0].value(), shown[1].value(), shown[2].value()));
                  })
              .build();
      Status status = search.solve();
      assertEquals(expected.isEmpty() ? Status.UNSATISFIABLE : Status.OPTIMAL, status);
      assertEquals(expected.size(), found.size(), instance.toString());
      assertEquals(expected, new HashSet<>(found), instance.toString());
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
            for (int option = 0; option < 4; option++) {
              boolean restartOnSolution = (option & 1) != 0;
              boolean nogoods = (option & 2) != 0;
              Model model = new Model(instance);
              List<Integer> costs = new ArrayList<>();
              FreeSearch.Builder builder =
                  branching
                      .apply(model)
                      .builder(model.store)
                      .restarts(restarts.get())
                      .restartOnSolution(restartOnSolution)
                      .nogoodsFromRestarts(nogoods)
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
                .nogoodsFromRestarts(true)
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
  void timeLimitStopsASearchWithSlowNodes() {
    // pigeonhole: 8 variables, 7 values, pairwise different; thousands of nodes to prove it
    Store store = new Store();
    IntVar[] x = new IntVar[8];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, 0, x.length - 2);
    }
    for (int i = 0; i < x.length; i++) {
      for (int j = i + 1; j < x.length; j++) {
        store.impose(new XneqY(x[i], x[j]));
      }
    }
    IndomainMin<IntVar> min = new IndomainMin<>();
    // each node takes 20 ms, as with a costly propagation
    Indomain<IntVar> slow =
        v -> {
          try {
            Thread.sleep(20);
          } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
          }
          return min.indomain(v);
        };
    FreeSearch search =
        FreeSearch.builder(store, new SimpleSelect<>(x, null, slow))
            .timeLimit(Duration.ofMillis(100))
            .build();
    long start = System.currentTimeMillis();
    Status status = search.solve();
    long elapsed = System.currentTimeMillis() - start;
    assertTrue(search.limitReached());
    assertEquals(Status.UNKNOWN, status);
    // a check every 256 nodes would only stop after more than a second
    assertTrue(elapsed < 1000, "stopped after " + elapsed + " ms");
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

  @Test
  void restartNoGoodsPropagateAndBacktrack() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar z = new IntVar(store, "z", 0, 3);
    store.setLevel(1);
    RestartNoGoods nogoods = new RestartNoGoods(store, 10, 10);
    store.impose(nogoods);
    nogoods.add(new IntVar[] {x, y, z}, new int[] {1, 2, 3}, 3);
    // a literal false at the root: the nogood always holds and is not kept
    nogoods.add(new IntVar[] {x, y}, new int[] {2, 7}, 2);
    assertEquals(1, nogoods.size());
    assertTrue(store.consistency());

    store.setLevel(2);
    x.domain.in(store.level, x, 1, 1);
    assertTrue(store.consistency());
    assertTrue(z.domain.contains(3));
    store.setLevel(3);
    y.domain.in(store.level, y, 2, 2);
    assertTrue(store.consistency());
    assertFalse(z.domain.contains(3));
    store.removeLevel(3);
    store.setLevel(2);
    assertTrue(z.domain.contains(3));
    store.setLevel(3);
    z.domain.in(store.level, z, 3, 3);
    assertTrue(store.consistency());
    assertFalse(y.domain.contains(2));
    store.removeLevel(3);
    store.setLevel(3);
    // all literals true: the propagation fails
    y.domain.in(store.level, y, 2, 2);
    z.domain.in(store.level, z, 3, 3);
    assertFalse(store.consistency());
    store.removeLevel(3);
    store.removeLevel(2);
    store.setLevel(1);

    // a unit nogood removes its value at once
    nogoods.add(new IntVar[] {x}, new int[] {0}, 1);
    assertFalse(x.domain.contains(0));
    // a nogood whose literals all hold at the root makes the next propagation fail
    store.setLevel(2);
    x.domain.in(store.level, x, 2, 2);
    assertTrue(store.consistency());
    nogoods.add(new IntVar[] {x}, new int[] {2}, 1);
    assertFalse(store.consistency());
    nogoods.detach();
  }

  @Test
  void restartNoGoodsDeleteTheOldestBeyondTheLimit() {
    Store store = new Store();
    IntVar[] v = new IntVar[4];
    for (int i = 0; i < v.length; i++) {
      v[i] = new IntVar(store, "v" + i, 0, 3);
    }
    store.setLevel(1);
    RestartNoGoods nogoods = new RestartNoGoods(store, 2, 3);
    store.impose(nogoods);
    nogoods.add(new IntVar[] {v[0], v[1]}, new int[] {0, 0}, 2);
    nogoods.add(new IntVar[] {v[1], v[2]}, new int[] {1, 1}, 2);
    nogoods.add(new IntVar[] {v[2], v[3]}, new int[] {2, 2}, 2);
    assertEquals(2, nogoods.size());
    assertEquals(1, nogoods.getDeleted());
    // too long to be kept
    nogoods.add(v, new int[] {3, 3, 3, 3}, 4);
    assertEquals(2, nogoods.size());

    store.setLevel(2);
    v[0].domain.in(store.level, v[0], 0, 0);
    assertTrue(store.consistency());
    // the oldest nogood is gone
    assertTrue(v[1].domain.contains(0));
    v[2].domain.in(store.level, v[2], 2, 2);
    assertTrue(store.consistency());
    assertFalse(v[3].domain.contains(2));
    nogoods.detach();
  }

  @Test
  void nogoodsFromRestartsProveUnsatisfiability() {
    // seven pigeons, six holes
    Store store = new Store();
    IntVar[] p = new IntVar[7];
    for (int i = 0; i < p.length; i++) {
      p[i] = new IntVar(store, "p" + i, 0, 5);
    }
    for (int i = 0; i < p.length; i++) {
      for (int j = i + 1; j < p.length; j++) {
        store.impose(new XneqY(p[i], p[j]));
      }
    }
    FreeSearch search =
        FreeSearch.builder(store, new SimpleSelect<>(p, null, new IndomainMin<>()))
            .restarts(new LubyCalculator(2))
            .nogoodsFromRestarts(true)
            .build();
    assertEquals(Status.UNSATISFIABLE, search.solve());
    assertTrue(search.getNogoods() > 0);
    assertTrue(search.getRestarts() > 0);
    // the nogoods are removed with the search; the store has its domains back
    assertEquals(6, p[0].getSize());
    assertEquals(0, store.countWatches());
  }

  @Test
  void boundImpactPicksTheValueWithTheBestBoundAndLeavesTheStore() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 3);
    IntVar y = new IntVar(store, "y", 0, 5);
    IntVar cost = new IntVar(store, "cost", -100, 100);
    // cost = y - 4x: x = 3 leaves the smallest bound
    store.impose(new LinearInt(new IntVar[] {y, x, cost}, new int[] {1, -4, -1}, "==", 0));
    assertTrue(store.consistency());
    IndomainBoundImpact impact =
        new IndomainBoundImpact(store, cost, false, 10, new IndomainMin<>());
    assertEquals(3, impact.indomain(x));
    assertEquals(3, impact.getProbes());
    assertEquals(3, x.getSize());
    assertEquals(-12, cost.min());
    assertEquals(
        1, new IndomainBoundImpact(store, cost, true, 10, new IndomainMin<>()).indomain(x));
    IndomainBoundImpact once =
        new IndomainBoundImpact(store, cost, false, 10, new IndomainMin<>()).untilFirstSolution();
    assertEquals(3, once.indomain(x));
    once.onSolution(null);
    assertEquals(1, once.indomain(x));
    // larger domains than the limit use the wrapped heuristic
    assertEquals(
        0, new IndomainBoundImpact(store, cost, false, 2, new IndomainMin<>()).indomain(y));
  }

  @Test
  void pseudoCostsSelectTheLargestGainAndLeaveTheStore() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar cost = new IntVar(store, "cost", -100, 100);
    // cost = a + 5b: b = 1 raises the bound most
    store.impose(new LinearInt(new IntVar[] {a, b, cost}, new int[] {1, 5, -1}, "==", 0));
    assertTrue(store.consistency());
    IntVar[] vars = {a, b};
    DomWdeg domWdeg = new DomWdeg(vars, new IndomainMin<>());
    ReliabilityPseudoCost pscost =
        new ReliabilityPseudoCost(store, domWdeg, new IndomainMin<>(), cost, 1, 8, 0.01d);
    assertEquals(b, pscost.getChoiceVariable(0));
    assertEquals(0, pscost.getChoiceValue());
    assertEquals(4, pscost.getProbes());
    assertEquals(2, a.getSize());
    assertEquals(2, b.getSize());
    assertEquals(0, cost.min());
    // both are reliable now: no more probes, the pseudo-costs decide
    assertEquals(b, pscost.getChoiceVariable(0));
    assertEquals(4, pscost.getProbes());
    // without probes dom/wdeg breaks the tie of unknown pseudo-costs
    ReliabilityPseudoCost unprobed =
        new ReliabilityPseudoCost(store, domWdeg, new IndomainMin<>(), cost, 0, 8, 0.01d);
    assertEquals(a, unprobed.getChoiceVariable(0));
    assertEquals(0, unprobed.getProbes());
  }

  @Test
  void pseudoCostsSelectAVariableWithAFailedBranch() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    IntVar d = new IntVar(store, "d", 0, 1);
    IntVar cost = new IntVar(store, "cost", -100, 100);
    store.impose(new LinearInt(new IntVar[] {a, c, cost}, new int[] {5, 1, -1}, "==", 0));
    // c = 0 leaves no value for d, which only probing finds
    store.impose(new IfThen(new XeqC(c, 0), new XeqC(d, 0)));
    store.impose(new IfThen(new XeqC(c, 0), new XeqC(d, 1)));
    assertTrue(store.consistency());
    assertEquals(2, c.getSize());
    DomWdeg domWdeg = new DomWdeg(new IntVar[] {a, c, d}, new IndomainMin<>());
    ReliabilityPseudoCost pscost =
        new ReliabilityPseudoCost(store, domWdeg, new IndomainMin<>(), cost, 1, 8, 0.01d);
    assertEquals(c, pscost.getChoiceVariable(0));
    assertEquals(2, c.getSize());
  }

  @Test
  void pseudoCostsKeepTheOptimum() {
    Random rnd = new Random(13);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int[] reference = instance.bruteForce();
      for (boolean maximize : new boolean[] {false, true}) {
        Model model = new Model(instance);
        IndomainLastSolution phase = new IndomainLastSolution(concat(model), new IndomainMin<>());
        DomWdeg domWdeg = new DomWdeg(concat(model), phase);
        IntVar minimised = model.cost;
        if (maximize) {
          minimised = new IntVar(model.store, "negated", -1000, 1000);
          model.store.impose(new XplusYeqC(model.cost, minimised, 0));
        }
        ReliabilityPseudoCost pscost =
            new ReliabilityPseudoCost(model.store, domWdeg, phase, minimised);
        LastConflict lc = new LastConflict(pscost, phase, 1);
        FreeSearch.Builder builder =
            FreeSearch.builder(model.store, lc)
                .monitor(phase)
                .monitor(domWdeg)
                .monitor(pscost)
                .monitor(lc)
                .restarts(new LubyCalculator(2))
                .restartOnSolution(true)
                .nogoodsFromRestarts(true)
                .onSolution(s -> model.checkSolution());
        FreeSearch search =
            (maximize ? builder.maximize(model.cost) : builder.minimize(model.cost)).build();
        Status status = search.solve();
        if (reference[0] == 0) {
          assertEquals(Status.UNSATISFIABLE, status);
        } else {
          assertEquals(Status.OPTIMAL, status, instance.toString());
          assertEquals(reference[maximize ? 2 : 1], search.getCostValue());
        }
      }
    }
  }

  @Test
  void boundImpactKeepsTheOptimum() {
    Random rnd = new Random(7);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int[] reference = instance.bruteForce();
      for (boolean maximize : new boolean[] {false, true}) {
        Model model = new Model(instance);
        IndomainBoundImpact impact =
            new IndomainBoundImpact(model.store, model.cost, maximize, 5, new IndomainMin<>());
        IndomainLastSolution phase = new IndomainLastSolution(concat(model), impact);
        DomWdeg domWdeg = new DomWdeg(concat(model), phase);
        FreeSearch.Builder builder =
            FreeSearch.builder(model.store, domWdeg)
                .monitor(phase)
                .monitor(domWdeg)
                .restarts(new LubyCalculator(2))
                .restartOnSolution(true)
                .nogoodsFromRestarts(true)
                .onSolution(s -> model.checkSolution());
        FreeSearch search =
            (maximize ? builder.maximize(model.cost) : builder.minimize(model.cost)).build();
        Status status = search.solve();
        if (reference[0] == 0) {
          assertEquals(Status.UNSATISFIABLE, status);
        } else {
          assertEquals(Status.OPTIMAL, status, instance.toString());
          assertEquals(reference[maximize ? 2 : 1], search.getCostValue());
        }
      }
    }
  }

  @Test
  void restartLimitsStartAgainAfterReset() {
    GeometricCalculator geometric = new GeometricCalculator(2, 10);
    geometric.newLimit();
    geometric.newLimit();
    assertEquals(40, geometric.getFailLimit());
    geometric.reset();
    assertEquals(10, geometric.getFailLimit());
    geometric.newLimit();
    assertEquals(20, geometric.getFailLimit());
    LubyCalculator luby = new LubyCalculator(5);
    luby.newLimit();
    luby.newLimit();
    assertEquals(10, luby.getFailLimit());
    luby.reset();
    assertEquals(5, luby.getFailLimit());
  }

  @Test
  void chocoLikeSettingsKeepTheOptimum() {
    // short restarts started again after each solution, weights forgotten every other restart and
    // bound-impact values in every other run
    Random rnd = new Random(11);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int[] reference = instance.bruteForce();
      for (boolean maximize : new boolean[] {false, true}) {
        Model model = new Model(instance);
        IndomainBoundImpact impact =
            new IndomainBoundImpact(model.store, model.cost, maximize, 5, new IndomainMin<>())
                .everyRestarts(2);
        IndomainLastSolution phase = new IndomainLastSolution(concat(model), impact);
        DomWdeg domWdeg = new DomWdeg(concat(model), phase).flushEvery(2);
        LastConflict lastConflict = new LastConflict(domWdeg, phase, 1);
        FreeSearch.Builder builder =
            FreeSearch.builder(model.store, lastConflict)
                .monitor(impact)
                .monitor(phase)
                .monitor(domWdeg)
                .monitor(lastConflict)
                .restarts(new GeometricCalculator(1.05, 1))
                .restartOnSolution(true)
                .resetRestartsOnSolution(true)
                .nogoodsFromRestarts(true)
                .onSolution(s -> model.checkSolution());
        FreeSearch search =
            (maximize ? builder.maximize(model.cost) : builder.minimize(model.cost)).build();
        Status status = search.solve();
        if (reference[0] == 0) {
          assertEquals(Status.UNSATISFIABLE, status, instance.toString());
        } else {
          assertEquals(Status.OPTIMAL, status, instance.toString());
          assertEquals(reference[maximize ? 2 : 1], search.getCostValue(), instance.toString());
        }
      }
    }
  }

  @Test
  void objectiveProbesKeepTheOptimum() {
    // probes with the objective at its lower bound and a growing offset, from one failure each,
    // under every branching and restart policy, with and without nogoods and restart on solution
    Random rnd = new Random(13);
    long refuted = 0;
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int[] reference = instance.bruteForce();
      for (boolean maximize : new boolean[] {false, true}) {
        for (var branching : branchings()) {
          for (Supplier<Calculator> restarts : restartPolicies()) {
            if (restarts.get() == null) {
              continue;
            }
            for (int option = 0; option < 8; option++) {
              boolean restartOnSolution = (option & 1) != 0;
              boolean nogoods = (option & 2) != 0;
              double share = (option & 4) != 0 ? 3.0 : 0.5;
              Model model = new Model(instance);
              List<Integer> costs = new ArrayList<>();
              FreeSearch.Builder builder =
                  branching
                      .apply(model)
                      .builder(model.store)
                      .restarts(restarts.get())
                      .restartOnSolution(restartOnSolution)
                      .nogoodsFromRestarts(nogoods)
                      .probeObjective(share, 1 + option % 3)
                      .record(model.x)
                      .onSolution(
                          s -> {
                            model.checkSolution();
                            costs.add(model.cost.value());
                          });
              FreeSearch search =
                  (maximize ? builder.maximize(model.cost) : builder.minimize(model.cost)).build();
              Status status = search.solve();
              String context = instance + (maximize ? " max " : " min ") + option;
              refuted += search.getProbesRefuted();
              assertStoreIsBack(model, context);
              if (reference[0] == 0) {
                assertEquals(Status.UNSATISFIABLE, status, context);
                continue;
              }
              assertEquals(Status.OPTIMAL, status, context);
              int optimum = maximize ? reference[2] : reference[1];
              assertEquals(optimum, search.getCostValue(), context);
              for (int i = 1; i < costs.size(); i++) {
                assertTrue(
                    maximize ? costs.get(i) > costs.get(i - 1) : costs.get(i) < costs.get(i - 1),
                    "objective does not improve: " + costs + " " + context);
              }
            }
          }
        }
      }
    }
    assertTrue(refuted > 0);
  }

  @Test
  void objectiveProbesStoppedByALimitLeaveTheStore() {
    Random rnd = new Random(17);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      for (int limit = 1; limit <= 6; limit++) {
        Model model = new Model(instance);
        FreeSearch search =
            FreeSearch.builder(
                    model.store, new SimpleSelect<>(concat(model), null, new IndomainMin<>()))
                .restarts(new LubyCalculator(1))
                .probeObjective(10, 2)
                .minimize(model.cost)
                .failLimit(limit)
                .onSolution(s -> model.checkSolution())
                .build();
        Status status = search.solve();
        assertStoreIsBack(model, instance + " limit " + limit);
        if (search.limitReached()) {
          assertEquals(search.getSolutions() > 0 ? Status.SATISFIED : Status.UNKNOWN, status);
        }
      }
    }
  }

  @Test
  void refutedProbesRaiseTheLowerBound() {
    // seven pairwise different variables over 0..9 minimising their sum: the sum propagates a lower
    // bound of 0 while the optimum is 21, so the probes below 21 must be refuted by search
    for (boolean maximize : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar[] x = new IntVar[7];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 9);
      }
      for (int i = 0; i < x.length; i++) {
        for (int j = i + 1; j < x.length; j++) {
          store.impose(new XneqY(x[i], x[j]));
        }
      }
      IntVar cost = new IntVar(store, "cost", 0, 63);
      store.impose(new LinearInt(x, new int[] {1, 1, 1, 1, 1, 1, 1}, "==", cost));
      IntVar objective = cost;
      if (maximize) {
        objective = new IntVar(store, "negated", -63, 0);
        store.impose(new XplusYeqC(cost, objective, 0));
      }
      FreeSearch.Builder builder =
          FreeSearch.builder(store, new SimpleSelect<>(x, null, new IndomainMax<>()))
              .restarts(new LubyCalculator(10))
              .restartOnSolution(true)
              .probeObjective(1, 10);
      FreeSearch search = (maximize ? builder.maximize(objective) : builder.minimize(cost)).build();
      assertEquals(Status.OPTIMAL, search.solve());
      assertEquals(maximize ? -21 : 21, search.getCostValue());
      assertTrue(search.getProbesRefuted() > 0);
      assertEquals(0, cost.min());
      assertEquals(63, cost.max());
    }
  }

  /**
   * dom/wdeg as a full scan of the variables and of the scopes of their constraints at every node,
   * the way DomWdeg selected before it kept its unfixed sets incrementally.
   */
  private static final class ScanDomWdeg implements SelectChoicePoint<IntVar>, SearchMonitor {
    private final IntVar[] vars;
    private final Indomain<IntVar> indomain;
    private final List<List<Constraint>> constraints = new ArrayList<>();
    private final Map<Constraint, Double> weights = new IdentityHashMap<>();
    private IntVar selected;

    ScanDomWdeg(IntVar[] vars, Indomain<IntVar> indomain) {
      this.vars = vars;
      this.indomain = indomain;
      for (IntVar v : vars) {
        List<Constraint> cs = new ArrayList<>();
        for (Constraint c : v.dom().constraints()) {
          if (cs.stream().noneMatch(d -> d == c)) {
            cs.add(c);
            weights.put(c, 1.0d);
          }
        }
        constraints.add(cs);
      }
    }

    @Override
    public IntVar getChoiceVariable(int index) {
      selected = null;
      double best = Double.MAX_VALUE;
      for (int i = 0; i < vars.length; i++) {
        IntVar v = vars[i];
        if (v.singleton()) {
          continue;
        }
        double w = 0.0d;
        for (Constraint c : constraints.get(i)) {
          if (c.arguments().stream().filter(x -> !x.singleton()).count() >= 2) {
            w += weights.get(c);
          }
        }
        double score = w > 0.0d ? v.getSize() / w : Double.MAX_VALUE / 2 + v.getSize();
        if (selected == null || score < best) {
          best = score;
          selected = v;
        }
      }
      return selected;
    }

    @Override
    public int getChoiceValue() {
      return indomain.indomain(selected);
    }

    @Override
    public PrimitiveConstraint getChoiceConstraint(int index) {
      return null;
    }

    @Override
    public Map<IntVar, Integer> getVariablesMapping() {
      Map<IntVar, Integer> mapping = new IdentityHashMap<>();
      for (int i = 0; i < vars.length; i++) {
        mapping.putIfAbsent(vars[i], i);
      }
      return mapping;
    }

    @Override
    public int getIndex() {
      return 0;
    }

    @Override
    public void onFailure(Constraint failed, Var decision) {
      weights.computeIfPresent(failed, (c, w) -> w + 1.0d);
    }
  }

  /** Runs dom/wdeg with restarts and nogoods, minimising the cost, and returns its statistics. */
  private static long[] domWdegRun(Instance instance, boolean scan) {
    Model model = new Model(instance);
    IndomainLastSolution phase = new IndomainLastSolution(concat(model), new IndomainMin<>());
    SelectChoicePoint<IntVar> select;
    SearchMonitor weights;
    if (scan) {
      ScanDomWdeg s = new ScanDomWdeg(concat(model), phase);
      select = s;
      weights = s;
    } else {
      DomWdeg d = new DomWdeg(concat(model), phase);
      select = d;
      weights = d;
    }
    FreeSearch search =
        FreeSearch.builder(model.store, select)
            .monitor(phase)
            .monitor(weights)
            .restarts(new LubyCalculator(1))
            .nogoodsFromRestarts(true)
            .restartOnSolution(true)
            .minimize(model.cost)
            .build();
    Status status = search.solve();
    return new long[] {
      status.ordinal(),
      search.getNodes(),
      search.getFailures(),
      search.getRestarts(),
      search.getSolutions(),
      status == Status.OPTIMAL ? search.getCostValue() : 0
    };
  }

  @Test
  void domWdegSearchesLikeAFullScan() {
    Random rnd = new Random(11);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      assertEquals(
          Arrays.toString(domWdegRun(instance, true)),
          Arrays.toString(domWdegRun(instance, false)),
          instance.toString());
    }
  }

  /** Checks that the domains of the model are those it had before the search. */
  private static void assertStoreIsBack(Model model, String context) {
    for (int i = 0; i < N; i++) {
      assertEquals(0, model.x[i].min(), context);
      assertEquals(MAX_VALUE, model.x[i].max(), context);
      assertEquals(MAX_VALUE + 1, model.x[i].getSize(), context);
    }
    assertEquals(-1000, model.cost.min(), context);
    assertEquals(1000, model.cost.max(), context);
  }

  @Test
  void largeNeighbourhoodRunsKeepTheOptimum() {
    // runs in neighbourhoods of the best solution take as much time as the other runs and fail
    // after three failures; they must neither lose the optimum nor claim a proof, also when
    // objective probes share the runs with them
    Random rnd = new Random(13);
    long lnsRuns = 0;
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int[] reference = instance.bruteForce();
      for (boolean nogoods : new boolean[] {false, true}) {
        Model model = new Model(instance);
        IndomainLastSolution phase = new IndomainLastSolution(concat(model), new IndomainMin<>());
        DomWdeg domWdeg = new DomWdeg(concat(model), phase);
        AdaptiveLns lns = new AdaptiveLns(model.store, concat(model), model.cost, new Random(k));
        List<Integer> costs = new ArrayList<>();
        FreeSearch search =
            FreeSearch.builder(model.store, domWdeg)
                .monitor(phase)
                .monitor(domWdeg)
                .restarts(new GeometricCalculator(1.05, 1))
                .restartOnSolution(true)
                .nogoodsFromRestarts(nogoods)
                .lns(lns, 1.0, 3)
                .probeObjective(nogoods ? 0.5 : 0, 2)
                .minimize(model.cost)
                .onSolution(
                    s -> {
                      model.checkSolution();
                      costs.add(model.cost.value());
                    })
                .build();
        Status status = search.solve();
        lnsRuns += search.getLnsRuns();
        if (reference[0] == 0) {
          assertEquals(Status.UNSATISFIABLE, status, instance.toString());
          continue;
        }
        assertEquals(Status.OPTIMAL, status, instance.toString());
        assertEquals(reference[1], search.getCostValue(), instance.toString());
        for (int i = 1; i < costs.size(); i++) {
          assertTrue(costs.get(i) < costs.get(i - 1), costs + " " + instance);
        }
        assertEquals(lns.runs(), search.getLnsRuns());
      }
    }
    assertTrue(lnsRuns > 0);
  }

  @Test
  void restartHookFixesVariablesInEveryRun() {
    // the hook fixes x0 to its value in the last solution in every other run: those runs prove
    // nothing, so the optimum is proved by a run without it, by the bound failing at the root, or
    // when the hook marks the search complete
    Random rnd = new Random(17);
    for (int k = 0; k < INSTANCES; k++) {
      Instance instance = Instance.random(rnd);
      int[] reference = instance.bruteForce();
      Model model = new Model(instance);
      int[] calls = new int[1];
      int[] last = {-1};
      List<Integer> statuses = new ArrayList<>();
      RestartHook hook =
          new RestartHook() {
            @Override
            public void restart(Store store, int status) {
              statuses.add(status);
              if (calls[0]++ % 2 == 0 && last[0] >= 0) {
                model.x[0].domain.inValue(store.level, model.x[0], last[0]);
              }
            }

            @Override
            public void solution() {
              last[0] = model.x[0].value();
            }

            @Override
            public boolean completeMarked() {
              return calls[0] > 400;
            }
          };
      FreeSearch search =
          FreeSearch.builder(
                  model.store, new SimpleSelect<>(concat(model), null, new IndomainMin<>()))
              .restarts(new GeometricCalculator(1.1, 2))
              .restartOnSolution(true)
              .nogoodsFromRestarts(true)
              .restartHook(hook)
              .minimize(model.cost)
              .onSolution(s -> model.checkSolution())
              .build();
      Status status = search.solve();
      if (!statuses.isEmpty()) {
        assertEquals(RestartHook.START, (int) statuses.getFirst());
      }
      if (reference[0] == 0) {
        assertEquals(Status.UNSATISFIABLE, status, instance.toString());
        continue;
      }
      assertEquals(Status.OPTIMAL, status, instance.toString());
      assertEquals(reference[1], search.getCostValue(), instance.toString());
    }
  }

  @Test
  void largeNeighbourhoodRunsKeepTablesInStepWithRootPrunings() {
    // nogoods learned at a restart prune at the root; a table that first sees those prunings at
    // the level of the next run in a neighbourhood forgets them when that level is removed, and
    // then accepts tuples with removed values
    Random rnd = new Random(29);
    for (int k = 0; k < INSTANCES; k++) {
      Store store = new Store();
      IntVar[] x = new IntVar[N];
      for (int i = 0; i < N; i++) {
        x[i] = new IntVar(store, "x" + i, 0, MAX_VALUE);
      }
      int[][] scopes = {{0, 1, 2}, {2, 3, 4}, {4, 5, 0}};
      List<Set<List<Integer>>> allowed = new ArrayList<>();
      for (int[] scope : scopes) {
        List<int[]> tuples = new ArrayList<>();
        Set<List<Integer>> set = new HashSet<>();
        for (int a = 0; a <= MAX_VALUE; a++) {
          for (int b = 0; b <= MAX_VALUE; b++) {
            for (int c = 0; c <= MAX_VALUE; c++) {
              if (rnd.nextInt(10) < 4) {
                tuples.add(new int[] {a, b, c});
                set.add(List.of(a, b, c));
              }
            }
          }
        }
        allowed.add(set);
        store.impose(
            new HybridTable(
                new IntVar[] {x[scope[0]], x[scope[1]], x[scope[2]]},
                tuples.toArray(new int[0][])));
      }
      int[] w = new int[N + 1];
      for (int i = 0; i < N; i++) {
        w[i] = rnd.nextInt(9) - 3;
      }
      w[N] = -1;
      IntVar cost = new IntVar(store, "cost", -1000, 1000);
      IntVar[] terms = Arrays.copyOf(x, N + 1);
      terms[N] = cost;
      store.impose(new LinearInt(terms, w, "==", 0));
      Function<int[], Boolean> satisfied =
          v -> {
            for (int t = 0; t < scopes.length; t++) {
              int[] sc = scopes[t];
              if (!allowed.get(t).contains(List.of(v[sc[0]], v[sc[1]], v[sc[2]]))) {
                return false;
              }
            }
            return true;
          };
      int best = Integer.MAX_VALUE;
      int[] v = new int[N];
      for (int code = 0; code < Math.pow(MAX_VALUE + 1, N); code++) {
        int c = code;
        int sum = 0;
        for (int i = 0; i < N; i++) {
          v[i] = c % (MAX_VALUE + 1);
          c /= MAX_VALUE + 1;
          sum += w[i] * v[i];
        }
        if (satisfied.apply(v)) {
          best = Math.min(best, sum);
        }
      }
      DomWdeg domWdeg = new DomWdeg(x, new IndomainRandom<>(k));
      FreeSearch search =
          FreeSearch.builder(store, domWdeg)
              .monitor(domWdeg)
              .restarts(new GeometricCalculator(1.05, 1))
              .restartOnSolution(true)
              .nogoodsFromRestarts(true)
              .lns(new AdaptiveLns(store, x, cost, new Random(k)), 1.0, 2)
              .minimize(cost)
              .onSolution(
                  s -> {
                    int[] sol = new int[N];
                    for (int i = 0; i < N; i++) {
                      sol[i] = x[i].value();
                    }
                    assertTrue(satisfied.apply(sol), "wrong solution " + Arrays.toString(sol));
                  })
              .build();
      Status status = search.solve();
      if (best == Integer.MAX_VALUE) {
        assertEquals(Status.UNSATISFIABLE, status);
      } else {
        assertEquals(Status.OPTIMAL, status);
        assertEquals(best, search.getCostValue());
      }
    }
  }
}
