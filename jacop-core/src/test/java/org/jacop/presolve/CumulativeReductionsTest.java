/*
 * CumulativeReductionsTest.java
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

package org.jacop.presolve;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * The cumulative presolve rule: removing irrelevant tasks and implied resources keeps every
 * solution, and dual fixing keeps the optimum and satisfiability.
 */
class CumulativeReductionsTest {

  private static final int TRIALS = Integer.getInteger("cumulative.presolve.trials", 300);

  /** A random scheduling model; with a makespan, it is the last variable. */
  private record Model(long seed, boolean withMakespan) {

    IntVar[] build(Store store) {
      Random r = new Random(seed);
      int n = 3 + r.nextInt(2);
      int horizon = 3 + r.nextInt(4);
      IntVar[] s = new IntVar[n];
      IntVar[] d = new IntVar[n];
      IntVar[] u = new IntVar[n];
      List<IntVar> vars = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        int lo = r.nextInt(3);
        s[i] = new IntVar(store, "s" + i, lo, lo + 2 + r.nextInt(horizon));
        int dv = 1 + r.nextInt(3);
        d[i] = new IntVar(store, "d" + i, r.nextInt(4) == 0 ? r.nextInt(2) : dv, dv);
        int uv = 1 + r.nextInt(3);
        u[i] = new IntVar(store, "u" + i, r.nextInt(5) == 0 ? 0 : uv, uv);
        vars.add(s[i]);
        vars.add(d[i]);
        vars.add(u[i]);
      }
      int lv = 2 + r.nextInt(3);
      IntVar limit = new IntVar(store, "limit", r.nextInt(4) == 0 ? 2 : lv, lv);
      vars.add(limit);
      int resources = 1 + r.nextInt(2);
      for (int k = 0; k < resources; k++) {
        List<Integer> tasks = new ArrayList<>();
        for (int i = 0; i < n; i++) {
          if (r.nextInt(4) != 0) {
            tasks.add(i);
          }
        }
        if (tasks.isEmpty()) {
          continue;
        }
        IntVar[] ts = tasks.stream().map(i -> s[i]).toArray(IntVar[]::new);
        IntVar[] td = tasks.stream().map(i -> d[i]).toArray(IntVar[]::new);
        IntVar[] tu = tasks.stream().map(i -> u[i]).toArray(IntVar[]::new);
        store.impose(
            r.nextBoolean()
                ? new Cumulative(ts, td, tu, limit)
                : new CumulativeBasic(ts, td, tu, limit));
        if (r.nextInt(3) == 0) {
          // a unary resource and sometimes one on a subset of its tasks, as the disjunctive cliques
          // and the model can both post
          IntVar one = new IntVar(store, 1, 1);
          IntVar[] ones = new IntVar[ts.length];
          Arrays.fill(ones, one);
          store.impose(new CumulativeUnary(ts, td, ones, one, true));
          if (ts.length > 2 && r.nextBoolean()) {
            store.impose(
                new CumulativeUnary(
                    Arrays.copyOf(ts, 2), Arrays.copyOf(td, 2), Arrays.copyOf(ones, 2), one));
          }
        }
      }
      IntVar makespan = withMakespan ? new IntVar(store, "makespan", 0, horizon + 8) : null;
      for (int i = 0; i < n; i++) {
        if (withMakespan) {
          store.impose(
              new LinearInt(new IntVar[] {s[i], d[i], makespan}, new int[] {1, 1, -1}, "<=", 0));
        }
        if (r.nextInt(4) == 0) {
          int j = r.nextInt(n);
          if (j != i) {
            store.impose(new XplusClteqZ(s[i], d[i].min(), s[j]));
          }
        }
        if (r.nextInt(6) == 0) {
          int j = r.nextInt(n);
          if (j != i) {
            store.impose(new XneqY(s[i], s[j]));
          }
        }
        if (r.nextInt(6) == 0) {
          int j = r.nextInt(n);
          if (j != i) {
            store.impose(
                new LinearInt(new IntVar[] {s[i], s[j]}, new int[] {1, 1}, ">=", 1 + r.nextInt(5)));
          }
        }
      }
      if (withMakespan) {
        vars.add(makespan);
      }
      return vars.toArray(new IntVar[0]);
    }
  }

  @Test
  void removingTasksAndResourcesKeepsEverySolution() {
    int removals = 0;
    for (int t = 0; t < TRIALS; t++) {
      Model model = new Model(t, false);
      Set<List<Integer>> expected = solveDirectly(model);
      CumulativeReductions rule = new CumulativeReductions(false);
      Store store = new Store();
      Set<List<Integer>> found = solveThroughPresolve(store, model.build(store), rule);
      assertThat(found).as("seed %d", t).isEqualTo(expected);
      assertThat(rule.fixedStarts()).isZero();
      removals += rule.removedTasks() + rule.removedResources();
    }
    assertThat(removals).isPositive();
  }

  @Test
  void dualFixingKeepsTheOptimum() {
    int fixed = 0;
    for (int t = 0; t < TRIALS; t++) {
      Model model = new Model(t, true);
      Store original = new Store();
      IntVar[] originalVars = model.build(original);
      int expected =
          original.consistency()
              ? minimize(original, originalVars, originalVars[originalVars.length - 1], () -> {})
              : Integer.MAX_VALUE;

      Store store = new Store();
      IntVar[] vars = model.build(store);
      IntVar makespan = vars[vars.length - 1];
      CumulativeReductions rule = new CumulativeReductions(true).objective(makespan, true);
      // checking mode: every solution found is checked against the whole model
      Derivation d = Presolver.of(store).keep(vars).checking(true).rule(rule).presolve();
      int found = Integer.MAX_VALUE;
      if (d.outcome() != Derivation.Outcome.INFEASIBLE) {
        // a makespan fixed by presolve has no counterpart in the child
        IntVar cost =
            d.get(makespan) != null
                ? d.get(makespan)
                : new IntVar(d.child(), makespan.value(), makespan.value());
        found = minimize(d.child(), d.counterparts(vars), cost, d::returnSolution);
        d.discard();
      }
      assertThat(found).as("seed %d", t).isEqualTo(expected);
      fixed += rule.fixedStarts();
    }
    assertThat(fixed).isPositive();
  }

  @Test
  void dualFixingKeepsSatisfiability() {
    int fixed = 0;
    for (int t = 0; t < TRIALS; t++) {
      Model model = new Model(t, false);
      Set<List<Integer>> expected = solveDirectly(model);
      Store store = new Store();
      IntVar[] vars = model.build(store);
      CumulativeReductions rule = new CumulativeReductions(true);
      Set<List<Integer>> found = solveThroughPresolve(store, vars, rule);
      assertThat(expected.containsAll(found)).as("seed %d", t).isTrue();
      assertThat(found.isEmpty()).as("seed %d", t).isEqualTo(expected.isEmpty());
      fixed += rule.fixedStarts();
    }
    assertThat(fixed).isPositive();
  }

  @Test
  void aStartAloneAtItsEarliestTimeIsFixed() {
    Store store = new Store();
    IntVar s0 = new IntVar(store, "s0", 0, 10);
    IntVar s1 = new IntVar(store, "s1", 3, 10);
    IntVar mk = new IntVar(store, "mk", 0, 20);
    IntVar two = new IntVar(store, 2, 2);
    IntVar one = new IntVar(store, 1, 1);
    store.impose(
        new Cumulative(
            new IntVar[] {s0, s1}, new IntVar[] {two, two}, new IntVar[] {one, one}, one));
    store.impose(new XplusClteqZ(s0, 2, mk));
    store.impose(new XplusClteqZ(s1, 2, mk));
    CumulativeReductions rule = new CumulativeReductions(true).objective(mk, true);
    Derivation d = Presolver.of(store).rule(rule).presolve();
    assertThat(d.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    // s0 runs alone in [0, 2), and only the makespan bounds the starts from above
    assertThat(s0.singleton(0)).isTrue();
    // once s0 is fixed, s1 runs alone from its earliest time too
    assertThat(s1.singleton(3)).isTrue();
    assertThat(rule.fixedStarts()).isEqualTo(2);
  }

  @Test
  void aUnaryResourceInsideAnotherIsRemoved() {
    Store store = new Store();
    IntVar[] s = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 10);
    }
    IntVar one = new IntVar(store, 1, 1);
    IntVar two = new IntVar(store, 2, 2);
    IntVar[] d = {two, two, two, two};
    IntVar[] u = {one, one, one, one};
    store.impose(new CumulativeUnary(s, d, u, one));
    store.impose(
        new CumulativeUnary(
            new IntVar[] {s[2], s[0]}, new IntVar[] {two, two}, new IntVar[] {one, one}, one));
    CumulativeReductions rule = new CumulativeReductions(false);
    Derivation d0 = Presolver.of(store).rule(rule).presolve();
    assertThat(d0.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    assertThat(rule.removedResources()).isEqualTo(1);
    assertThat(d0.statistics().childConstraints()).isEqualTo(1);
  }

  /** Returns the smallest cost of a solution, or Integer.MAX_VALUE if there is none. */
  private static int minimize(Store store, IntVar[] vars, IntVar cost, Runnable onSolution) {
    int[] best = {Integer.MAX_VALUE};
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            best[0] = Math.min(best[0], cost.value());
            onSolution.run();
            return result;
          }
        });
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()), cost);
    return best[0];
  }

  private static Set<List<Integer>> solveDirectly(Model model) {
    Store store = new Store();
    IntVar[] vars = model.build(store);
    Set<List<Integer>> found = new HashSet<>();
    if (store.consistency()) {
      search(store, vars, () -> found.add(values(vars)));
    }
    return found;
  }

  private static Set<List<Integer>> solveThroughPresolve(
      Store store, IntVar[] vars, CumulativeReductions rule) {
    Set<List<Integer>> found = new HashSet<>();
    // checking mode checks every solution against the constraints the rule removed
    Derivation d = Presolver.of(store).keep(vars).checking(true).rule(rule).presolve();
    if (d.outcome() == Derivation.Outcome.INFEASIBLE) {
      return found;
    }
    search(
        d.child(),
        d.counterparts(vars),
        () -> {
          if (d.returnSolution()) {
            found.add(values(vars));
          }
        });
    d.discard();
    return found;
  }

  private static List<Integer> values(IntVar[] vars) {
    return Arrays.stream(vars).map(IntVar::value).toList();
  }

  private static void search(Store store, IntVar[] vars, Runnable onSolution) {
    if (vars.length == 0) {
      onSolution.run();
      return;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            onSolution.run();
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
  }
}
