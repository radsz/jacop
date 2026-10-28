/*
 * SatPresolveTest.java
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
import java.util.function.Predicate;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * SAT preprocessing of the clauses (presolve rule 9), checked against brute force on random clause
 * sets with some variables also in a linear constraint.
 */
class SatPresolveTest {

  /** Random models per mode. */
  private static final int TRIALS = Integer.getInteger("satpresolve.trials", 3000);

  /** The value recorded for a variable postsolve leaves open, or one a projection leaves out. */
  private static final int OPEN = -1;

  /** A random model: the store, its variables, the clauses kept outside it and the solutions. */
  private record Model(
      Store store,
      IntVar[] vars,
      List<IntVar[][]> external,
      Set<List<Integer>> solutions,
      Set<IntVar> frozen) {}

  private enum Mode {
    /** No frozen variables are given: the child has exactly the parent's solutions. */
    KEEP_VARIABLES,
    /** Solution preserving: every solution once, apart from variables postsolve leaves free. */
    ALL_SOLUTIONS,
    /** Every rule: satisfiability and the values of protected variables are kept. */
    MERGE
  }

  @Test
  void childHasTheSolutionsOfTheParent() {
    for (Mode mode : Mode.values()) {
      for (int seed = 0; seed < TRIALS; seed++) {
        check(seed, mode, false);
      }
    }
  }

  @Test
  void clausesOutsideTheStoreArePreprocessedToo() {
    for (Mode mode : Mode.values()) {
      for (int seed = 0; seed < TRIALS; seed++) {
        check(seed, mode, true);
      }
    }
  }

  @Test
  void blockedClausesWithoutResolution() {
    System.setProperty("jacop.presolve.resolution", "false");
    try {
      for (int seed = 0; seed < TRIALS; seed++) {
        check(seed, Mode.MERGE, seed % 2 == 0);
      }
    } finally {
      System.clearProperty("jacop.presolve.resolution");
    }
  }

  @Test
  void subsumedClauseIsRemoved() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    store.impose(new BoolClause(new IntVar[] {a, b}, new IntVar[0]));
    store.impose(new BoolClause(new IntVar[] {a, b, c}, new IntVar[0]));
    Derivation d = Derivation.of(store).derive();
    assertThat(d.clauseStatistics().subsumed()).isEqualTo(1);
    assertThat(d.clauseStatistics().clausesAfter()).isEqualTo(1);
  }

  @Test
  void strengtheningFindsUnit() {
    // (a \/ b) and (a \/ -b) give a
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    store.impose(new BoolClause(new IntVar[] {a, b}, new IntVar[0]));
    store.impose(new BoolClause(new IntVar[] {a}, new IntVar[] {b}));
    Derivation d = Derivation.of(store).derive();
    assertThat(d.clauseStatistics().fixed()).isEqualTo(1);
    assertThat(a.singleton(1)).isTrue();
  }

  @Test
  void equivalentVariableIsRemovedAndRestored() {
    // a = b, and b \/ c, c \/ d over the other variables
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    store.impose(new XeqY(a, b));
    store.impose(new BoolClause(new IntVar[] {b, c}, new IntVar[0]));
    store.impose(new LinearInt(new IntVar[] {a, c}, new int[] {1, 1}, "<=", 1));
    Derivation d = Derivation.of(store).retention(Derivation.Retention.KEPT).keep().derive();
    assertThat(d.clauseStatistics().equivalent()).isEqualTo(1);
    assertThat(d.entry(b)).isInstanceOf(Entry.Eliminated.class);
    assertThat(d.child().consistency()).isTrue();
    IntVar[] counterparts = d.counterparts(new IntVar[] {a, c});
    List<List<Integer>> found = new ArrayList<>();
    solve(
        d.child(),
        counterparts,
        () -> {
          assertThat(d.returnSolution()).isTrue();
          found.add(List.of(a.value(), b.value(), c.value()));
        });
    assertThat(found).containsExactlyInAnyOrder(List.of(1, 1, 0), List.of(0, 0, 1));
  }

  @Test
  void variableOnlyInClausesIsEliminated() {
    // (x \/ a) /\ (-x \/ b): x is eliminated, leaving (a \/ b)
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    store.impose(new BoolClause(new IntVar[] {x, a}, new IntVar[0]));
    store.impose(new BoolClause(new IntVar[] {b}, new IntVar[] {x}));
    store.impose(new LinearInt(new IntVar[] {a, b}, new int[] {1, 1}, "<=", 1));
    Derivation d =
        Derivation.of(store)
            .retention(Derivation.Retention.KEPT)
            .keep()
            .solutionPreserving(false)
            .derive();
    assertThat(d.clauseStatistics().eliminated()).isEqualTo(1);
    assertThat(d.entry(x)).isInstanceOf(Entry.Eliminated.class);
  }

  private static void check(int seed, Mode mode, boolean external) {
    Model m = model(seed, external);
    Random r = new Random(seed * 31L + 7);
    List<Var> protect = new ArrayList<>();
    for (IntVar x : m.vars()) {
      if (r.nextInt(4) == 0) {
        protect.add(x);
      }
    }
    Derivation.Builder b = Derivation.of(m.store()).retention(Derivation.Retention.KEPT);
    if (external) {
      b.clauses(m.external());
    }
    if (mode != Mode.KEEP_VARIABLES) {
      // the variables of the constraint that is not a clause are compared too, so they are kept:
      // variable elimination (rule 8) could otherwise give one of them a single value
      b.keep(protect.toArray(new Var[0]))
          .keep(m.frozen().toArray(new Var[0]))
          .solutionPreserving(mode == Mode.ALL_SOLUTIONS);
    }
    Derivation d = b.derive();
    String what = "seed " + seed + " " + mode + (external ? " external" : "");
    if (d.outcome() == Derivation.Outcome.INFEASIBLE) {
      assertThat(m.solutions()).as(what).isEmpty();
      return;
    }
    assertThat(d.outcome()).as(what).isEqualTo(Derivation.Outcome.DERIVED);
    Store child = d.child();
    if (external) {
      for (IntVar[][] c : m.external()) {
        child.impose(new BoolClause(c[0], c[1]));
      }
    }
    List<List<Integer>> found = new ArrayList<>();
    if (child.consistency()) {
      IntVar[] counterparts = d.counterparts(m.vars());
      Runnable record =
          () -> {
            assertThat(d.returnSolution()).as(what).isTrue();
            found.add(values(m.vars()));
          };
      if (counterparts.length == 0) {
        record.run();
      } else {
        solve(child, counterparts, record);
      }
    }
    d.discard();
    // a variable postsolve leaves open is free: every value of it completes the solution
    List<List<Integer>> completed = new ArrayList<>();
    for (List<Integer> s : found) {
      completed.addAll(completions(s));
    }
    assertThat(m.solutions()).as(what).containsAll(completed);
    if (mode != Mode.MERGE) {
      assertThat(found).as(what).doesNotHaveDuplicates();
      assertThat(completed).as(what).doesNotHaveDuplicates();
      assertThat(new HashSet<>(completed)).as(what).isEqualTo(m.solutions());
      if (mode == Mode.KEEP_VARIABLES) {
        assertThat(completed).as(what).hasSameSizeAs(found);
      }
      return;
    }
    Set<IntVar> kept = new HashSet<>(m.frozen());
    protect.forEach(v -> kept.add((IntVar) v));
    assertThat(project(completed, m.vars(), kept))
        .as(what)
        .isEqualTo(project(m.solutions(), m.vars(), kept));
  }

  private static Set<List<Integer>> project(
      java.util.Collection<List<Integer>> solutions, IntVar[] vars, Set<IntVar> kept) {
    Set<List<Integer>> result = new HashSet<>();
    for (List<Integer> s : solutions) {
      result.add(project(s, vars, kept));
    }
    return result;
  }

  private static List<Integer> project(List<Integer> solution, IntVar[] vars, Set<IntVar> kept) {
    List<Integer> p = new ArrayList<>();
    for (int i = 0; i < vars.length; i++) {
      p.add(kept.contains(vars[i]) ? solution.get(i) : OPEN);
    }
    return p;
  }

  /** The assignments that give each open variable of a solution the value 0 or 1. */
  private static List<List<Integer>> completions(List<Integer> solution) {
    List<List<Integer>> result = new ArrayList<>();
    result.add(new ArrayList<>(solution));
    for (int i = 0; i < solution.size(); i++) {
      if (solution.get(i) == OPEN) {
        List<List<Integer>> next = new ArrayList<>();
        for (List<Integer> s : result) {
          for (int value = 0; value <= 1; value++) {
            List<Integer> t = new ArrayList<>(s);
            t.set(i, value);
            next.add(t);
          }
        }
        result = next;
      }
    }
    return result;
  }

  private static Model model(int seed, boolean externalClauses) {
    Random r = new Random(seed);
    Store store = new Store();
    int n = 3 + r.nextInt(8);
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = r.nextInt(3) == 0 ? new BooleanVar(store, "x" + i) : new IntVar(store, "x" + i, 0, 1);
    }
    IntVar one = new IntVar(store, "one", 1, 1);
    IntVar zero = new IntVar(store, "zero", 0, 0);
    List<Predicate<int[]>> checks = new ArrayList<>();
    List<IntVar[][]> external = new ArrayList<>();
    Set<IntVar> frozen = new HashSet<>();
    int m = 1 + r.nextInt(3 * n);
    for (int k = 0; k < m; k++) {
      int kind = r.nextInt(12);
      int i = r.nextInt(n);
      int j = (i + 1 + r.nextInt(n - 1)) % n;
      switch (kind) {
        case 0 -> {
          store.impose(new XeqY(x[i], x[j]));
          checks.add(v -> v[i] == v[j]);
        }
        case 1 -> {
          store.impose(new XneqY(x[i], x[j]));
          checks.add(v -> v[i] != v[j]);
        }
        case 2 -> {
          store.impose(new XlteqY(x[i], x[j]));
          checks.add(v -> v[i] <= v[j]);
        }
        case 3, 4 -> {
          int[] idx = distinct(r, n, 2 + r.nextInt(Math.min(3, n - 1)));
          IntVar[] list = Arrays.stream(idx).mapToObj(t -> x[t]).toArray(IntVar[]::new);
          if (kind == 3) {
            store.impose(new OrBoolVector(list, one));
            checks.add(v -> Arrays.stream(idx).anyMatch(t -> v[t] == 1));
          } else {
            store.impose(new AndBoolVector(list, zero));
            checks.add(v -> Arrays.stream(idx).anyMatch(t -> v[t] == 0));
          }
        }
        default -> {
          int len = 1 + r.nextInt(Math.min(4, n));
          int[] pos = new int[r.nextInt(len + 1)];
          int[] neg = new int[len - pos.length];
          for (int t = 0; t < pos.length; t++) {
            pos[t] = r.nextInt(n);
          }
          for (int t = 0; t < neg.length; t++) {
            neg[t] = r.nextInt(n);
          }
          IntVar[] p = Arrays.stream(pos).mapToObj(t -> x[t]).toArray(IntVar[]::new);
          IntVar[] q = Arrays.stream(neg).mapToObj(t -> x[t]).toArray(IntVar[]::new);
          if (externalClauses && r.nextBoolean()) {
            external.add(new IntVar[][] {p, q});
          } else {
            store.impose(new BoolClause(p, q));
          }
          checks.add(
              v ->
                  Arrays.stream(pos).anyMatch(t -> v[t] == 1)
                      || Arrays.stream(neg).anyMatch(t -> v[t] == 0));
        }
      }
    }
    if (r.nextBoolean()) {
      // a constraint that is not a clause: its variables keep their meaning
      int[] idx = distinct(r, n, 2 + r.nextInt(Math.min(3, n - 1)));
      IntVar[] list = Arrays.stream(idx).mapToObj(t -> x[t]).toArray(IntVar[]::new);
      int bound = r.nextInt(idx.length);
      int[] w = new int[idx.length];
      Arrays.fill(w, 1);
      store.impose(new LinearInt(list, w, "<=", bound));
      checks.add(v -> Arrays.stream(idx).map(t -> v[t]).sum() <= bound);
      frozen.addAll(Arrays.asList(list));
    }
    Set<List<Integer>> solutions = new HashSet<>();
    int[] v = new int[n];
    for (int mask = 0; mask < 1 << n; mask++) {
      for (int t = 0; t < n; t++) {
        v[t] = (mask >> t) & 1;
      }
      if (checks.stream().allMatch(c -> c.test(v))) {
        solutions.add(Arrays.stream(v).boxed().toList());
      }
    }
    return new Model(store, x, external, solutions, frozen);
  }

  private static int[] distinct(Random r, int n, int k) {
    List<Integer> all = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      all.add(i);
    }
    java.util.Collections.shuffle(all, r);
    return all.subList(0, Math.min(k, n)).stream().mapToInt(Integer::intValue).toArray();
  }

  private static List<Integer> values(IntVar[] vars) {
    return Arrays.stream(vars).map(x -> x.singleton() ? x.value() : OPEN).toList();
  }

  private static void solve(Store store, IntVar[] vars, Runnable onSolution) {
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
