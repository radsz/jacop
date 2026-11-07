/*
 * ProbingTest.java
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
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Root probing removes only values that belong to no solution, and finds what propagation misses.
 */
class ProbingTest {

  private static final int TRIALS = 300;

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  @Test
  void shavingRemovesBoundsThatPropagationKeeps() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 2);
    IntVar y = new IntVar(store, "y", 1, 2);
    IntVar z = new IntVar(store, "z", 1, 2);
    pairwiseDifferent(store, x, y, z);
    assertThat(store.consistency()).isTrue();
    assertThat(x.getSize()).isEqualTo(3);

    Probing.Result result = Probing.of(store).mode(Probing.Mode.SHAVE).probe();

    assertThat(result.feasible()).isTrue();
    assertThat(x.singleton(0)).isTrue();
    assertThat(result.failed()).isEqualTo(2);
    assertThat(result.removed()).isEqualTo(2);
    assertThat(store.level).isZero();
  }

  @Test
  void sacRemovesAnInnerValueThatShavingKeeps() {
    IntVar[] shaved = innerValueModel();
    Probing.of(shaved[0].getStore()).mode(Probing.Mode.SHAVE).probe();
    assertThat(shaved[0].dom().contains(1)).isTrue();

    IntVar[] sac = innerValueModel();
    Probing.Result result = Probing.of(sac[0].getStore()).mode(Probing.Mode.SAC).probe();
    assertThat(result.feasible()).isTrue();
    assertThat(sac[0].dom().eq(new IntervalDomain(0, 0).union(2))).isTrue();
  }

  private static IntVar[] innerValueModel() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 2);
    IntVar y = new IntVar(store, "y", new IntervalDomain(1, 1).union(5));
    IntVar z = new IntVar(store, "z", new IntervalDomain(1, 1).union(5));
    pairwiseDifferent(store, x, y, z);
    return new IntVar[] {x, y, z};
  }

  @Test
  void aFailedLiteralFixesTheBooleanToTheOtherValue() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 2);
    IntVar y = new IntVar(store, "y", 1, 2);
    IntVar z = new IntVar(store, "z", 1, 2);
    BooleanVar b = new BooleanVar(store, "b");
    store.impose(new XneqY(y, z));
    store.impose(new Reified(new XeqC(x, 2), b));
    // b = 1 forces y = z = 1, which propagation sees only once b is set
    store.impose(new IfThen(new XeqC(b, 1), new XeqC(y, 1)));
    store.impose(new IfThen(new XeqC(b, 1), new XeqC(z, 1)));
    assertThat(store.consistency()).isTrue();
    assertThat(b.singleton()).isFalse();

    Probing.Result result = Probing.of(store).mode(Probing.Mode.SHAVE).probe();

    assertThat(result.feasible()).isTrue();
    assertThat(b.singleton(0)).isTrue();
    assertThat(x.dom().contains(2)).isFalse();
  }

  @Test
  void bothLiteralsNarrowAVariableToTheHullOfItsBranches() {
    Store store = new Store();
    // a 0-1 integer variable created first is probed before x is shaved
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar x = new IntVar(store, "x", 0, 10);
    store.impose(new IfThen(new XeqC(b, 1), new XeqC(x, 3)));
    store.impose(new IfThen(new XeqC(b, 0), new XeqC(x, 5)));
    assertThat(store.consistency()).isTrue();
    assertThat(x.min()).isZero();

    Probing.Result result = Probing.of(store).mode(Probing.Mode.SHAVE).probe();

    assertThat(result.feasible()).isTrue();
    assertThat(result.narrowed()).isPositive();
    assertThat(x.min()).isEqualTo(3);
    assertThat(x.max()).isEqualTo(5);
  }

  @Test
  void probingProvesInfeasibilityThatPropagationMisses() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 2);
    IntVar y = new IntVar(store, "y", 1, 2);
    IntVar z = new IntVar(store, "z", 1, 2);
    pairwiseDifferent(store, x, y, z);

    Derivation d = Presolver.of(store).probing(Probing.Mode.SHAVE, 1000).presolve();

    assertThat(d.outcome()).isEqualTo(Derivation.Outcome.INFEASIBLE);
    assertThat(d.rules())
        .filteredOn(ProbingRule.class::isInstance)
        .singleElement()
        .satisfies(r -> assertThat(((ProbingRule) r).result().feasible()).isFalse());
  }

  @Test
  void aZeroBudgetProbesNothing() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 2);
    pairwiseDifferent(store, x, new IntVar(store, "y", 1, 2), new IntVar(store, "z", 1, 2));

    Probing.Result result = Probing.of(store).budget(0).probe();

    assertThat(result.exhausted()).isTrue();
    assertThat(x.getSize()).isEqualTo(3);
  }

  @Test
  void randomModelsKeepTheirSolutions() {
    Random random = new Random(20261027);
    int changed = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = random.nextLong();
      Probing.Mode mode = trial % 2 == 0 ? Probing.Mode.SHAVE : Probing.Mode.SAC;
      Set<List<Integer>> expected = solutions(seed, null);
      Probing.Result[] result = new Probing.Result[1];
      Set<List<Integer>> probed = solutions(seed, store -> result[0] = probe(store, mode));
      assertThat(probed).as("trial %d, %s", trial, mode).isEqualTo(expected);
      if (result[0] != null && result[0].changed()) {
        changed++;
        assertThat(result[0].feasible() || expected.isEmpty()).isTrue();
      }
    }
    // the random models give probing something to remove
    assertThat(changed).isGreaterThan(TRIALS / 10);
  }

  @Test
  void randomModelsKeepTheirSolutionsThroughPresolve() {
    Random random = new Random(20261028);
    for (int trial = 0; trial < TRIALS / 3; trial++) {
      long seed = random.nextLong();
      Set<List<Integer>> expected = solutions(seed, null);
      Model m = model(seed);
      Derivation d =
          Presolver.of(m.store())
              .keep(m.all())
              .checking(trial % 2 == 0)
              .probing(Probing.Mode.SAC, 1000)
              .presolve();
      Set<List<Integer>> found = new HashSet<>();
      if (d.outcome() != Derivation.Outcome.INFEASIBLE) {
        search(
            d.child(),
            d.counterparts(m.all()),
            () -> {
              if (d.returnSolution()) {
                found.add(values(m.all()));
              }
            });
        d.discard();
      }
      assertThat(found).as("trial %d", trial).isEqualTo(expected);
    }
  }

  private static Probing.Result probe(Store store, Probing.Mode mode) {
    return Probing.of(store).mode(mode).budget(10_000).probe();
  }

  private interface Step {
    Object apply(Store store);
  }

  private record Model(Store store, IntVar[] all) {}

  /**
   * A random model with weak propagation (pairwise disequalities, sums, reified equalities and
   * implications), so probing has values to remove.
   */
  private static Model model(long seed) {
    Random r = new Random(seed);
    Store store = new Store();
    int n = 4 + r.nextInt(3);
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      int min = r.nextInt(3);
      x[i] = new IntVar(store, "x" + i, min, min + 1 + r.nextInt(4));
    }
    BooleanVar[] b = new BooleanVar[2 + r.nextInt(2)];
    for (int i = 0; i < b.length; i++) {
      b[i] = new BooleanVar(store, "b" + i);
    }
    int constraints = 3 + r.nextInt(5);
    for (int k = 0; k < constraints; k++) {
      IntVar a = x[r.nextInt(n)];
      IntVar c = x[r.nextInt(n)];
      IntVar d = x[r.nextInt(n)];
      BooleanVar l = b[r.nextInt(b.length)];
      switch (r.nextInt(6)) {
        case 0 -> {
          if (a != c) {
            store.impose(new XneqY(a, c));
          }
        }
        case 1 -> store.impose(new XplusYeqZ(a, c, d));
        case 2 -> store.impose(new Reified(new XeqC(a, r.nextInt(4)), l));
        case 3 -> store.impose(new IfThen(new XeqC(l, r.nextInt(2)), new XeqC(a, r.nextInt(5))));
        case 4 -> {
          int[] w = new int[n];
          for (int i = 0; i < n; i++) {
            w[i] = r.nextInt(3) - 1;
          }
          store.impose(
              new LinearInt(x, w, RELATIONS[r.nextInt(RELATIONS.length)], r.nextInt(7) - 3));
        }
        default -> {
          List<IntVar> pool = new ArrayList<>(Arrays.asList(x));
          java.util.Collections.shuffle(pool, r);
          store.impose(new Alldifferent(pool.subList(0, 3).toArray(new IntVar[0])));
        }
      }
    }
    IntVar[] all = Arrays.copyOf(x, n + b.length);
    System.arraycopy(b, 0, all, n, b.length);
    return new Model(store, all);
  }

  private static Set<List<Integer>> solutions(long seed, Step before) {
    Model m = model(seed);
    Set<List<Integer>> found = new HashSet<>();
    if (!m.store().consistency()) {
      return found;
    }
    if (before != null) {
      Object result = before.apply(m.store());
      if (result instanceof Probing.Result p && !p.feasible()) {
        return found;
      }
    }
    search(m.store(), m.all(), () -> found.add(values(m.all())));
    return found;
  }

  private static void pairwiseDifferent(Store store, IntVar... vars) {
    for (int i = 0; i < vars.length; i++) {
      for (int j = i + 1; j < vars.length; j++) {
        store.impose(new XneqY(vars[i], vars[j]));
      }
    }
  }

  private static List<Integer> values(IntVar[] vars) {
    return Arrays.stream(vars).map(IntVar::value).toList();
  }

  private static void search(Store store, IntVar[] vars, Runnable onSolution) {
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
