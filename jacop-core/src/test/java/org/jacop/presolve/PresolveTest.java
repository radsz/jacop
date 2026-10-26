/*
 * PresolveTest.java
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
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Consumer;
import org.jacop.api.Copyable;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.StoreState;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Presolve on random small models: the solutions found through a derived store, returned to the
 * original store, are those of the original model.
 */
class PresolveTest {

  private static final int TRIALS = 400;

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  /** A random model over integer and Boolean variables, imposed on a given store. */
  private record Model(int[][] domains, int booleans, Consumer<Model.Vars> impose) {

    record Vars(Store store, IntVar[] x, BooleanVar[] b) {}

    Vars build() {
      Store store = new Store();
      IntVar[] x = new IntVar[domains.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, domains[i][0], domains[i][1]);
      }
      BooleanVar[] b = new BooleanVar[booleans];
      for (int i = 0; i < b.length; i++) {
        b[i] = new BooleanVar(store, "b" + i);
      }
      Vars vars = new Vars(store, x, b);
      impose.accept(vars);
      return vars;
    }
  }

  @Test
  void randomModelsHaveTheSameSolutionsThroughPresolve() {
    Random random = new Random(20261025);
    int derived = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Model model = randomModel(random);
      Set<List<Integer>> expected = solveDirectly(model);
      boolean checking = trial % 2 == 0;
      Result result = solveThroughPresolve(model, checking, -1, 0, random.nextInt());
      assertThat(result.solutions())
          .as("trial %d, checking %b", trial, checking)
          .isEqualTo(expected);
      if (result.outcome() == Derivation.Outcome.DERIVED) {
        derived++;
      }
    }
    // every constraint of the random models can be copied
    assertThat(derived).isGreaterThan(TRIALS / 2);
  }

  @Test
  void randomModelsHaveTheSameSolutionsWhenDerivedAboveLevelZero() {
    Random random = new Random(20261026);
    for (int trial = 0; trial < TRIALS; trial++) {
      Model model = randomModel(random);
      int restricted = random.nextInt(model.domains().length);
      int[] range = model.domains()[restricted];
      int kept = range[0] + random.nextInt(range[1] - range[0] + 1);
      Set<List<Integer>> expected = solveDirectly(model);
      expected.removeIf(s -> s.get(restricted) != kept);
      boolean checking = trial % 2 == 0;
      Result result = solveThroughPresolve(model, checking, restricted, kept, random.nextInt());
      assertThat(result.solutions())
          .as("trial %d, x%d = %d at level 1, checking %b", trial, restricted, kept, checking)
          .isEqualTo(expected);
    }
  }

  @Test
  void entailedConstraintsAreNotCopied() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 1);
    IntVar y = new IntVar(store, "y", 2, 2);
    IntVar z = new IntVar(store, "z", 0, 9);
    IntVar w = new IntVar(store, "w", 0, 9);
    IntVar u = new IntVar(store, "u", 0, 9);
    store.impose(new XltY(x, y));
    store.impose(new XplusYeqZ(x, y, z));
    store.impose(new XplusYeqZ(w, x, u));

    Derivation derivation = Presolver.of(store).keep(w, u).presolve();

    assertThat(derivation.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    // x < y has fixed variables only, and x + y = z fixed z at the fixpoint; the store may have
    // detached the first already
    Derivation.Statistics statistics = derivation.statistics();
    assertThat(statistics.childConstraints()).isEqualTo(1);
    assertThat(statistics.dropped()).isEqualTo(statistics.parentConstraints() - 1);
    assertThat(derivation.entry(x)).isInstanceOf(Entry.Kept.class);
    assertThat(derivation.entry(y)).isInstanceOf(Entry.Fixed.class);
    assertThat(derivation.entry(z)).isInstanceOf(Entry.Fixed.class);
    assertThat(derivation.get(w).max()).isEqualTo(8);
  }

  // a derived variable keeps the static degree of its parent, which degree-based selections read
  @Test
  void derivedVariablesKeepTheStaticDegreeOfTheParent() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 1);
    IntVar y = new IntVar(store, "y", 0, 9);
    IntVar z = new IntVar(store, "z", 0, 9);
    IntVar w = new IntVar(store, "w", 0, 9);
    store.impose(new XltY(x, y));
    store.impose(new XplusYeqZ(y, z, w));
    store.impose(new Alldifferent(new IntVar[] {y, z, w}).setDegreeWeight(2));
    store.impose(new XltY(z, w).setDegreeWeight(0));
    y.adjustDegree(4);
    // at the fixpoint the store may have detached x < y already
    assertThat(store.consistency()).isTrue();
    int[] parent = {
      y.sizeConstraintsOriginal(), z.sizeConstraintsOriginal(), w.sizeConstraintsOriginal()
    };
    assertThat(parent[0]).isBetween(7, 8);
    assertThat(parent[1]).isEqualTo(3);
    assertThat(parent[2]).isEqualTo(3);

    Derivation derivation = Presolver.of(store).presolve();

    assertThat(derivation.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    // x < y is entailed and not copied
    assertThat(derivation.statistics().childConstraints()).isEqualTo(3);
    assertThat(
            new int[] {
              derivation.get(y).sizeConstraintsOriginal(),
              derivation.get(z).sizeConstraintsOriginal(),
              derivation.get(w).sizeConstraintsOriginal()
            })
        .containsExactly(parent);
  }

  @Test
  void aConstraintThatCannotBeCopiedKeepsTheLiveStore() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    store.impose(new XltY(x, y));
    store.impose(
        new Constraint(new IntVar[] {x}) {
          @Override
          public void consistency(Store s) {
            x.domain.inComplement(s.level, x, 1);
          }
        });

    Derivation derivation = Presolver.of(store).keep(x, y).presolve();

    assertThat(derivation.outcome()).isEqualTo(Derivation.Outcome.LIVE);
    assertThat(derivation.child()).isSameAs(store);
    assertThat(derivation.get(x)).isSameAs(x);
    assertThat(store.state()).isEqualTo(StoreState.ACTIVE);
  }

  @Test
  void anInheritedCopyDoesNotMakeASubclassCopyable() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);

    assertThat(Copyable.canCopy(new XltY(x, y))).isTrue();
    assertThat(Copyable.canCopy(new XltY(x, y) {})).isFalse();
    assertThat(Copyable.canCopy(new Not(new XltY(x, y)))).isTrue();
    assertThat(Copyable.canCopy(new Not(new XltY(x, y) {}))).isFalse();
  }

  @Test
  void aReleasedParentRefusesNewConstraintsAndAKeptParentIsActiveAfterDiscard() {
    Store released = new Store();
    IntVar x = new IntVar(released, "x", 0, 3);
    IntVar y = new IntVar(released, "y", 0, 3);
    released.impose(new XltY(x, y));
    Derivation d1 = Presolver.of(released).presolve();
    assertThat(released.state()).isEqualTo(StoreState.SINK);
    assertThatThrownBy(() -> released.impose(new XneqY(x, y)))
        .isInstanceOf(IllegalStateException.class);
    d1.discard();
    assertThat(released.state()).isEqualTo(StoreState.CLOSED);

    Store kept = new Store();
    IntVar u = new IntVar(kept, "u", 0, 3);
    IntVar v = new IntVar(kept, "v", 0, 3);
    kept.impose(new XltY(u, v));
    Derivation d2 = Presolver.of(kept).checking(true).presolve();
    assertThat(kept.state()).isEqualTo(StoreState.SUSPENDED);
    d2.child().impose(new XeqC(d2.get(u), 2));
    assertThat(d2.child().consistency()).isTrue();
    assertThat(d2.returnSolution()).isTrue();
    assertThat(u.value()).isEqualTo(2);
    assertThat(v.value()).isEqualTo(3);
    d2.discard();
    assertThat(kept.state()).isEqualTo(StoreState.ACTIVE);
    assertThat(u.max()).isEqualTo(2);
    assertThat(v.dom().getSize()).isEqualTo(3);
  }

  @Test
  void recordingKeepsEveryImposedConstraintIncludingDecompositions() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    store.impose(new XltY(x, y));
    store.recordModel(true);
    XneqY first = new XneqY(x, y);
    store.impose(first);
    store.imposeDecomposition(new Lex(new IntVar[][] {{x}, {y}}, true));

    assertThat(store.model()).first().isSameAs(first);
    // the decomposition's constraints are imposed through the store and recorded too
    assertThat(store.model().size()).isGreaterThan(1);
    store.recordModel(false);
    assertThat(store.model()).isEmpty();
  }

  private record Result(Derivation.Outcome outcome, Set<List<Integer>> solutions) {}

  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(3);
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      int min = random.nextInt(3) - 1;
      domains[i] = new int[] {min, min + random.nextInt(4)};
    }
    int booleans = random.nextInt(3);
    int constraints = 1 + random.nextInt(4);
    long seed = random.nextLong();
    return new Model(
        domains,
        booleans,
        vars -> {
          Random r = new Random(seed);
          for (int k = 0; k < constraints; k++) {
            vars.store().impose(randomConstraint(r, vars));
          }
        });
  }

  private static Constraint randomConstraint(Random r, Model.Vars vars) {
    IntVar[] x = vars.x();
    IntVar[] all = new IntVar[x.length + vars.b().length];
    System.arraycopy(x, 0, all, 0, x.length);
    System.arraycopy(vars.b(), 0, all, x.length, vars.b().length);
    IntVar[] three = distinct(r, x, 3);
    IntVar a = three[0];
    IntVar c = three[1];
    IntVar d = three[2];
    IntVar[] bools = vars.b().length > 0 ? vars.b() : null;
    switch (r.nextInt(12)) {
      case 0:
        {
          int[] w = new int[x.length];
          for (int i = 0; i < w.length; i++) {
            w[i] = r.nextInt(5) - 2;
          }
          return new LinearInt(x, w, RELATIONS[r.nextInt(RELATIONS.length)], r.nextInt(5) - 2);
        }
      case 1:
        return new XplusYeqZ(a, c, d);
      case 2:
        return bools != null
            ? new Reified(new XeqC(a, r.nextInt(3)), bools[0])
            : new XeqC(a, r.nextInt(3));
      case 3:
        return new Alldifferent(distinct(r, x, 2 + r.nextInt(2)));
      case 4:
        return new ElementInteger(a, new int[] {r.nextInt(3), r.nextInt(3), r.nextInt(3)}, c, 0);
      case 5:
        return bools != null
            ? new SumBool(bools, RELATIONS[r.nextInt(RELATIONS.length)], a)
            : new XltY(a, c);
      case 6:
        return bools != null
            ? new BoolClause(new IntVar[] {bools[0]}, new IntVar[] {bools[bools.length - 1]})
            : new XneqY(a, c);
      case 7:
        {
          int[][] tuples = new int[2 + r.nextInt(5)][];
          for (int t = 0; t < tuples.length; t++) {
            tuples[t] = new int[] {r.nextInt(4) - 1, r.nextInt(4) - 1};
          }
          return new HybridTable(distinct(r, x, 2), tuples);
        }
      case 8:
        return new Count(distinct(r, x, 3), a, r.nextInt(3));
      case 9:
        return new IfThen(
            new XgtY(a, c), new Or(new PrimitiveConstraint[] {new XeqC(d, 0), new XneqY(a, d)}));
      case 10:
        return new Max(distinct(r, x, 2), d);
      default:
        return r.nextBoolean()
            ? new AbsXeqY(a, c)
            : new SumWeight(
                distinct(r, all, 2), new int[] {1 + r.nextInt(2), -1}, r.nextInt(3) - 1);
    }
  }

  private static IntVar[] distinct(Random r, IntVar[] x, int k) {
    List<IntVar> pool = new ArrayList<>(Arrays.asList(x));
    IntVar[] result = new IntVar[Math.min(k, pool.size())];
    for (int i = 0; i < result.length; i++) {
      result[i] = pool.remove(r.nextInt(pool.size()));
    }
    return result;
  }

  private static Set<List<Integer>> solveDirectly(Model model) {
    Model.Vars vars = model.build();
    Set<List<Integer>> found = new HashSet<>();
    if (!vars.store().consistency()) {
      return found;
    }
    IntVar[] decisions = decisions(vars);
    search(vars.store(), decisions, 0, () -> found.add(values(decisions)));
    return found;
  }

  private static Result solveThroughPresolve(
      Model model, boolean checking, int restricted, int kept, int seed) {
    Model.Vars vars = model.build();
    Store store = vars.store();
    IntVar[] decisions = decisions(vars);
    Set<List<Integer>> found = new HashSet<>();
    if (restricted >= 0) {
      store.setLevel(1);
      try {
        vars.x()[restricted].domain.in(store.level, vars.x()[restricted], kept, kept);
      } catch (FailException e) {
        return new Result(Derivation.Outcome.INFEASIBLE, found);
      }
    }
    Derivation derivation = Presolver.of(store).keep(decisions).checking(checking).presolve();
    if (derivation.outcome() == Derivation.Outcome.INFEASIBLE) {
      return new Result(derivation.outcome(), found);
    }
    IntVar[] counterparts = derivation.counterparts(decisions);
    search(
        derivation.child(),
        counterparts,
        seed,
        () -> {
          if (derivation.returnSolution()) {
            found.add(values(decisions));
          }
        });
    derivation.discard();
    return new Result(derivation.outcome(), found);
  }

  private static IntVar[] decisions(Model.Vars vars) {
    IntVar[] decisions = Arrays.copyOf(vars.x(), vars.x().length + vars.b().length);
    System.arraycopy(vars.b(), 0, decisions, vars.x().length, vars.b().length);
    return decisions;
  }

  private static List<Integer> values(IntVar[] vars) {
    return Arrays.stream(vars).map(IntVar::value).toList();
  }

  private static void search(Store store, IntVar[] vars, int seed, Runnable onSolution) {
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
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainRandom<>(seed)));
  }
}
