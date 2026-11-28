/*
 * AffineSubstitutionTest.java
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
import java.util.function.Consumer;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.table.Table;
import org.jacop.core.AffineView;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Rule 2 of presolve, affine equality substitution: the classes found, the child it gives, and
 * random models whose solutions must not change.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class AffineSubstitutionTest {

  private static final int TRIALS = 400;

  @Test
  void aChainOfAffineEqualitiesBecomesViewsOfOneVariable() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", -20, 20);
    IntVar z = new IntVar(store, "z", -50, 50);
    IntVar w = new IntVar(store, "w", -30, 30);
    store.impose(new XplusCeqZ(x, 3, y)); // y = x + 3
    store.impose(new XmulCeqZ(y, -2, z)); // z = -2y
    store.impose(new Alldifferent(new IntVar[] {x, w}));
    store.impose(new XltY(z, w));

    Derivation d = Presolver.of(store).presolve();

    assertThat(d.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    assertThat(d.affineSubstituted()).isEqualTo(2);
    assertThat(d.statistics().dropped()).isEqualTo(2);
    assertThat(d.statistics().childConstraints()).isEqualTo(2);
    IntVar cx = d.get(x);
    assertThat(cx).isNotInstanceOf(AffineView.class);
    AffineView cz = (AffineView) d.get(z);
    assertThat(cz.base()).isSameAs(cx);
    assertThat(cz.factor()).isEqualTo(-2);
    assertThat(cz.offset()).isEqualTo(-6);
    assertThat(((AffineView) d.get(y)).offset()).isEqualTo(3);
  }

  @Test
  void theRepresentativeKeepsOnlyValuesEveryMemberAllows() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 9);
    IntVar y = new IntVar(store, "y", 0, 20);
    y.domain.inComplement(0, y, 4);
    y.domain.inComplement(0, y, 10);
    store.impose(new XmulCeqZ(x, 2, y)); // bounds consistency leaves x = 2 and x = 5 in x
    store.impose(new XneqY(x, new IntVar(store, "v", 0, 0)));

    Derivation d = Presolver.of(store).presolve();

    assertThat(d.get(x).dom().contains(2)).isFalse();
    assertThat(d.get(x).dom().contains(5)).isFalse();
    assertThat(d.get(y).dom().contains(6)).isTrue();
  }

  @Test
  void anEmptyClassMakesTheDerivationInfeasible() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 1, 1);
    y.addDom(3, 3);
    store.impose(new XmulCeqZ(x, 2, y));

    assertThat(Presolver.of(store).presolve().outcome()).isEqualTo(Derivation.Outcome.INFEASIBLE);
  }

  @Test
  void aViewPrunedByADomainReachingTheEndOfTheRangeStaysValid() {
    // the preimage of MIN_INT..5 under u + 2 starts below MIN_INT; it used to be kept as such, and
    // the complement taken by SmallDenseDomain.in with asserts on threw
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    AffineView v = new AffineView(store, "v", x, 1, 2);
    store.setLevel(1);
    v.domain.in(store.level, v, new IntervalDomain(IntDomain.MIN_INT, 5));
    assertThat(x.max()).isEqualTo(3);
    v.domain.in(store.level, v, new IntervalDomain(-4, IntDomain.MAX_INT));
    assertThat(x.min()).isZero();
    AffineView w = new AffineView(store, "w", x, -1, -2);
    w.domain.in(store.level, w, new IntervalDomain(IntDomain.MIN_INT, -3));
    assertThat(x.min()).isEqualTo(1);
  }

  @Test
  void anEqualityThatClosesACycleIsKeptUnlessImplied() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", 0, 10);
    IntVar z = new IntVar(store, "z", 0, 10);
    store.impose(new XplusCeqZ(x, 1, y));
    store.impose(new XplusCeqZ(y, 1, z));
    store.impose(new XplusCeqZ(x, 2, z)); // implied by the first two
    store.impose(new XplusYeqC(x, z, 6)); // with them, x = 2; root propagation does not see it

    Derivation d = Presolver.of(store).keep(x, y, z).presolve();

    // the third offset is implied and goes; x + z = 6, which closes a cycle that is not implied,
    // stays, and as it has two members of the class they keep copies tied by equalities
    IntVar[] vars = {x, y, z};
    Set<List<Integer>> found = new HashSet<>();
    search(
        d.child(),
        d.counterparts(vars),
        1,
        () -> {
          if (d.returnSolution()) {
            found.add(values(vars));
          }
        });
    assertThat(found).containsExactly(List.of(2, 3, 4));
  }

  @Test
  void variablesInOneConstraintWithTheirRepresentativeKeepACopy() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 4);
    IntVar y = new IntVar(store, "y", 0, 4);
    store.impose(new XplusCeqZ(x, 1, y));
    store.impose(new Alldifferent(new IntVar[] {x, y}));

    Derivation d = Presolver.of(store).presolve();

    assertThat(d.get(y)).isNotInstanceOf(AffineView.class);
    assertThat(d.get(y)).isNotSameAs(d.get(x));
    assertThat(d.affineSubstituted()).isZero();
  }

  @Test
  void booleanVariablesAreOnlyAliasesOfBooleanVariables() {
    Store store = new Store();
    BooleanVar a = new BooleanVar(store, "a");
    BooleanVar b = new BooleanVar(store, "b");
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    store.impose(new XeqY(a, b));
    store.impose(new XeqY(x, a));
    store.impose(new XplusYeqC(y, b, 1)); // y = 1 - b is not an alias, so it stays
    store.impose(new SumBool(new IntVar[] {a, y}, "==", new IntVar(store, "s", 1, 1)));
    store.impose(new XneqY(x, new IntVar(store, "t", 0, 2)));

    Derivation d = Presolver.of(store).presolve();

    // the equations over 0/1 variables may also go to the SAT preprocessing as clauses; either
    // way no Boolean variable or 0/1 variable tied to one becomes a view
    assertThat(d.get(a)).isInstanceOf(BooleanVar.class);
    assertThat(d.get(b)).isNotInstanceOf(AffineView.class);
    assertThat(d.get(x)).isNotInstanceOf(AffineView.class);
    assertThat(d.get(y)).isNotInstanceOf(AffineView.class);
  }

  @Test
  void withoutViewsOnlyAliasesAreSubstituted() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", 0, 10);
    IntVar z = new IntVar(store, "z", 0, 10);
    // a linear equation, as XeqY goes to the aliasing of equal domains before rule 2
    store.impose(new LinearInt(new IntVar[] {x, y}, new int[] {1, -1}, "==", 0));
    store.impose(new XplusCeqZ(x, 1, z));
    store.impose(new XneqY(y, z));

    Derivation d = Presolver.of(store).views(false).presolve();

    assertThat(d.get(y)).isSameAs(d.get(x));
    assertThat(d.get(z)).isNotInstanceOf(AffineView.class);
    assertThat(d.affineSubstituted()).isEqualTo(1);
  }

  @Test
  void randomModelsWithAffineEqualitiesHaveTheSameSolutions() {
    Random random = new Random(20261027);
    int substituted = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Model model = randomModel(random);
      Set<List<Integer>> expected = solveDirectly(model);
      boolean checking = trial % 2 == 0;
      boolean views = trial % 3 != 0;
      int seed = random.nextInt();
      Model.Vars vars = model.build();
      Set<List<Integer>> found = new HashSet<>();
      IntVar[] decisions = decisions(vars);
      Derivation d =
          Presolver.of(vars.store()).keep(decisions).checking(checking).views(views).presolve();
      if (d.outcome() != Derivation.Outcome.INFEASIBLE) {
        substituted += d.affineSubstituted();
        search(
            d.child(),
            d.counterparts(decisions),
            seed,
            () -> {
              if (d.returnSolution()) {
                found.add(values(decisions));
              }
            });
        d.discard();
      }
      assertThat(found)
          .as("trial %d, checking %b, views %b", trial, checking, views)
          .isEqualTo(expected);
    }
    assertThat(substituted).isGreaterThan(TRIALS / 16);
  }

  /** A random model over integer and Boolean variables, imposed on a fresh store. */
  private record Model(int[][] domains, int booleans, Consumer<Model.Vars> impose) {

    record Vars(Store store, IntVar[] x, BooleanVar[] b) {}

    Vars build() {
      Store store = new Store();
      IntVar[] x = new IntVar[domains.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, domains[i][0], domains[i][1]);
        if (domains[i].length > 2) {
          x[i].domain.inComplement(0, x[i], domains[i][2]);
        }
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

  private static Model randomModel(Random random) {
    int n = 4 + random.nextInt(3);
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      int min = random.nextInt(5) - 2;
      int max = min + 1 + random.nextInt(5);
      domains[i] =
          random.nextInt(3) == 0
              ? new int[] {min, max, min + 1 + random.nextInt(max - min)}
              : new int[] {min, max};
    }
    int booleans = random.nextInt(3);
    int equalities = 1 + random.nextInt(3);
    int others = random.nextInt(3);
    long seed = random.nextLong();
    return new Model(
        domains,
        booleans,
        vars -> {
          Random r = new Random(seed);
          for (int k = 0; k < equalities; k++) {
            vars.store().impose(randomEquality(r, vars));
          }
          for (int k = 0; k < others; k++) {
            vars.store().impose(randomConstraint(r, vars));
          }
        });
  }

  private static Constraint randomEquality(Random r, Model.Vars vars) {
    IntVar[] x = vars.x();
    IntVar[] two = distinct(r, x, 2);
    IntVar a = two[0];
    IntVar c = two[1];
    BooleanVar[] b = vars.b();
    switch (r.nextInt(7)) {
      case 0:
        return new XeqY(a, c);
      case 1:
        return new XplusCeqZ(a, r.nextInt(5) - 2, c);
      case 2:
        return new XmulCeqZ(a, r.nextBoolean() ? 2 : -1, c);
      case 3:
        return new XplusYeqC(a, c, r.nextInt(5) - 2);
      case 4:
        {
          int k = r.nextInt(3) - 1;
          return new XplusYeqZ(a, new IntVar(vars.store(), k, k), c);
        }
      case 5:
        return b.length > 1 ? new XeqY(b[0], b[1]) : new XeqY(a, c);
      default:
        return b.length > 0 ? new XeqY(a, b[0]) : new XplusCeqZ(c, 1, a);
    }
  }

  private static Constraint randomConstraint(Random r, Model.Vars vars) {
    IntVar[] x = vars.x();
    IntVar[] three = distinct(r, x, 3);
    BooleanVar[] b = vars.b();
    switch (r.nextInt(7)) {
      case 0:
        return new Alldifferent(distinct(r, x, 2 + r.nextInt(2)));
      case 1:
        {
          int[] w = new int[3];
          for (int i = 0; i < w.length; i++) {
            w[i] = r.nextInt(5) - 2;
          }
          return new LinearInt(three, w, r.nextBoolean() ? "<=" : "==", r.nextInt(5) - 2);
        }
      case 2:
        return new ElementInteger(
            three[0], new int[] {r.nextInt(3), r.nextInt(3), r.nextInt(3)}, three[1], -1);
      case 3:
        return new Max(new IntVar[] {three[0], three[1]}, three[2]);
      case 4:
        return b.length > 0
            ? new Reified(new XeqC(three[0], r.nextInt(3)), b[0])
            : new XneqY(three[0], three[1]);
      case 5:
        {
          int[][] tuples = new int[2 + r.nextInt(5)][];
          for (int t = 0; t < tuples.length; t++) {
            tuples[t] = new int[] {r.nextInt(5) - 2, r.nextInt(5) - 2};
          }
          return new Table(new IntVar[] {three[0], three[1]}, tuples);
        }
      default:
        return new XltY(three[0], three[1]);
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
