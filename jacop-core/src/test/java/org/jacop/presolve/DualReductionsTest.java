/*
 * DualReductionsTest.java
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
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Dual reductions on random small models: every solution found through the derived store is a
 * solution of the original model, there is one when the model has one, and the optimum stays.
 */
class DualReductionsTest {

  private static final int TRIALS = Integer.getInteger("presolve.dual.trials", 3000);

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  /** No objective, minimise the last variable, maximise it, or minimise a linear definition. */
  private enum Goal {
    SATISFY,
    MINIMIZE,
    MAXIMIZE,
    MINIMIZE_DEFINED
  }

  /** A random model: variables in small ranges, the first {@code booleans} of them 0/1. */
  private record Model(int[][] domains, int booleans, Goal goal, long seed, int constraints) {

    IntVar[] build(Store store) {
      IntVar[] x = new IntVar[domains.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, domains[i][0], domains[i][1]);
      }
      Random r = new Random(seed);
      for (int k = 0; k < constraints; k++) {
        store.impose(randomConstraint(r, x, booleans));
      }
      if (goal == Goal.MINIMIZE_DEFINED) {
        // the last variable is the objective, defined by a linear equality over the others
        IntVar[] terms = Arrays.copyOf(x, x.length);
        int[] w = new int[x.length];
        for (int i = 0; i < x.length - 1; i++) {
          w[i] = r.nextInt(5) - 2;
        }
        w[x.length - 1] = r.nextBoolean() ? 1 : -1;
        store.impose(new LinearInt(terms, w, "==", r.nextInt(3)));
      }
      return x;
    }
  }

  @Test
  void randomModelsKeepASolutionAndTheOptimum() {
    Random random = new Random(20261027);
    int reduced = 0;
    int dominated = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Model model = randomModel(random);
      Set<List<Integer>> expected = solveDirectly(model);
      boolean checking = trial % 2 == 0;
      List<List<Integer>> found = new ArrayList<>();
      Derivation.DualStatistics statistics =
          solveThroughPresolve(model, checking, random.nextInt(), found);
      String context = "trial " + trial + ", " + model.goal() + ", checking " + checking;
      assertThat(expected).as(context).containsAll(found);
      assertThat(found.isEmpty()).as(context).isEqualTo(expected.isEmpty());
      if (model.goal() != Goal.SATISFY && !expected.isEmpty()) {
        assertThat(best(model, found)).as(context).isEqualTo(best(model, expected));
      }
      if (statistics != null && statistics.fixed() + statistics.tightened() > 0) {
        reduced++;
      }
      if (statistics != null && statistics.dominanceClauses() > 0) {
        dominated++;
      }
    }
    assertThat(reduced).isGreaterThan(TRIALS / 4);
    assertThat(dominated).isGreaterThan(TRIALS / 50);
  }

  @Test
  void aDominatedColumnGetsAnImplication() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    IntVar z = new IntVar(store, "z", 0, 3);
    IntVar cost = new IntVar(store, "cost", 0, 100);
    // x covers whatever y covers and costs less, so some optimum has y <= x
    store.impose(new LinearInt(new IntVar[] {x, y, z}, new int[] {1, 1, 1}, ">=", 2));
    store.impose(new LinearInt(new IntVar[] {x, y}, new int[] {2, 1}, ">=", 1));
    store.impose(new LinearInt(new IntVar[] {x, y, z, cost}, new int[] {3, 5, 4, -1}, "==", 0));

    Derivation derivation =
        Presolver.of(store).keep(x, y, z, cost).dualReductions(cost, true).presolve();

    assertThat(derivation.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    assertThat(derivation.dualStatistics().dominanceClauses()).isPositive();
    Store child = derivation.child();
    IntVar[] c = derivation.counterparts(new IntVar[] {x, y});
    child.impose(new XgteqC(c[1], 1));
    assertThat(child.consistency()).isTrue();
    assertThat(c[0].value()).isEqualTo(1);
  }

  @Test
  void equalColumnsGetOneImplicationOnly() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    // x and y dominate each other; both clauses would leave only x = y
    store.impose(new LinearInt(new IntVar[] {x, y}, new int[] {1, 1}, "==", 1));

    Derivation derivation = Presolver.of(store).dualReductions(null, true).presolve();

    assertThat(derivation.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    assertThat(derivation.dualStatistics().dominated()).isEqualTo(2);
    assertThat(derivation.dualStatistics().dominanceClauses()).isEqualTo(1);
  }

  @Test
  void variablesAreFixedOrBoundedWhereTheConstraintsLetThem() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 9);
    IntVar y = new IntVar(store, "y", 0, 2);
    IntVar z = new IntVar(store, "z", 0, 9);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    // x + y >= 5 holds once x >= 5 whatever y is; x <= z lets x decrease and z increase; b and c
    // occur only positively in a clause
    store.impose(new LinearInt(new IntVar[] {x, y}, new int[] {1, 1}, ">=", 5));
    store.impose(new XlteqY(x, z));
    store.impose(new BoolClause(new IntVar[] {b, c}, new IntVar[0]));

    Derivation derivation =
        Presolver.of(store).dualReductions(null, true).keep(x, y, z, b, c).presolve();

    assertThat(derivation.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    assertThat(y.value()).isEqualTo(2);
    assertThat(z.value()).isEqualTo(9);
    // x loses the values above 5, where x + y >= 5 holds whatever y is; once y is 2 and z is 9
    // both constraints hold, so x is left free in 3..5
    assertThat(x.min()).isEqualTo(3);
    assertThat(x.max()).isEqualTo(5);
    assertThat(b.value()).isEqualTo(1);
    assertThat(c.value()).isEqualTo(1);
    assertThat(derivation.dualStatistics().fixed()).isEqualTo(4);
    assertThat(derivation.dualStatistics().tightened()).isEqualTo(1);
  }

  @Test
  void theObjectiveDefinitionLetsItsTermsImprove() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 0, 5);
    IntVar obj = new IntVar(store, "obj", 0, 100);
    IntVar[] terms = {x, y, obj};
    store.impose(new LinearInt(terms, new int[] {2, 3, -1}, "==", 0));
    store.impose(new XneqY(x, y));

    Presolver.of(store).dualReductions(obj, true).presolve();

    // the terms want to be small, but x != y locks them
    assertThat(x.max()).isEqualTo(5);

    Store other = new Store();
    IntVar u = new IntVar(other, "u", 0, 5);
    IntVar v = new IntVar(other, "v", 0, 5);
    IntVar cost = new IntVar(other, "cost", 0, 100);
    other.impose(new LinearInt(new IntVar[] {u, v, cost}, new int[] {2, -3, -1}, "==", -15));
    other.impose(new LinearInt(new IntVar[] {u, v}, new int[] {1, 1}, ">=", 3));

    Presolver.of(other).dualReductions(cost, true).presolve();

    // cost = 2u - 3v + 15: v wants to be large and is fixed, then u is bounded by u + v >= 3
    assertThat(v.value()).isEqualTo(5);
    assertThat(u.value()).isEqualTo(0);
  }

  @Test
  void anObjectiveWhoseDomainCutsTheDefinitionIsNotRelaxed() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 0, 5);
    // obj = x + y but obj >= 3: the sum cannot be followed below 3
    IntVar obj = new IntVar(store, "obj", 3, 10);
    store.impose(new LinearInt(new IntVar[] {x, y, obj}, new int[] {1, 1, -1}, "==", 0));

    Derivation derivation = Presolver.of(store).dualReductions(obj, true).presolve();

    assertThat(derivation.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    assertThat(derivation.dualStatistics().fixed()).isZero();
    assertThat(x.min()).isZero();
    assertThat(x.max()).isEqualTo(5);
  }

  @Test
  void exemptVariablesAreLeftAlone() {
    Store store = new Store();
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    store.impose(new BoolClause(new IntVar[] {b, c}, new IntVar[0]));

    Presolver.of(store).dualReductions(null, true).exempt(c).presolve();

    assertThat(b.value()).isEqualTo(1);
    assertThat(c.singleton()).isFalse();
  }

  @Test
  void aReifiedConditionLetsItsVariablesMoveWhenTheReificationCanFollow() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 9);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    // b <-> x <= 4, and b only positively in a clause: x moving down only makes b truer
    store.impose(new Reified(new XlteqC(x, 4), b));
    store.impose(new BoolClause(new IntVar[] {b, c}, new IntVar[0]));
    store.impose(new XgteqC(x, 2));

    Presolver.of(store).dualReductions(null, true).presolve();

    assertThat(x.value()).isEqualTo(2);
    assertThat(c.value()).isEqualTo(1);
  }

  @Test
  void aVariableMovesOnlyWhereItsReificationCanFollow() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 9);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    // b <-> x <= 4 and b + c <= 1, maximising c: b can follow x down but not up, so x is fixed
    // to its maximum, which keeps the optimum c = 1
    store.impose(new Reified(new XlteqC(x, 4), b));
    store.impose(new LinearInt(new IntVar[] {b, c}, new int[] {1, 1}, "<=", 1));

    Presolver.of(store).dualReductions(c, false).presolve();

    assertThat(x.value()).isEqualTo(9);
    assertThat(b.value()).isZero();
    assertThat(c.value()).isEqualTo(1);
  }

  private static Integer best(Model model, Iterable<List<Integer>> solutions) {
    Integer best = null;
    for (List<Integer> s : solutions) {
      int v = s.getLast();
      if (best == null || (model.goal() == Goal.MAXIMIZE ? v > best : v < best)) {
        best = v;
      }
    }
    return best;
  }

  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(4);
    int booleans = random.nextInt(n);
    Goal goal = Goal.values()[random.nextInt(Goal.values().length)];
    int size = goal == Goal.MINIMIZE_DEFINED ? n + 1 : n;
    int[][] domains = new int[size][];
    for (int i = 0; i < n; i++) {
      if (i < booleans) {
        domains[i] = new int[] {0, 1};
      } else {
        int min = random.nextInt(3) - 1;
        domains[i] = new int[] {min, min + random.nextInt(4)};
      }
    }
    if (goal == Goal.MINIMIZE_DEFINED) {
      // wide enough to follow the definition, or cut on one side
      domains[n] = random.nextInt(3) == 0 ? new int[] {-2, 30} : new int[] {-40, 40};
    }
    return new Model(domains, booleans, goal, random.nextLong(), 1 + random.nextInt(6));
  }

  private static Constraint randomConstraint(Random r, IntVar[] all, int booleans) {
    int n = all.length;
    IntVar a = all[r.nextInt(n)];
    IntVar c = all[r.nextInt(n)];
    while (c == a) {
      c = all[r.nextInt(n)];
    }
    IntVar[] bools = new IntVar[booleans];
    System.arraycopy(all, 0, bools, 0, booleans);
    IntVar b = booleans > 0 ? bools[r.nextInt(booleans)] : null;
    switch (r.nextInt(12)) {
      case 0, 1 -> {
        int[] w = new int[n];
        for (int i = 0; i < n; i++) {
          w[i] = r.nextInt(5) - 2;
        }
        return new LinearInt(all, w, RELATIONS[r.nextInt(RELATIONS.length)], r.nextInt(5) - 2);
      }
      case 2 -> {
        return new XplusClteqZ(a, r.nextInt(3) - 1, c);
      }
      case 3 -> {
        return r.nextBoolean() ? new XlteqY(a, c) : new XltY(a, c);
      }
      case 4 -> {
        if (booleans >= 2) {
          IntVar[] pos = r.nextBoolean() ? new IntVar[] {bools[0]} : new IntVar[0];
          IntVar[] neg = r.nextBoolean() ? new IntVar[] {bools[1]} : new IntVar[] {};
          if (pos.length + neg.length > 0) {
            return new BoolClause(pos, neg);
          }
        }
        return new XlteqY(a, c);
      }
      case 5 -> {
        if (booleans >= 2) {
          IntVar[] list = {bools[0], bools[1]};
          IntVar res = r.nextBoolean() ? bools[r.nextInt(booleans)] : bools[0];
          if (res == bools[0] || res == bools[1]) {
            return new XneqY(a, c);
          }
          return r.nextBoolean() ? new OrBoolVector(list, res) : new AndBoolVector(list, res);
        }
        return new XneqY(a, c);
      }
      case 6 -> {
        if (booleans >= 3) {
          return r.nextBoolean()
              ? new OrBoolSimple(bools[0], bools[1], bools[2])
              : new AndBoolSimple(bools[0], bools[1], bools[2]);
        }
        return new XplusClteqZ(c, 0, a);
      }
      case 7 -> {
        if (b != null && a != b) {
          return new Reified(
              r.nextBoolean() ? new XlteqC(a, r.nextInt(3)) : new XgteqC(a, r.nextInt(3)), b);
        }
        return new XlteqY(c, a);
      }
      case 8 -> {
        if (b != null && a != b) {
          return new Implies(
              b, r.nextBoolean() ? new XlteqC(a, r.nextInt(3)) : new XgteqC(a, r.nextInt(3)));
        }
        return new XltY(c, a);
      }
      case 9 -> {
        IntVar[] list = {a, c};
        IntVar sum = all[r.nextInt(n)];
        if (sum == a || sum == c) {
          return new XneqY(a, c);
        }
        return new SumInt(list, r.nextBoolean() ? "<=" : ">=", sum);
      }
      case 10 -> {
        return new XneqY(a, c);
      }
      default -> {
        return new Alldifferent(new IntVar[] {a, c});
      }
    }
  }

  private static Set<List<Integer>> solveDirectly(Model model) {
    Store store = new Store();
    IntVar[] x = model.build(store);
    Set<List<Integer>> found = new HashSet<>();
    if (store.consistency()) {
      search(store, x, 0, () -> found.add(values(x)));
    }
    return found;
  }

  private static Derivation.DualStatistics solveThroughPresolve(
      Model model, boolean checking, int seed, List<List<Integer>> found) {
    Store store = new Store();
    IntVar[] x = model.build(store);
    IntVar objective = model.goal() == Goal.SATISFY ? null : x[x.length - 1];
    Derivation derivation =
        Presolver.of(store)
            .keep(x)
            .checking(checking)
            .dualReductions(objective, model.goal() != Goal.MAXIMIZE)
            .presolve();
    if (derivation.outcome() == Derivation.Outcome.INFEASIBLE) {
      return derivation.dualStatistics();
    }
    search(
        derivation.child(),
        derivation.counterparts(x),
        seed,
        () -> {
          if (derivation.returnSolution()) {
            found.add(values(x));
          }
        });
    derivation.discard();
    return derivation.dualStatistics();
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
