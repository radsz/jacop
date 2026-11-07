/*
 * ReificationCleanupTest.java
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
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Not;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XplusYgtC;
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

/** Presolve rule 6: reifications with a fixed Boolean, half-reification, unused Booleans. */
class ReificationCleanupTest {

  private static final int TRIALS = Integer.getInteger("presolve.reification.trials", 600);

  @Test
  void aReificationWhoseBooleanIsWantedTrueBecomesAnImplication() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 0, 5);
    BooleanVar b = new BooleanVar(store, "b");
    BooleanVar d = new BooleanVar(store, "d");
    store.impose(new Reified(new XltY(x, y), b));
    store.impose(new BoolClause(new IntVar[] {b, d}, new IntVar[0]));

    Derivation derivation = Presolver.of(store).keep(x, y, d).solutionPreserving(false).presolve();

    assertThat(derivation.reductions()).containsEntry("halfReified", 1);
    assertThat(childConstraints(derivation)).hasAtLeastOneElementOfType(Implies.class);
    assertThat(childConstraints(derivation)).noneMatch(c -> c instanceof Reified);
  }

  @Test
  void aReificationWhoseBooleanIsWantedFalseBecomesTheConverse() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 0, 5);
    BooleanVar b = new BooleanVar(store, "b");
    store.impose(new Reified(new XltY(x, y), b));
    store.impose(new Implies(b, new XlteqC(x, 2)));

    Derivation derivation = Presolver.of(store).keep(x, y).solutionPreserving(false).presolve();

    assertThat(derivation.reductions()).containsEntry("halfReified", 1);
    assertThat(childConstraints(derivation)).hasAtLeastOneElementOfType(IfThen.class);
  }

  @Test
  void aReificationOrImplicationWhoseBooleanIsUsedNowhereElseIsDropped() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 0, 5);
    BooleanVar b = new BooleanVar(store, "b");
    BooleanVar d = new BooleanVar(store, "d");
    store.impose(new Reified(new XltY(x, y), b));
    store.impose(new Implies(d, new XltY(y, x)));

    Derivation derivation = Presolver.of(store).keep(x, y).solutionPreserving(false).presolve();

    assertThat(derivation.reductions()).containsEntry("reificationsDropped", 2);
    assertThat(derivation.statistics().childConstraints()).isZero();
    assertThat(derivation.entry(b)).isInstanceOf(Entry.Free.class);
  }

  @Test
  void aReificationWithAFixedBooleanBecomesItsConstraintOrItsNegation() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 0, 5);
    IntVar z = new IntVar(store, "z", 0, 5);
    BooleanVar b = new BooleanVar(store, "b");
    BooleanVar d = new BooleanVar(store, "d");
    store.impose(new Reified(new XltY(x, y), b));
    store.impose(new Reified(new XltY(y, z), d));
    store.impose(new XeqC(b, 1));
    store.impose(new XeqC(d, 0));

    // this part keeps every solution, so it runs without frozen variables too
    Derivation derivation = Presolver.of(store).presolve();

    assertThat(derivation.reductions()).containsEntry("reificationsSimplified", 2);
    List<Constraint> child = childConstraints(derivation);
    assertThat(child).hasAtLeastOneElementOfType(XltY.class);
    assertThat(child).hasAtLeastOneElementOfType(Not.class);
    assertThat(derivation.entry(b)).isInstanceOf(Entry.Fixed.class);
  }

  @Test
  void frozenBooleansAndSolutionPreservingDerivationsAreNotRelaxed() {
    for (boolean frozenB : new boolean[] {true, false}) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", 0, 5);
      IntVar y = new IntVar(store, "y", 0, 5);
      BooleanVar b = new BooleanVar(store, "b");
      BooleanVar d = new BooleanVar(store, "d");
      store.impose(new Reified(new XltY(x, y), b));
      store.impose(new BoolClause(new IntVar[] {b, d}, new IntVar[0]));
      Presolver presolver = Presolver.of(store).keep(x, y, d);
      if (frozenB) {
        presolver.keep(b).solutionPreserving(false);
      }
      Derivation derivation = presolver.presolve();
      assertThat(derivation.reductions()).containsEntry("halfReified", 0);
      assertThat(childConstraints(derivation)).hasAtLeastOneElementOfType(Reified.class);
    }
  }

  @Test
  void randomModelsKeepTheirSolutionsOnTheFrozenVariables() {
    Random random = new Random(20261027);
    int relaxed = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = random.nextLong();
      int frozenMask = random.nextInt(1 << BOOLEANS);
      Set<List<Integer>> expected = new HashSet<>();
      Instance direct = new Instance(seed, frozenMask);
      search(direct.store, direct.all(), () -> expected.add(direct.frozenValues()));

      Instance presolved = new Instance(seed, frozenMask);
      boolean checking = trial % 2 == 0;
      Derivation derivation =
          Presolver.of(presolved.store)
              .keep(presolved.frozen())
              .solutionPreserving(false)
              .checking(checking)
              .presolve();
      Set<List<Integer>> found = new HashSet<>();
      if (derivation.outcome() != Derivation.Outcome.INFEASIBLE) {
        relaxed += derivation.reductions().getOrDefault("halfReified", 0);
        relaxed += derivation.reductions().getOrDefault("reificationsDropped", 0);
        // the relaxed Booleans are left out of the search, as the FlatZinc front end does
        IntVar[] searched =
            Arrays.stream(presolved.all())
                .filter(v -> !derivation.relaxed().contains(v))
                .toArray(IntVar[]::new);
        search(
            derivation.child(),
            derivation.counterparts(searched),
            () -> {
              assertThat(derivation.returnSolution()).isTrue();
              found.add(presolved.frozenValues());
            });
      }
      assertThat(found).as("trial %d, checking %b", trial, checking).isEqualTo(expected);
    }
    assertThat(relaxed).isGreaterThan(TRIALS / 5);
  }

  private static final int INTEGERS = 3;
  private static final int BOOLEANS = 5;

  /** A random model of reifications, implications and monotone Boolean constraints. */
  private static final class Instance {
    final Store store = new Store();
    final IntVar[] x = new IntVar[INTEGERS];
    final IntVar[] b = new IntVar[BOOLEANS];
    final int frozenMask;

    Instance(long seed, int frozenMask) {
      this.frozenMask = frozenMask;
      Random r = new Random(seed);
      for (int i = 0; i < INTEGERS; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 3);
      }
      for (int i = 0; i < BOOLEANS; i++) {
        b[i] = r.nextBoolean() ? new BooleanVar(store, "b" + i) : new IntVar(store, "b" + i, 0, 1);
      }
      int n = 2 + r.nextInt(6);
      for (int k = 0; k < n; k++) {
        store.impose(constraint(r));
      }
    }

    private Constraint constraint(Random r) {
      IntVar bi = b[r.nextInt(BOOLEANS)];
      return switch (r.nextInt(9)) {
        case 0, 1, 2 -> new Reified(primitive(r), bi);
        case 3 -> new Implies(bi, primitive(r));
        case 4 -> new BoolClause(booleans(r), booleans(r));
        case 5 -> new SumBool(booleans(r), r.nextBoolean() ? ">=" : "<=", constant(r, 2));
        case 6 -> new XlteqY(bi, b[r.nextInt(BOOLEANS)]);
        case 7 ->
            r.nextBoolean()
                ? new OrBoolVector(booleans(r), constant(r, 1))
                : new AndBoolVector(booleans(r), constant(r, 1));
        default -> {
          IntVar[] vs = {bi, b[r.nextInt(BOOLEANS)], x[r.nextInt(INTEGERS)]};
          int[] a = {r.nextInt(5) - 2, r.nextInt(5) - 2, r.nextInt(3) - 1};
          yield new LinearInt(vs, a, r.nextBoolean() ? "<=" : ">", r.nextInt(5) - 2);
        }
      };
    }

    private PrimitiveConstraint primitive(Random r) {
      IntVar u = x[r.nextInt(INTEGERS)];
      IntVar v = r.nextInt(4) == 0 ? b[r.nextInt(BOOLEANS)] : x[r.nextInt(INTEGERS)];
      return switch (r.nextInt(4)) {
        case 0 -> new XltY(u, v);
        case 1 -> new XlteqC(u, r.nextInt(4));
        case 2 -> new XplusYgtC(u, v, r.nextInt(5));
        default -> new Reified(new XltY(v, u), b[r.nextInt(BOOLEANS)]);
      };
    }

    private IntVar[] booleans(Random r) {
      List<IntVar> list = new ArrayList<>();
      for (IntVar v : b) {
        if (r.nextInt(3) == 0) {
          list.add(v);
        }
      }
      return list.toArray(new IntVar[0]);
    }

    private IntVar constant(Random r, int max) {
      int c = r.nextInt(max + 1);
      return new IntVar(store, c, c);
    }

    IntVar[] all() {
      IntVar[] all = Arrays.copyOf(x, INTEGERS + BOOLEANS);
      System.arraycopy(b, 0, all, INTEGERS, BOOLEANS);
      return all;
    }

    Var[] frozen() {
      List<Var> frozen = new ArrayList<>(Arrays.asList(x));
      for (int i = 0; i < BOOLEANS; i++) {
        if ((frozenMask >> i & 1) != 0) {
          frozen.add(b[i]);
        }
      }
      return frozen.toArray(new Var[0]);
    }

    List<Integer> frozenValues() {
      List<Integer> values = new ArrayList<>();
      for (Var v : frozen()) {
        values.add(((IntVar) v).value());
      }
      return values;
    }
  }

  private static List<Constraint> childConstraints(Derivation derivation) {
    Store child = derivation.child();
    Set<Constraint> seen = new HashSet<>();
    List<Constraint> result = new ArrayList<>();
    for (int i = 0; i < child.size(); i++) {
      for (Constraint c : child.vars[i].dom().constraints()) {
        if (seen.add(c)) {
          result.add(c);
        }
      }
    }
    return result;
  }

  private static void search(Store store, IntVar[] vars, Runnable onSolution) {
    if (!store.consistency()) {
      return;
    }
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
