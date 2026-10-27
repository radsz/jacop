/*
 * TablingTest.java
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
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.BooleanVar;
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
 * Automatic tabulation in presolve: the derived store has the same solutions, with the same
 * multiplicity, as the original one.
 */
class TablingTest {

  private static final int TRIALS = Integer.getInteger("tabling.trials", 400);

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  /** The default limits, but every group within them is tabulated. */
  private static final Tabling.Limits ALWAYS =
      new Tabling.Limits(10, 3, 10_000, 100_000, 2_000_000, false);

  @Test
  void randomModelsHaveTheSameSolutionsThroughTabling() {
    Random random = new Random(20261027);
    int tabled = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = random.nextLong();
      List<List<Integer>> expected = solveDirectly(s -> randomModel(s, new Random(seed)));
      boolean checking = trial % 2 == 0;
      Tabling.Limits limits = trial % 4 < 2 ? ALWAYS : Tabling.Limits.DEFAULT;
      Run run = solveThroughTabling(s -> randomModel(s, new Random(seed)), checking, limits);
      assertThat(run.solutions())
          .as("trial %d, checking %b", trial, checking)
          .containsExactlyInAnyOrderElementsOf(expected);
      if (run.statistics().tables() > 0) {
        tabled++;
      }
    }
    assertThat(tabled).isGreaterThan(TRIALS / 10);
  }

  @Test
  void anIntermediateVariableJoinsItsDefinitionAndItsUse() {
    // t = x * y, t + x = 8: bounds reasoning does not see that only (2, 3) and (4, 1) remain
    Function<Store, IntVar[]> model =
        s -> {
          IntVar x = new IntVar(s, "x", 0, 5);
          IntVar y = new IntVar(s, "y", 0, 5);
          IntVar t = new IntVar(s, "t", 0, 25);
          s.impose(new XmulYeqZ(x, y, t));
          s.impose(new XplusYeqZ(t, x, new IntVar(s, "z", 8, 8)));
          return new IntVar[] {x, y, t};
        };
    Run run = solveThroughTabling(model, true, Tabling.Limits.DEFAULT);
    assertThat(run.statistics().tables()).isEqualTo(1);
    assertThat(run.statistics().replaced()).isEqualTo(2);
    assertThat(run.solutions()).containsExactlyInAnyOrderElementsOf(solveDirectly(model));
  }

  @Test
  void aGroupThatPropagatesToItsSolutionsIsKept() {
    // x != y, y != z: a tree of arc-consistent constraints is domain consistent as a whole
    Store s = new Store();
    IntVar x = new IntVar(s, "x", 0, 2);
    IntVar y = new IntVar(s, "y", 0, 2);
    IntVar z = new IntVar(s, "z", 0, 2);
    s.impose(new XneqY(x, y));
    s.impose(new XneqY(y, z));
    Derivation d = Derivation.of(s).tabling(true).derive();
    assertThat(d.tablingStatistics().tables()).isZero();
    assertThat(d.statistics().childConstraints()).isEqualTo(2);
  }

  @Test
  void aGroupThatMissesHolesIsReplaced() {
    // t = x - y, |t| = 2: the linear constraint reasons on bounds, so removing x = 3 leaves y = 1
    // without a solution; assigning values alone never shows it
    Store s = new Store();
    IntVar x = new IntVar(s, "x", 0, 5);
    IntVar y = new IntVar(s, "y", 0, 5);
    IntVar t = new IntVar(s, "t", -5, 5);
    s.impose(new XplusYeqZ(t, y, x));
    s.impose(new AbsXeqY(t, new IntVar(s, "z", 2, 2)));
    Derivation d = Derivation.of(s).tabling(true).derive();
    assertThat(d.tablingStatistics().tables()).isEqualTo(1);
  }

  @Test
  void aGroupWithoutSolutionMakesThePresolveInfeasible() {
    Store s = new Store();
    IntVar x = new IntVar(s, "x", 0, 5);
    IntVar y = new IntVar(s, "y", 0, 5);
    IntVar z = new IntVar(s, "z", 0, 10);
    s.impose(new XplusYeqZ(x, y, z));
    s.impose(new LinearInt(new IntVar[] {x, y, z}, new int[] {2, 2, -2}, "==", 1));
    Derivation d = Derivation.of(s).tabling(true).derive();
    assertThat(d.outcome()).isEqualTo(Derivation.Outcome.INFEASIBLE);
  }

  @Test
  void aGroupOverTheLimitsIsKept() {
    Derivation d = Derivation.of(sumOfDistinct()).tabling(ALWAYS).derive();
    assertThat(d.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    assertThat(d.tablingStatistics().tables()).isZero();
    assertThat(d.statistics().childConstraints()).isEqualTo(2);

    Derivation larger =
        Derivation.of(sumOfDistinct())
            .tabling(new Tabling.Limits(10, 3, 100_000, 1_000_000, 1_000_000, false))
            .derive();
    assertThat(larger.tablingStatistics().tables()).isEqualTo(1);
    assertThat(larger.tablingStatistics().tuples()).isEqualTo(201 * 200);
    assertThat(larger.statistics().childConstraints()).isEqualTo(1);
  }

  /** x + y = z and x != y over 0..200: 40,200 solutions. */
  private static Store sumOfDistinct() {
    Store s = new Store();
    IntVar x = new IntVar(s, "x", 0, 200);
    IntVar y = new IntVar(s, "y", 0, 200);
    IntVar z = new IntVar(s, "z", 0, 400);
    s.impose(new XplusYeqZ(x, y, z));
    s.impose(new XneqY(x, y));
    return s;
  }

  @Test
  void aGroupOverTooManyVariablesIsNotFormed() {
    Store s = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(s, "x" + i, 0, 2);
    }
    s.impose(new LinearInt(x, new int[] {1, 1, 1, 1}, "==", 4));
    s.impose(new XneqY(x[0], x[1]));
    Derivation d =
        Derivation.of(s).tabling(new Tabling.Limits(3, 3, 100, 1000, 1000, false)).derive();
    assertThat(d.tablingStatistics().tables()).isZero();
  }

  private record Run(List<List<Integer>> solutions, Derivation.TablingStatistics statistics) {}

  private static IntVar[] randomModel(Store s, Random r) {
    int n = 3 + r.nextInt(4);
    IntVar[] x = new IntVar[n + 1];
    for (int i = 0; i < n; i++) {
      int lo = r.nextInt(5) - 2;
      x[i] = new IntVar(s, "x" + i, lo, lo + 1 + r.nextInt(4));
    }
    x[n] = new BooleanVar(s, "b");
    int constraints = 2 + r.nextInt(4);
    for (int k = 0; k < constraints; k++) {
      s.impose(randomConstraint(r, Arrays.copyOf(x, n), (BooleanVar) x[n]));
    }
    return x;
  }

  private static Constraint randomConstraint(Random r, IntVar[] x, BooleanVar b) {
    List<IntVar> pool = new ArrayList<>(Arrays.asList(x));
    IntVar a = pool.remove(r.nextInt(pool.size()));
    IntVar c = pool.remove(r.nextInt(pool.size()));
    IntVar d = pool.remove(r.nextInt(pool.size()));
    return switch (r.nextInt(10)) {
      case 0 -> new XplusYeqZ(a, c, d);
      case 1 -> new XmulYeqZ(a, c, d);
      case 2 -> new AbsXeqY(a, c);
      case 3 ->
          new LinearInt(
              new IntVar[] {a, c, d},
              new int[] {1 + r.nextInt(2), -1 - r.nextInt(2), r.nextInt(3) - 1},
              RELATIONS[r.nextInt(RELATIONS.length)],
              r.nextInt(3) - 1);
      case 4 -> new XneqY(a, c);
      case 5 -> new XltY(a, c);
      case 6 -> new Reified(new XeqC(a, r.nextInt(3)), b);
      case 7 -> new ElementInteger(a, new int[] {r.nextInt(3), r.nextInt(3), r.nextInt(3)}, c, -1);
      case 8 -> new Count(new IntVar[] {a, c, d}, b, r.nextInt(2));
      default -> c.min() > 0 ? new XmodYeqZ(a, c, d) : new XmulYeqZ(a, c, d);
    };
  }

  private static List<List<Integer>> solveDirectly(Function<Store, IntVar[]> model) {
    Store s = new Store();
    IntVar[] vars = model.apply(s);
    List<List<Integer>> found = new ArrayList<>();
    if (s.consistency()) {
      search(s, vars, () -> found.add(values(vars)));
    }
    return found;
  }

  private static Run solveThroughTabling(
      Function<Store, IntVar[]> model, boolean checking, Tabling.Limits limits) {
    Store s = new Store();
    IntVar[] vars = model.apply(s);
    List<List<Integer>> found = new ArrayList<>();
    Derivation d =
        Derivation.of(s)
            .keep(vars)
            .tabling(limits)
            .retention(checking ? Derivation.Retention.KEPT : Derivation.Retention.RELEASED)
            .derive();
    if (d.outcome() == Derivation.Outcome.INFEASIBLE) {
      return new Run(found, d.tablingStatistics());
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
    return new Run(found, d.tablingStatistics());
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
