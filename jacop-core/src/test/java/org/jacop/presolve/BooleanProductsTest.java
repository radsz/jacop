/*
 * BooleanProductsTest.java
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
import java.util.function.Function;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
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

/** Presolve of products with a 0/1 factor. */
class BooleanProductsTest {

  private static final int TRIALS = Integer.getInteger("presolve.booleanProducts.trials", 1000);

  /** A model: integer variables, then 0/1 variables, and its constraints. */
  private record Model(Store store, IntVar[] x, List<Constraint> constraints) {}

  private static Model model(
      int[][] domains, int booleans, Function<IntVar[], List<Constraint>> f) {
    Store store = new Store();
    IntVar[] x = new IntVar[domains.length + booleans];
    for (int i = 0; i < domains.length; i++) {
      x[i] = new IntVar(store, "x" + i);
      for (int k = 0; k + 1 < domains[i].length; k += 2) {
        x[i].addDom(domains[i][k], domains[i][k + 1]);
      }
    }
    for (int i = 0; i < booleans; i++) {
      x[domains.length + i] = new BooleanVar(store, "b" + i);
    }
    List<Constraint> constraints = f.apply(x);
    constraints.forEach(store::impose);
    return new Model(store, x, constraints);
  }

  private static BooleanProducts rule(Derivation d) {
    return d.rules().stream()
        .filter(BooleanProducts.class::isInstance)
        .map(BooleanProducts.class::cast)
        .findFirst()
        .orElseThrow();
  }

  private static int replaced(Model m) {
    Derivation d = Presolver.of(m.store()).keep(m.x()).presolve();
    assertThat(d.outcome()).isNotEqualTo(Derivation.Outcome.INFEASIBLE);
    int replaced = rule(d).replaced();
    d.discard();
    return replaced;
  }

  @Test
  void productWithABooleanIsReplacedEitherWay() {
    int[][] domains = {{-2, 5}, {-10, 10}};
    assertThat(replaced(model(domains, 1, x -> list(new XmulYeqZ(x[0], x[2], x[1]))))).isOne();
    assertThat(replaced(model(domains, 1, x -> list(new XmulYeqZ(x[2], x[0], x[1]))))).isOne();
  }

  @Test
  void productsThatAreNotOfIndependentFactorsAreKept() {
    int[][] one = {{-2, 5}};
    // b * b = x, x * x = b, b * x = b, x * b = x, b1 * b2 = b3, and a factor fixed to 1
    assertThat(replaced(model(one, 1, x -> list(new XmulYeqZ(x[1], x[1], x[0]))))).isZero();
    assertThat(replaced(model(one, 1, x -> list(new XmulYeqZ(x[0], x[0], x[1]))))).isZero();
    assertThat(replaced(model(one, 1, x -> list(new XmulYeqZ(x[1], x[0], x[1]))))).isZero();
    assertThat(replaced(model(one, 1, x -> list(new XmulYeqZ(x[0], x[1], x[0]))))).isZero();
    assertThat(replaced(model(new int[0][], 3, x -> list(new XmulYeqZ(x[0], x[1], x[2])))))
        .isZero();
    int[][] two = {{-2, 5}, {-10, 10}, {1, 1}};
    assertThat(replaced(model(two, 0, x -> list(new XmulYeqZ(x[0], x[2], x[1]))))).isZero();
  }

  @Test
  void productOfAnOffsetVariableUsesItsBase() {
    // t = d + 1, z = t * b, as in maximum-dag: (distance + 1) * chosen
    int[][] domains = {{0, 6}, {1, 7}, {0, 7}};
    Function<IntVar[], List<Constraint>> f =
        x -> list(new XplusCeqZ(x[0], 1, x[1]), new XmulYeqZ(x[1], x[3], x[2]));
    assertThat(replaced(model(domains, 1, f))).isOne();
    assertThat(solve(model(domains, 1, f), true)).isEqualTo(solve(model(domains, 1, f), false));
  }

  @Test
  void constraintsWithoutALinearFormAreSkipped() {
    // a subclass of SumInt has no linear form: linearForm() returns null
    int[][] domains = {{-2, 5}, {-10, 10}, {-3, 3}};
    Function<IntVar[], List<Constraint>> f =
        x ->
            list(
                new SumInt(new IntVar[] {x[0], x[2]}, "==", x[1]) {},
                new XmulYeqZ(x[0], x[3], x[1]));
    assertThat(replaced(model(domains, 1, f))).isOne();
    assertThat(solve(model(domains, 1, f), true)).isEqualTo(solve(model(domains, 1, f), false));
  }

  @Test
  void booleanProductsCanBeSwitchedOff() {
    String property = "jacop.presolve.booleanProducts";
    System.setProperty(property, "false");
    try {
      Model m =
          model(new int[][] {{-2, 5}, {-10, 10}}, 1, x -> list(new XmulYeqZ(x[0], x[2], x[1])));
      assertThat(replaced(m)).isZero();
    } finally {
      System.clearProperty(property);
    }
  }

  @Test
  void ruleIsIdempotent() {
    Model m = model(new int[][] {{-2, 5}, {-10, 10}}, 1, x -> list(new XmulYeqZ(x[0], x[2], x[1])));
    Derivation d = Presolver.of(m.store()).keep(m.x()).rounds(5).presolve();
    assertThat(rule(d).replaced()).isOne();
    // the round after the replacement changes nothing, and so does the round of medium rules
    assertThat(d.rounds()).isLessThanOrEqualTo(3);
    d.discard();
  }

  @Test
  void randomProductModelsHaveTheSameSolutionsThroughPresolve() {
    Random random = new Random(20261028);
    int replaced = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = random.nextLong();
      Random r = new Random(seed);
      int[][] domains = new int[4][];
      for (int i = 0; i < domains.length; i++) {
        int min = r.nextInt(7) - 4;
        int max = min + 1 + r.nextInt(5);
        domains[i] =
            r.nextInt(3) == 0 && max - min >= 3
                ? new int[] {min, min + 1, max - 1, max}
                : new int[] {min, max};
      }
      int booleans = 2;
      Function<IntVar[], List<Constraint>> f = x -> randomConstraints(new Random(seed), x);

      Set<List<Integer>> expected = solve(model(domains, booleans, f), false);
      Model m = model(domains, booleans, f);
      boolean checking = trial % 2 == 0;
      Derivation d = Presolver.of(m.store()).keep(m.x()).checking(checking).presolve();
      Set<List<Integer>> found =
          d.outcome() == Derivation.Outcome.INFEASIBLE ? Set.of() : solve(m, d);
      assertThat(found).as("trial %d, seed %d", trial, seed).isEqualTo(expected);
      if (d.outcome() != Derivation.Outcome.INFEASIBLE) {
        replaced += rule(d).replaced();
      }
    }
    assertThat(replaced).isGreaterThan(TRIALS / 5);
  }

  /**
   * Products over four integer variables and two 0/1 variables, with offsets and side constraints.
   */
  private static List<Constraint> randomConstraints(Random r, IntVar[] all) {
    IntVar[] x = Arrays.copyOf(all, 4);
    IntVar[] b = Arrays.copyOfRange(all, 4, all.length);
    List<Constraint> result = new ArrayList<>();
    int n = 1 + r.nextInt(3);
    for (int k = 0; k < n; k++) {
      IntVar factor = r.nextInt(6) == 0 ? b[r.nextInt(b.length)] : x[r.nextInt(x.length)];
      IntVar bool = r.nextInt(8) == 0 ? x[r.nextInt(x.length)] : b[r.nextInt(b.length)];
      IntVar product = r.nextInt(8) == 0 ? all[r.nextInt(all.length)] : x[r.nextInt(x.length)];
      result.add(
          r.nextBoolean()
              ? new XmulYeqZ(factor, bool, product)
              : new XmulYeqZ(bool, factor, product));
    }
    int side = r.nextInt(3);
    for (int k = 0; k < side; k++) {
      IntVar u = x[r.nextInt(x.length)];
      IntVar v = x[r.nextInt(x.length)];
      if (u == v) {
        continue;
      }
      result.add(
          switch (r.nextInt(3)) {
            case 0 -> new XplusCeqZ(u, r.nextInt(5) - 2, v);
            case 1 -> new LinearInt(new IntVar[] {u, v}, new int[] {-1, 1}, "==", r.nextInt(3));
            default -> new XneqY(u, v);
          });
    }
    return result;
  }

  private static Set<List<Integer>> solve(Model m, boolean presolve) {
    if (!presolve) {
      return solve(m, null);
    }
    Derivation d = Presolver.of(m.store()).keep(m.x()).checking(true).presolve();
    return d.outcome() == Derivation.Outcome.INFEASIBLE ? Set.of() : solve(m, d);
  }

  private static Set<List<Integer>> solve(Model m, Derivation d) {
    Set<List<Integer>> found = new HashSet<>();
    Store store = d == null ? m.store() : d.child();
    IntVar[] decisions = d == null ? m.x() : d.counterparts(m.x());
    Runnable onSolution =
        () -> {
          if (d == null || d.returnSolution()) {
            found.add(Arrays.stream(m.x()).map(IntVar::value).toList());
          }
        };
    if (!store.consistency()) {
      // no solution
    } else if (Arrays.stream(decisions).allMatch(IntVar::singleton)) {
      onSolution.run();
    } else {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.setSolutionListener(
          new SimpleSolutionListener<>() {
            @Override
            public boolean executeAfterSolution(
                Search<IntVar> s, SelectChoicePoint<IntVar> select) {
              boolean result = super.executeAfterSolution(s, select);
              onSolution.run();
              return result;
            }
          });
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      search.labeling(store, new SimpleSelect<>(decisions, null, new IndomainMin<>()));
    }
    if (d != null) {
      d.discard();
    }
    return found;
  }

  private static List<Constraint> list(Constraint... c) {
    return new ArrayList<>(List.of(c));
  }
}
