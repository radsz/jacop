/*
 * RedundantConstraintsTest.java
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
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/** Rules 3 and 4 of presolve: canonical linear relations, duplicate and dominated constraints. */
class RedundantConstraintsTest {

  private static final int TRIALS = Integer.getInteger("presolve.redundant.trials", 600);

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  /** A model: variables in a store and its constraints, built twice for the two runs. */
  private record Model(Store store, List<IntVar> vars, List<Constraint> constraints) {
    IntVar[] x() {
      return vars.toArray(new IntVar[0]);
    }
  }

  private static Model model(
      int[][] domains, int booleans, Function<IntVar[], List<Constraint>> f) {
    Store store = new Store();
    IntVar[] x = new IntVar[domains.length + booleans];
    for (int i = 0; i < domains.length; i++) {
      x[i] = new IntVar(store, "x" + i, domains[i][0], domains[i][1]);
    }
    for (int i = 0; i < booleans; i++) {
      x[domains.length + i] = new BooleanVar(store, "b" + i);
    }
    List<Constraint> constraints = f.apply(x);
    for (Constraint c : constraints) {
      store.impose(c);
    }
    return new Model(store, List.of(x), constraints);
  }

  private static RedundantConstraints.Result find(Model m) {
    assertThat(m.store().consistency()).isTrue();
    return RedundantConstraints.find(m.constraints());
  }

  private static int[][] box(int n, int min, int max) {
    int[][] d = new int[n][];
    Arrays.setAll(d, i -> new int[] {min, max});
    return d;
  }

  @Test
  void exactDuplicatesAreRemovedOnce() {
    Model m =
        model(
            box(3, 0, 9),
            0,
            x ->
                List.of(
                    new LinearInt(x, new int[] {1, 2, 3}, "<=", 20),
                    new LinearInt(x, new int[] {1, 2, 3}, "<=", 20),
                    new LinearInt(new IntVar[] {x[2], x[0], x[1]}, new int[] {3, 1, 2}, "<=", 20)));
    RedundantConstraints.Result r = find(m);
    assertThat(r.duplicates()).containsExactly(m.constraints().get(1), m.constraints().get(2));
    assertThat(r.dominated()).isEmpty();
  }

  @Test
  void looserBoundsAndBoundsUnderAnEqualityAreDominated() {
    Model m =
        model(
            box(3, 0, 9),
            0,
            x ->
                List.of(
                    new LinearInt(x, new int[] {1, 2, 3}, "<=", 20),
                    new LinearInt(x, new int[] {2, 4, 6}, "<=", 30), // x0 + 2x1 + 3x2 <= 15
                    new LinearInt(x, new int[] {-1, -2, -3}, "<=", -2), // >= 2
                    new LinearInt(x, new int[] {1, 2, 3}, ">", 4), // >= 5
                    new LinearInt(x, new int[] {1, 2, 3}, "!=", 3), // below the lower bound
                    new LinearInt(x, new int[] {1, 2, 3}, "!=", 7)));
    RedundantConstraints.Result r = find(m);
    List<Constraint> c = m.constraints();
    assertThat(r.dominated()).containsExactlyInAnyOrder(c.get(0), c.get(2), c.get(4));
    assertThat(r.duplicates()).isEmpty();

    Model eq =
        model(
            box(3, 0, 9),
            0,
            x ->
                List.of(
                    new LinearInt(x, new int[] {1, 2, 3}, "<=", 20),
                    new SumWeight(x, new int[] {1, 2, 3}, 12),
                    new LinearInt(x, new int[] {1, 2, 3}, ">=", 1),
                    new LinearInt(x, new int[] {1, 2, 3}, "!=", 11)));
    r = find(eq);
    c = eq.constraints();
    assertThat(r.dominated()).containsExactlyInAnyOrder(c.get(0), c.get(2), c.get(3));
  }

  @Test
  void equalitiesOfDifferentClassesAreAllKept() {
    Model m =
        model(
            box(2, 0, 9),
            0,
            x ->
                List.of(
                    new XeqY(x[0], x[1]),
                    new LinearInt(x, new int[] {1, -1}, "==", 0),
                    new LinearInt(x, new int[] {-2, 2}, "==", 0),
                    new LinearIntDom(x, new int[] {1, -1}, "==", 0),
                    new XlteqY(x[0], x[1])));
    RedundantConstraints.Result r = find(m);
    List<Constraint> c = m.constraints();
    assertThat(r.duplicates()).containsExactly(c.get(2));
    assertThat(r.dominated()).containsExactly(c.get(4));
  }

  @Test
  void coefficientStrengtheningAndGcdExposeDominance() {
    // 5b0 + 3b1 + x2 <= 6 with x2 in 0..2: b0 = 0 leaves at most 5, so 5b0 becomes 4b0 and the
    // constant 5; and 2x0 + 4x1 <= 9 is x0 + 2x1 <= 4
    Model m =
        model(
            box(3, 0, 2),
            2,
            x ->
                List.of(
                    new LinearInt(new IntVar[] {x[3], x[4], x[2]}, new int[] {5, 3, 1}, "<=", 6),
                    new LinearInt(new IntVar[] {x[3], x[4], x[2]}, new int[] {4, 3, 1}, "<=", 5),
                    new LinearInt(new IntVar[] {x[0], x[1]}, new int[] {2, 4}, "<=", 9),
                    new LinearInt(new IntVar[] {x[0], x[1]}, new int[] {1, 2}, "<=", 4)));
    RedundantConstraints.Result r = find(m);
    List<Constraint> c = m.constraints();
    assertThat(r.duplicates()).containsExactly(c.get(1), c.get(3));
  }

  @Test
  void fixedVariablesAndRepeatedVariablesAreFolded() {
    Model m =
        model(
            new int[][] {{0, 9}, {0, 9}, {4, 4}},
            0,
            x ->
                List.of(
                    new LinearInt(x, new int[] {1, 1, 1}, "<=", 10),
                    new LinearInt(new IntVar[] {x[0], x[1], x[0]}, new int[] {2, 1, -1}, "<=", 6),
                    new XplusYlteqZ(x[0], x[1], new IntVar(x[0].getStore(), "six", 6, 6))));
    RedundantConstraints.Result r = find(m);
    List<Constraint> c = m.constraints();
    assertThat(r.duplicates()).containsExactly(c.get(1), c.get(2));
  }

  @Test
  void infeasibleGroupsMakeTheDerivationInfeasible() {
    List<Function<IntVar[], List<Constraint>>> models =
        List.of(
            x ->
                List.of(
                    new LinearInt(x, new int[] {1, 1}, "==", 6),
                    new LinearInt(x, new int[] {2, 2}, "==", 10)),
            x -> List.of(new LinearInt(x, new int[] {2, 4}, "==", 7)),
            x ->
                List.of(
                    new LinearInt(x, new int[] {1, -1}, "<=", 2),
                    new LinearInt(x, new int[] {-1, 1}, "<=", -3)),
            x ->
                List.of(
                    new LinearInt(x, new int[] {1, 1}, "==", 6),
                    new LinearInt(x, new int[] {1, 1}, "!=", 6)));
    for (Function<IntVar[], List<Constraint>> f : models) {
      Model m = model(box(2, -50, 50), 0, f);
      Derivation d = Presolver.of(m.store()).presolve();
      assertThat(d.outcome()).isEqualTo(Derivation.Outcome.INFEASIBLE);
    }
  }

  @Test
  void reifiedDuplicatesNeedTheSameControlClassAndRelation() {
    Model m =
        model(
            box(2, 0, 9),
            2,
            x ->
                List.of(
                    new Reified(new XlteqY(x[0], x[1]), x[2]),
                    new Reified(new XlteqY(x[0], x[1]), x[2]),
                    new Reified(new XlteqY(x[0], x[1]), x[3]),
                    new Implies(x[2], new XlteqY(x[0], x[1])),
                    new Reified(
                        new LinearInt(new IntVar[] {x[0], x[1]}, new int[] {2, -2}, "<=", 1), x[2]),
                    new Reified(
                        new LinearInt(new IntVar[] {x[1], x[0]}, new int[] {-1, 1}, "<", 1),
                        x[2])));
    RedundantConstraints.Result r = find(m);
    List<Constraint> c = m.constraints();
    assertThat(r.duplicates()).containsExactly(c.get(1), c.get(5));
    assertThat(r.dominated()).isEmpty();
  }

  @Test
  void ruleIsIdempotent() {
    Random random = new Random(20261027);
    for (int trial = 0; trial < 50; trial++) {
      long seed = random.nextLong();
      Model m = model(box(4, -2, 3), 3, x -> randomConstraints(new Random(seed), x));
      if (!m.store().consistency()) {
        continue;
      }
      List<Constraint> kept;
      try {
        kept = new ArrayList<>(m.constraints());
        kept.removeAll(RedundantConstraints.find(kept).removed());
      } catch (FailException e) {
        continue;
      }
      assertThat(RedundantConstraints.find(kept).removed()).isEmpty();
    }
  }

  @Test
  void canonicalFormsHaveTheSameSolutionsInTheDomains() {
    Random random = new Random(20261028);
    int[] relations = {LinearForm.LE, LinearForm.GE, LinearForm.EQ, LinearForm.NE};
    for (int trial = 0; trial < 20 * TRIALS; trial++) {
      Store store = new Store();
      int n = 1 + random.nextInt(4);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        int min = random.nextInt(4) - 2;
        x[i] =
            random.nextInt(3) == 0
                ? new BooleanVar(store, "b" + i)
                : new IntVar(store, "x" + i, min, min + random.nextInt(4));
      }
      int terms = 1 + random.nextInt(5);
      IntVar[] vars = new IntVar[terms];
      long[] weights = new long[terms];
      for (int i = 0; i < terms; i++) {
        vars[i] = x[random.nextInt(n)];
        weights[i] = (random.nextInt(4) + 1L) * (random.nextInt(3) - 1) * (1 + random.nextInt(2));
      }
      LinearForm f =
          new LinearForm(
              vars, weights, random.nextInt(13) - 6L, relations[random.nextInt(relations.length)]);
      LinearForm canonical = RedundantConstraints.canonicalForm(f);
      int[] values = new int[n];
      int t = trial;
      enumerate(
          x,
          0,
          values,
          () ->
              assertThat(holds(canonical, x, values))
                  .as("trial %d: %s as %s at %s", t, f, canonical, Arrays.toString(values))
                  .isEqualTo(holds(f, x, values)));
    }
  }

  private static void enumerate(IntVar[] x, int i, int[] values, Runnable check) {
    if (i == x.length) {
      check.run();
      return;
    }
    for (int v = x[i].min(); v <= x[i].max(); v++) {
      values[i] = v;
      enumerate(x, i + 1, values, check);
    }
  }

  private static boolean holds(LinearForm f, IntVar[] x, int[] values) {
    long sum = 0;
    for (int i = 0; i < f.vars().length; i++) {
      sum += f.weights()[i] * values[Arrays.asList(x).indexOf(f.vars()[i])];
    }
    return switch (f.relation()) {
      case LinearForm.LE -> sum <= f.c();
      case LinearForm.GE -> sum >= f.c();
      case LinearForm.EQ -> sum == f.c();
      default -> sum != f.c();
    };
  }

  @Test
  void randomLinearModelsHaveTheSameSolutionsThroughPresolve() {
    Random random = new Random(20261027);
    int removed = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = random.nextLong();
      int[][] domains = box(3 + random.nextInt(2), random.nextInt(3) - 2, 2 + random.nextInt(2));
      int booleans = 2 + random.nextInt(2);
      Function<IntVar[], List<Constraint>> f = x -> randomConstraints(new Random(seed), x);

      Set<List<Integer>> expected = solve(model(domains, booleans, f), null);
      Model m = model(domains, booleans, f);
      boolean checking = trial % 2 == 0;
      Derivation d = Presolver.of(m.store()).keep(m.x()).checking(checking).presolve();
      Set<List<Integer>> found =
          d.outcome() == Derivation.Outcome.INFEASIBLE ? Set.of() : solve(m, d);
      assertThat(found).as("trial %d", trial).isEqualTo(expected);
      if (d.statistics() != null) {
        removed += d.statistics().dropped();
      }
    }
    assertThat(removed).isGreaterThan(TRIALS / 2);
  }

  /** Linear constraints of many classes over few variables, so left-hand sides repeat. */
  private static List<Constraint> randomConstraints(Random r, IntVar[] all) {
    int ints = 0;
    while (ints < all.length && !(all[ints] instanceof BooleanVar)) {
      ints++;
    }
    IntVar[] x = Arrays.copyOf(all, ints);
    IntVar[] b = Arrays.copyOfRange(all, ints, all.length);
    IntVar[] pair = {x[0], x[1]};
    List<Constraint> result = new ArrayList<>();
    int n = 4 + r.nextInt(6);
    for (int k = 0; k < n; k++) {
      int scale = 1 + r.nextInt(2);
      int[] w = {scale * (1 + r.nextInt(2)), -scale};
      String rel = RELATIONS[r.nextInt(RELATIONS.length)];
      int c = scale * (r.nextInt(5) - 2);
      result.add(
          switch (r.nextInt(10)) {
            case 0, 1 -> new LinearInt(pair, w, rel, c);
            case 2 -> new LinearInt(new IntVar[] {x[1], x[0]}, new int[] {-w[1], -w[0]}, rel, -c);
            case 3 -> new SumWeight(pair, w, c);
            case 4 -> r.nextBoolean() ? new XlteqY(x[0], x[1]) : new XneqY(x[0], x[1]);
            case 5 -> new XplusYlteqZ(x[0], x[1], x[2]);
            case 6 -> new SumInt(pair, rel.equals("!=") ? "<=" : rel, x[2]);
            case 7 -> {
              // 0/1 sums, with an integer variable for coefficient strengthening
              int[] bw = {1 + r.nextInt(4), 1 + r.nextInt(3), 1, 1};
              String br = new String[] {"==", "<=", ">="}[r.nextInt(3)];
              int sign = r.nextBoolean() ? 1 : -1;
              IntVar[] bx = Arrays.copyOf(b, b.length + 1);
              bx[b.length] = x[2];
              int[] xw = Arrays.copyOf(bw, bx.length);
              for (int i = 0; i < xw.length; i++) {
                xw[i] *= sign;
              }
              yield switch (r.nextInt(3)) {
                case 0 -> new LinearBool(b, Arrays.copyOf(bw, b.length), br, r.nextInt(4));
                case 1 -> new LinearInt(b, Arrays.copyOf(bw, b.length), br, r.nextInt(4));
                default -> new LinearInt(bx, xw, br, sign * (1 + r.nextInt(5)));
              };
            }
            case 8 -> new SumBool(b, r.nextBoolean() ? "<=" : ">=", x[2]);
            default ->
                r.nextBoolean()
                    ? new Reified(new LinearInt(pair, w, rel, c), (BooleanVar) b[0])
                    : new Implies(b[r.nextInt(b.length)], new XlteqY(x[0], x[1]));
          });
    }
    return result;
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
    if (store.consistency()) {
      if (decisions.length == 0) {
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
    }
    if (d != null) {
      d.discard();
    }
    return found;
  }
}
