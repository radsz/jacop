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
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
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
 * Dominance breaking nogoods on random small optimisation models: every solution left is a solution
 * of the original model, and the optimum stays.
 */
class DominanceNogoodsTest {

  private static final int TRIALS = Integer.getInteger("presolve.dominance.trials", 3000);

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  /**
   * A random model: variables in small ranges, the first {@code booleans} of them 0/1, possibly an
   * intermediate sum, and the last variable the objective, defined by a linear equality.
   */
  private record Model(
      int[][] domains,
      int booleans,
      boolean maximize,
      boolean intermediate,
      long seed,
      int constraints) {

    IntVar[] build(Store store) {
      IntVar[] x = new IntVar[domains.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, domains[i][0], domains[i][1]);
      }
      int n = x.length - 2;
      IntVar[] inner = Arrays.copyOf(x, n);
      Random r = new Random(seed);
      for (int k = 0; k < constraints; k++) {
        store.impose(randomConstraint(r, inner, booleans));
      }
      if (n >= 2 && r.nextBoolean()) {
        // a functional element: x[j] = list[x[i]]
        int i = r.nextInt(n);
        int j = r.nextInt(n);
        if (i != j) {
          int[] list = new int[6];
          for (int k = 0; k < list.length; k++) {
            list[k] = r.nextInt(5) - 1;
          }
          store.impose(new ElementInteger(x[i], list, x[j], -2));
        }
      }
      // x[n] = sum of some terms, an intermediate the objective may use
      int[] wz = new int[n + 1];
      IntVar[] tz = Arrays.copyOf(x, n + 1);
      for (int i = 0; i < n; i++) {
        wz[i] = r.nextInt(3) - 1;
      }
      wz[n] = -1;
      store.impose(new LinearInt(tz, wz, "==", 0));
      if (r.nextInt(3) == 0) {
        store.impose(new XlteqC(x[n], r.nextInt(4)));
      }
      int[] w = new int[n + 2];
      for (int i = 0; i < n; i++) {
        w[i] = r.nextInt(5) - 2;
      }
      w[n] = intermediate ? r.nextInt(3) - 1 : 0;
      w[n + 1] = r.nextBoolean() ? 1 : -1;
      store.impose(new LinearInt(x, w, "==", r.nextInt(3)));
      return x;
    }
  }

  @Test
  void randomModelsKeepTheOptimum() {
    Random random = new Random(20261112);
    int fired = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Model model = randomModel(random);
      Set<List<Integer>> expected = solve(model, false, 0, null);
      int[] nogoods = new int[1];
      Set<List<Integer>> found = solve(model, true, random.nextInt(), nogoods);
      String context = "trial " + trial + ", " + model;
      assertThat(expected).as(context).containsAll(found);
      assertThat(found.isEmpty()).as(context).isEqualTo(expected.isEmpty());
      if (!expected.isEmpty()) {
        assertThat(best(model, found)).as(context).isEqualTo(best(model, expected));
      }
      if (nogoods[0] > 0) {
        fired++;
      }
    }
    assertThat(fired).isGreaterThan(TRIALS / 10);
  }

  @Test
  void aKnapsackGetsTheSwapNogood() {
    // maximise 5a + 4b with 3a + 3b <= 3: b = 1 and a = 0 is dominated by a = 1 and b = 0
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar p = new IntVar(store, "p", 0, 9);
    store.impose(new LinearInt(new IntVar[] {a, b}, new int[] {3, 3}, "<=", 3));
    store.impose(new LinearInt(new IntVar[] {a, b, p}, new int[] {5, 4, -1}, "==", 0));
    assertThat(store.consistency()).isTrue();
    DominanceNogoods.Outcome o = new DominanceNogoods(store, p, false).run();
    assertThat(o.nogoods()).isGreaterThan(0);
    assertThat(store.consistency()).isTrue();
    b.domain.in(store.level, b, 1, 1);
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void anObjectiveBoundAboveTheDefinitionStopsTheRule() {
    // the objective's domain cuts the improving side, so no change may lower it
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar p = new IntVar(store, "p", 2, 9);
    store.impose(new LinearInt(new IntVar[] {a, b, p}, new int[] {1, 2, -1}, "==", 0));
    DominanceNogoods.Outcome o = new DominanceNogoods(store, p, true).run();
    assertThat(o.skipped()).isNotNull();
  }

  private static Integer best(Model model, Iterable<List<Integer>> solutions) {
    Integer best = null;
    for (List<Integer> s : solutions) {
      int v = s.getLast();
      if (best == null || (model.maximize() ? v > best : v < best)) {
        best = v;
      }
    }
    return best;
  }

  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(4);
    int booleans = random.nextInt(n + 1);
    int[][] domains = new int[n + 2][];
    for (int i = 0; i < n; i++) {
      if (i < booleans) {
        domains[i] = new int[] {0, 1};
      } else {
        int min = random.nextInt(3) - 1;
        domains[i] = new int[] {min, min + random.nextInt(4)};
      }
    }
    domains[n] = random.nextInt(4) == 0 ? new int[] {-1, 3} : new int[] {-20, 20};
    domains[n + 1] = random.nextInt(4) == 0 ? new int[] {-2, 30} : new int[] {-80, 80};
    return new Model(
        domains,
        booleans,
        random.nextBoolean(),
        random.nextBoolean(),
        random.nextLong(),
        random.nextInt(5));
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
              switch (r.nextInt(3)) {
                case 0 -> new XlteqC(a, r.nextInt(3));
                case 1 -> new XgteqC(a, r.nextInt(3));
                default -> new XeqC(a, r.nextInt(3));
              },
              b);
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

  private static Set<List<Integer>> solve(Model model, boolean nogoods, int seed, int[] count) {
    Store store = new Store();
    IntVar[] x = model.build(store);
    Set<List<Integer>> found = new HashSet<>();
    if (!store.consistency()) {
      return found;
    }
    if (nogoods) {
      DominanceNogoods.Outcome o =
          new DominanceNogoods(store, x[x.length - 1], !model.maximize()).run();
      count[0] = (int) o.nogoods() + o.removed();
      if (!store.consistency()) {
        return found;
      }
    }
    search(store, x, seed, () -> found.add(values(x)));
    return found;
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
