/*
 * ObjectivePresolveTest.java
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
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

class ObjectivePresolveTest {

  /** obj = sum of the costs of three exactly-one sets; each set costs at least its cheapest. */
  @Test
  void shiftingByExactlyOnesRaisesTheLowerBound() {
    Store store = new Store();
    int[][] costs = {{5, 7, 9}, {3, 4}, {10, 2, 6, 8}};
    List<IntVar> lits = new ArrayList<>();
    List<Integer> weights = new ArrayList<>();
    IntVar obj = new IntVar(store, "obj", 0, 1000);
    ObjectivePresolve presolve = new ObjectivePresolve(obj, true);
    for (int[] set : costs) {
      IntVar[] b = bools(store, set.length);
      store.impose(new SumBool(b, "==", new IntVar(store, 1, 1)));
      presolve.addEquation(b, ones(b.length), 1, null);
      for (int i = 0; i < b.length; i++) {
        lits.add(b[i]);
        weights.add(set[i]);
      }
    }
    lits.add(obj);
    weights.add(-1);
    IntVar[] vars = lits.toArray(new IntVar[0]);
    int[] coefs = weights.stream().mapToInt(Integer::intValue).toArray();
    store.impose(new LinearInt(vars, coefs, "==", 0));
    presolve.addEquation(vars, coefs, 0, obj);
    assertThat(store.consistency()).isTrue();
    assertThat(obj.min()).isEqualTo(0);

    LinearInt equation = presolve.reformulate();
    assertThat(equation).isNotNull();
    assertThat(presolve.shifted()).isEqualTo(3);
    store.impose(equation);
    assertThat(store.consistency()).isTrue();
    assertThat(obj.min()).isEqualTo(5 + 3 + 2);
  }

  /** When maximising, the shift lowers the upper bound. */
  @Test
  void shiftingWhenMaximisingLowersTheUpperBound() {
    Store store = new Store();
    IntVar obj = new IntVar(store, "obj", -100, 100);
    IntVar[] b = bools(store, 3);
    store.impose(new SumBool(b, "==", new IntVar(store, 1, 1)));
    ObjectivePresolve presolve = new ObjectivePresolve(obj, false);
    presolve.addEquation(b, ones(3), 1, null);
    IntVar[] vars = {obj, b[0], b[1], b[2]};
    int[] coefs = {1, -4, -6, 5};
    // obj = 4 b0 + 6 b1 - 5 b2 + 2
    store.impose(new LinearInt(vars, coefs, "==", 2));
    presolve.addEquation(vars, coefs, 2, obj);
    assertThat(store.consistency()).isTrue();
    assertThat(obj.max()).isEqualTo(12);

    store.impose(presolve.reformulate());
    assertThat(store.consistency()).isTrue();
    assertThat(obj.max()).isEqualTo(8);
    assertThat(obj.min()).isEqualTo(-3);
  }

  /**
   * The literals {@code b_v <-> x = v} of a variable with a literal for each value form an
   * exactly-one set; with a value missing they do not.
   */
  @Test
  void valueLiteralsOfAVariableWithAllValuesFormAnExactlyOneSet() {
    for (boolean complete : new boolean[] {true, false}) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", 1, complete ? 3 : 4);
      IntVar obj = new IntVar(store, "obj", 0, 100);
      ObjectivePresolve presolve = new ObjectivePresolve(obj, true);
      IntVar[] b = bools(store, 3);
      int[] cost = {7, 4, 9};
      for (int v = 1; v <= 3; v++) {
        store.impose(new Reified(new XeqC(x, v), b[v - 1]));
        presolve.addValueLiteral(x, v, b[v - 1]);
      }
      IntVar[] vars = {b[0], b[1], b[2], obj};
      int[] coefs = {cost[0], cost[1], cost[2], -1};
      store.impose(new LinearInt(vars, coefs, "==", 0));
      presolve.addEquation(vars, coefs, 0, obj);
      assertThat(store.consistency()).isTrue();

      LinearInt equation = presolve.reformulate();
      if (complete) {
        store.impose(equation);
        assertThat(store.consistency()).isTrue();
        assertThat(obj.min()).isEqualTo(4);
      } else {
        // x = 4 costs 0
        assertThat(equation).isNull();
      }
    }
  }

  /** The objective is expanded through the equations defining its terms before shifting. */
  @Test
  void theObjectiveIsExpandedThroughDefinedVariables() {
    Store store = new Store();
    IntVar obj = new IntVar(store, "obj", 0, 1000);
    IntVar y1 = new IntVar(store, "y1", 0, 1000);
    IntVar y2 = new IntVar(store, "y2", 0, 1000);
    IntVar[] a = bools(store, 2);
    IntVar[] c = bools(store, 2);
    ObjectivePresolve presolve = new ObjectivePresolve(obj, true);
    store.impose(new SumBool(a, "==", new IntVar(store, 1, 1)));
    presolve.addEquation(a, ones(2), 1, null);
    store.impose(new SumBool(c, "==", new IntVar(store, 1, 1)));
    presolve.addEquation(c, ones(2), 1, null);
    // y1 = 3 a0 + 5 a1, y2 = 2 c0 + 8 c1 - 1, obj = 2 y1 + y2
    equation(store, presolve, new IntVar[] {y1, a[0], a[1]}, new int[] {-1, 3, 5}, 0, y1);
    equation(store, presolve, new IntVar[] {y2, c[0], c[1]}, new int[] {1, -2, -8}, -1, y2);
    equation(store, presolve, new IntVar[] {obj, y1, y2}, new int[] {1, -2, -1}, 0, obj);
    assertThat(store.consistency()).isTrue();
    // bounds reasoning alone takes y1 >= 0 and y2 >= -1
    assertThat(obj.min()).isEqualTo(0);

    LinearInt e = presolve.reformulate();
    assertThat(presolve.expanded()).isEqualTo(2);
    assertThat(presolve.shifted()).isEqualTo(2);
    store.impose(e);
    assertThat(store.consistency()).isTrue();
    assertThat(obj.min()).isEqualTo(2 * 3 + 2 - 1);
  }

  /** Without a gain there is no equation: costs whose cheapest is 0, or no linear definition. */
  @Test
  void nothingIsReturnedWithoutAGain() {
    Store store = new Store();
    IntVar obj = new IntVar(store, "obj", 0, 100);
    IntVar[] b = bools(store, 3);
    ObjectivePresolve presolve = new ObjectivePresolve(obj, true);
    presolve.addEquation(b, ones(3), 1, null);
    presolve.addEquation(new IntVar[] {obj, b[0], b[1], b[2]}, new int[] {1, 0, -3, -4}, 0, obj);
    assertThat(presolve.reformulate()).isNull();

    ObjectivePresolve undefined = new ObjectivePresolve(obj, true);
    undefined.addEquation(b, ones(3), 1, null);
    assertThat(undefined.reformulate()).isNull();
  }

  /**
   * Random models with exactly-one sets, value literals, defined intermediate costs and side
   * constraints have the same solutions with the equation imposed, and its bound is no weaker.
   */
  @Test
  void randomModelsKeepTheirSolutions() {
    Random random = new Random(20261027L);
    int checked = 0;
    for (int run = 0; run < 300; run++) {
      long seed = random.nextLong();
      List<List<Integer>> without = solutions(seed, false);
      List<List<Integer>> with = solutions(seed, true);
      assertThat(new HashSet<>(with)).as("seed %d", seed).isEqualTo(new HashSet<>(without));
      assertThat(with).as("seed %d", seed).hasSameSizeAs(without);
      if (lastReformulated) {
        checked++;
      }
    }
    assertThat(checked).isGreaterThan(100);
  }

  private static boolean lastReformulated;

  private static List<List<Integer>> solutions(long seed, boolean presolved) {
    Random r = new Random(seed);
    Store store = new Store();
    boolean minimize = r.nextBoolean();
    IntVar obj = new IntVar(store, "obj", -1000, 1000);
    ObjectivePresolve presolve = new ObjectivePresolve(obj, minimize);
    List<IntVar> all = new ArrayList<>();
    List<IntVar> terms = new ArrayList<>();
    List<Integer> termCoefs = new ArrayList<>();

    int sets = 1 + r.nextInt(3);
    List<IntVar> lits = new ArrayList<>();
    for (int s = 0; s < sets; s++) {
      if (r.nextBoolean()) {
        IntVar[] b = bools(store, 2 + r.nextInt(3));
        store.impose(new SumBool(b, "==", new IntVar(store, 1, 1)));
        presolve.addEquation(b, ones(b.length), 1, null);
        lits.addAll(Arrays.asList(b));
      } else {
        int n = 2 + r.nextInt(3);
        IntVar x = new IntVar(store, "x" + s, 0, n - 1);
        all.add(x);
        int encoded = r.nextInt(4) == 0 ? n - 1 : n;
        for (int v = 0; v < encoded; v++) {
          IntVar b = new IntVar(store, 0, 1);
          store.impose(new Reified(new XeqC(x, v), b));
          presolve.addValueLiteral(x, v, b);
          lits.add(b);
        }
      }
    }
    all.addAll(lits);
    // a random clause over the literals
    if (lits.size() > 2 && r.nextBoolean()) {
      IntVar[] p = {lits.get(r.nextInt(lits.size())), lits.get(r.nextInt(lits.size()))};
      store.impose(new BoolClause(p, new IntVar[] {lits.get(r.nextInt(lits.size()))}));
    }
    // costs, some through an intermediate variable defined by an equation
    List<IntVar> pending = new ArrayList<>(lits);
    while (!pending.isEmpty()) {
      int k = Math.min(pending.size(), 1 + r.nextInt(4));
      List<IntVar> part = new ArrayList<>(pending.subList(0, k));
      pending.subList(0, k).clear();
      if (r.nextBoolean()) {
        IntVar y = new IntVar(store, -200, 200);
        IntVar[] vars = new IntVar[k + 1];
        int[] coefs = new int[k + 1];
        int sign = r.nextBoolean() ? 1 : -1;
        vars[0] = y;
        coefs[0] = sign;
        for (int i = 0; i < k; i++) {
          vars[i + 1] = part.get(i);
          coefs[i + 1] = r.nextInt(21) - 5;
        }
        int rhs = r.nextInt(7) - 3;
        equation(store, presolve, vars, coefs, rhs, y);
        terms.add(y);
        termCoefs.add(1 + r.nextInt(3));
      } else {
        for (IntVar b : part) {
          terms.add(b);
          termCoefs.add(r.nextInt(21) - 5);
        }
      }
    }
    IntVar[] vars = new IntVar[terms.size() + 1];
    int[] coefs = new int[vars.length];
    vars[0] = obj;
    coefs[0] = r.nextBoolean() ? 1 : -1;
    for (int i = 0; i < terms.size(); i++) {
      vars[i + 1] = terms.get(i);
      coefs[i + 1] = termCoefs.get(i);
    }
    equation(store, presolve, vars, coefs, r.nextInt(11) - 5, obj);
    all.add(obj);

    lastReformulated = false;
    if (!store.consistency()) {
      return List.of();
    }
    if (presolved) {
      LinearInt equation = presolve.reformulate();
      if (equation != null) {
        lastReformulated = true;
        int before = minimize ? obj.min() : obj.max();
        store.impose(equation);
        if (!store.consistency()) {
          return List.of();
        }
        assertThat(minimize ? obj.min() >= before : obj.max() <= before).isTrue();
      }
    }
    IntVar[] decisions = all.toArray(new IntVar[0]);
    List<List<Integer>> found = new ArrayList<>();
    Search<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select = new SimpleSelect<>(decisions, null, new IndomainMin<>());
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> sel) {
            boolean result = super.executeAfterSolution(s, sel);
            List<Integer> values = new ArrayList<>();
            for (IntVar v : decisions) {
              values.add(v.value());
            }
            found.add(values);
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setPrintInfo(false);
    search.labeling(store, select);
    return found;
  }

  private static void equation(
      Store store, ObjectivePresolve presolve, IntVar[] vars, int[] coefs, int rhs, IntVar y) {
    store.impose(new LinearInt(vars, coefs, "==", rhs));
    presolve.addEquation(vars, coefs, rhs, y);
  }

  private static IntVar[] bools(Store store, int n) {
    IntVar[] b = new IntVar[n];
    for (int i = 0; i < n; i++) {
      b[i] = new IntVar(store, 0, 1);
    }
    return b;
  }

  private static int[] ones(int n) {
    int[] a = new int[n];
    Arrays.fill(a, 1);
    return a;
  }
}
