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
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.OrBool;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
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
   * A count of a value over encoded variables is expanded into the value literals, so its cost
   * takes part in the shift: each byte is ASCII-free here and costs at least its cheapest of the
   * other encodings or the unknown one, as in jp-encoding.
   */
  @Test
  void aCountIsExpandedIntoTheValueLiteralsOfItsVariables() {
    Store store = new Store();
    // x[i] in 1..3, value 3 is "unknown" and costs 100 through the count n
    int[][] cost = {{6, 9}, {8, 5}, {7, 7}};
    IntVar[] x = new IntVar[cost.length];
    List<IntVar> vars = new ArrayList<>();
    List<Integer> coefs = new ArrayList<>();
    IntVar obj = new IntVar(store, "obj", 0, 1000);
    ObjectivePresolve presolve = new ObjectivePresolve(obj, true);
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 3);
      for (int v = 1; v <= 3; v++) {
        IntVar b = new IntVar(store, 0, 1);
        store.impose(new Reified(new XeqC(x[i], v), b));
        presolve.addValueLiteral(x[i], v, b);
        if (v < 3) {
          vars.add(b);
          coefs.add(cost[i][v - 1]);
        }
      }
    }
    IntVar n = new IntVar(store, "n", 0, x.length);
    store.impose(new Count(x, n, 3));
    presolve.addCount(x, 3, n);
    vars.add(n);
    coefs.add(100);
    vars.add(obj);
    coefs.add(-1);
    equation(
        store,
        presolve,
        vars.toArray(new IntVar[0]),
        coefs.stream().mapToInt(Integer::intValue).toArray(),
        0,
        obj);
    assertThat(store.consistency()).isTrue();
    assertThat(obj.min()).isEqualTo(0);

    List<Constraint> reformulation = presolve.reformulate(store);
    assertThat(presolve.expanded()).isEqualTo(1);
    assertThat(presolve.shifted()).isEqualTo(3);
    // one element constraint per variable, then the equation
    assertThat(reformulation).hasSize(4);
    reformulation.forEach(store::impose);
    assertThat(store.consistency()).isTrue();
    assertThat(obj.min()).isEqualTo(6 + 5 + 7);

    // a cost bound prunes the values of each variable through its cost variable
    obj.domain.inMax(store.level, obj, 6 + 5 + 7);
    assertThat(store.consistency()).isTrue();
    assertThat(x[0].singleton(1)).isTrue();
    assertThat(x[1].singleton(2)).isTrue();
    assertThat(x[2].min()).isEqualTo(1);
    assertThat(x[2].max()).isEqualTo(2);
  }

  /** A count over a variable without a literal for the counted value is not expanded. */
  @Test
  void aCountWithoutAllLiteralsIsNotExpanded() {
    Store store = new Store();
    IntVar obj = new IntVar(store, "obj", 0, 1000);
    ObjectivePresolve presolve = new ObjectivePresolve(obj, true);
    IntVar x = new IntVar(store, "x", 1, 2);
    IntVar y = new IntVar(store, "y", 1, 2);
    IntVar[] bx = bools(store, 2);
    for (int v = 1; v <= 2; v++) {
      store.impose(new Reified(new XeqC(x, v), bx[v - 1]));
      presolve.addValueLiteral(x, v, bx[v - 1]);
    }
    IntVar n = new IntVar(store, "n", 0, 2);
    store.impose(new Count(new IntVar[] {x, y}, n, 2));
    presolve.addCount(new IntVar[] {x, y}, 2, n);
    // obj = 3 (x = 1) + 10 n: y = 2 has no literal
    equation(store, presolve, new IntVar[] {obj, bx[0], n}, new int[] {1, -3, -10}, 0, obj);
    assertThat(store.consistency()).isTrue();
    assertThat(presolve.reformulate(store)).isEmpty();
    assertThat(presolve.expanded()).isZero();
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
      List<List<Integer>> without = solutions(seed, Mode.NONE);
      for (Mode mode : new Mode[] {Mode.EQUATION, Mode.COST_VARIABLES}) {
        List<List<Integer>> with = solutions(seed, mode);
        assertThat(new HashSet<>(with))
            .as("seed %d %s", seed, mode)
            .isEqualTo(new HashSet<>(without));
        assertThat(with).as("seed %d %s", seed, mode).hasSameSizeAs(without);
      }
      if (lastReformulated) {
        checked++;
      }
    }
    assertThat(checked).isGreaterThan(100);
  }

  /**
   * An assignment as in rel2onto: x[i] all different, a node v is used ({@code u_v <-> or(x[i] =
   * v)}) when some x[i] takes it, an edge e_v equal to u_v costs w_v, and x[i] costs c_i[x[i]]
   * through an element. The disjunction of exclusive literals is a sum, the edge is replaced by the
   * equal disjunction, and each x[i] costs at least its cheapest c_i[v] + w_v.
   */
  @Test
  void anExclusiveDisjunctionReachedThroughEqualitiesIsExpanded() {
    for (boolean allDifferent : new boolean[] {true, false}) {
      Store store = new Store();
      IntVar obj = new IntVar(store, "obj", 0, 1000);
      ObjectivePresolve presolve = new ObjectivePresolve(obj, true);
      int[][] cost = {{0, 4, 9}, {3, 0, 5}};
      int[] w = {10, 20, 6};
      IntVar[] x = {new IntVar(store, "x0", 1, 3), new IntVar(store, "x1", 1, 3)};
      if (allDifferent) {
        store.impose(new Alldistinct(x));
        presolve.addAllDifferent(x);
      }
      IntVar[][] lit = new IntVar[x.length][];
      for (int i = 0; i < x.length; i++) {
        lit[i] = bools(store, 3);
        for (int v = 1; v <= 3; v++) {
          store.impose(new Reified(new XeqC(x[i], v), lit[i][v - 1]));
          presolve.addValueLiteral(x[i], v, lit[i][v - 1]);
        }
      }
      List<IntVar> vars = new ArrayList<>(List.of(obj));
      List<Integer> coefs = new ArrayList<>(List.of(-1));
      for (int v = 1; v <= 3; v++) {
        IntVar used = new IntVar(store, "u" + v, 0, 1);
        IntVar[] or = {lit[0][v - 1], lit[1][v - 1]};
        store.imposeDecomposition(new OrBool(or, used));
        presolve.addOr(used, or);
        IntVar edge = new IntVar(store, "e" + v, 0, 1);
        store.impose(new XeqY(edge, used));
        presolve.addEquality(edge, used);
        vars.add(edge);
        coefs.add(w[v - 1]);
      }
      for (int i = 0; i < x.length; i++) {
        IntVar y = new IntVar(store, "y" + i, 0, 9);
        store.impose(new ElementInteger(x[i], cost[i], y, 0));
        presolve.addElement(x[i], cost[i], 1, y);
        vars.add(y);
        coefs.add(1);
      }
      equation(
          store,
          presolve,
          vars.toArray(new IntVar[0]),
          coefs.stream().mapToInt(Integer::intValue).toArray(),
          0,
          obj);
      assertThat(store.consistency()).isTrue();
      assertThat(obj.min()).isZero();

      List<Constraint> reformulation = presolve.reformulate(store);
      if (!allDifferent) {
        // two variables may take the same node, so the disjunction is not a sum
        assertThat(reformulation).isEmpty();
        continue;
      }
      assertThat(presolve.shifted()).isEqualTo(2);
      reformulation.forEach(store::impose);
      assertThat(store.consistency()).isTrue();
      // x0 costs at least min(0 + 10, 4 + 20, 9 + 6) = 10, x1 at least min(13, 20, 11) = 11
      assertThat(obj.min()).isEqualTo(10 + 11);
    }
  }

  /**
   * Random assignments with all-different constraints, value literals, disjunctions of the literals
   * of one value, equalities and element costs have the same solutions with the reformulation
   * imposed, and its bound is no weaker.
   */
  @Test
  void randomAssignmentsKeepTheirSolutions() {
    Random random = new Random(20261028L);
    int reformulated = 0;
    for (int run = 0; run < 200; run++) {
      long seed = random.nextLong();
      List<List<Integer>> without = assignmentSolutions(seed, false);
      List<List<Integer>> with = assignmentSolutions(seed, true);
      assertThat(new HashSet<>(with)).as("seed %d", seed).isEqualTo(new HashSet<>(without));
      assertThat(with).as("seed %d", seed).hasSameSizeAs(without);
      if (lastReformulated) {
        reformulated++;
      }
    }
    assertThat(reformulated).isGreaterThan(50);
  }

  private static List<List<Integer>> assignmentSolutions(long seed, boolean reformulate) {
    Random r = new Random(seed);
    Store store = new Store();
    boolean minimize = r.nextBoolean();
    IntVar obj = new IntVar(store, "obj", -1000, 1000);
    ObjectivePresolve presolve = new ObjectivePresolve(obj, minimize);
    int n = 2 + r.nextInt(2);
    int values = n + r.nextInt(2);
    IntVar[] x = new IntVar[n];
    IntVar[][] lit = new IntVar[n][values];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 1, values);
      for (int v = 1; v <= values; v++) {
        lit[i][v - 1] = new IntVar(store, 0, 1);
        store.impose(new Reified(new XeqC(x[i], v), lit[i][v - 1]));
        presolve.addValueLiteral(x[i], v, lit[i][v - 1]);
      }
    }
    // all different over all variables, over some of them, or not at all
    int different = r.nextInt(3) == 0 ? 0 : 2 + r.nextInt(n - 1);
    if (different > 0) {
      IntVar[] d = Arrays.copyOf(x, different);
      store.impose(new Alldistinct(d));
      presolve.addAllDifferent(d);
    }
    List<IntVar> all = new ArrayList<>(Arrays.asList(x));
    List<IntVar> vars = new ArrayList<>(List.of(obj));
    List<Integer> coefs = new ArrayList<>(List.of(-1));
    for (int v = 1; v <= values; v++) {
      IntVar used = new IntVar(store, "u" + v, 0, 1);
      IntVar[] or = new IntVar[n];
      for (int i = 0; i < n; i++) {
        or[i] = lit[i][v - 1];
      }
      store.imposeDecomposition(new OrBool(or, used));
      presolve.addOr(used, or);
      IntVar term = used;
      if (r.nextBoolean()) {
        term = new IntVar(store, "e" + v, 0, 1);
        store.impose(new XeqY(term, used));
        presolve.addEquality(term, used);
      }
      all.add(term);
      vars.add(term);
      coefs.add(r.nextInt(21) - 5);
    }
    for (int i = 0; i < n; i++) {
      if (r.nextBoolean()) {
        int[] cost = new int[values];
        for (int v = 0; v < values; v++) {
          cost[v] = r.nextInt(15) - 3;
        }
        IntVar y = new IntVar(store, "y" + i, -3, 11);
        store.impose(new ElementInteger(x[i], cost, y, 0));
        presolve.addElement(x[i], cost, 1, y);
        all.add(y);
        vars.add(y);
        coefs.add(1 + r.nextInt(2));
      }
    }
    equation(
        store,
        presolve,
        vars.toArray(new IntVar[0]),
        coefs.stream().mapToInt(Integer::intValue).toArray(),
        r.nextInt(7) - 3,
        obj);
    all.add(obj);
    lastReformulated = false;
    if (!store.consistency()) {
      return List.of();
    }
    if (reformulate) {
      List<Constraint> reformulation = presolve.reformulate(store);
      if (!reformulation.isEmpty()) {
        lastReformulated = true;
        int before = minimize ? obj.min() : obj.max();
        reformulation.forEach(store::impose);
        if (!store.consistency()) {
          return List.of();
        }
        assertThat(minimize ? obj.min() >= before : obj.max() <= before).isTrue();
      }
    }
    return allSolutions(store, all.toArray(new IntVar[0]));
  }

  private static boolean lastReformulated;

  /** How the random models are solved: as given, with the equation, with cost variables too. */
  private enum Mode {
    NONE,
    EQUATION,
    COST_VARIABLES
  }

  private static List<List<Integer>> solutions(long seed, Mode mode) {
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
    List<IntVar> encodedVars = new ArrayList<>();
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
        encodedVars.add(x);
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
    // a count of a value over the encoded variables, as a cost
    List<IntVar> counted = new ArrayList<>();
    if (!encodedVars.isEmpty() && r.nextBoolean()) {
      IntVar n = new IntVar(store, "n", 0, encodedVars.size());
      int value = r.nextInt(3);
      store.impose(new Count(encodedVars, n, value));
      presolve.addCount(encodedVars.toArray(new IntVar[0]), value, n);
      all.add(n);
      counted.add(n);
    }
    // a random clause over the literals
    if (lits.size() > 2 && r.nextBoolean()) {
      IntVar[] p = {lits.get(r.nextInt(lits.size())), lits.get(r.nextInt(lits.size()))};
      store.impose(new BoolClause(p, new IntVar[] {lits.get(r.nextInt(lits.size()))}));
    }
    // costs, some through an intermediate variable defined by an equation
    List<IntVar> pending = new ArrayList<>(lits);
    pending.addAll(counted);
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
    if (mode != Mode.NONE) {
      List<Constraint> reformulation =
          mode == Mode.EQUATION ? listOf(presolve.reformulate()) : presolve.reformulate(store);
      if (!reformulation.isEmpty()) {
        lastReformulated = true;
        int before = minimize ? obj.min() : obj.max();
        reformulation.forEach(store::impose);
        if (!store.consistency()) {
          return List.of();
        }
        assertThat(minimize ? obj.min() >= before : obj.max() <= before).isTrue();
      }
    }
    return allSolutions(store, all.toArray(new IntVar[0]));
  }

  private static List<List<Integer>> allSolutions(Store store, IntVar[] decisions) {
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

  private static List<Constraint> listOf(LinearInt equation) {
    return equation == null ? List.of() : List.of(equation);
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
