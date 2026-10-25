/*
 * LcgFuzzTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with Section 7 of the License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.fail;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.AllEqual;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Among;
import org.jacop.constraints.AmongVar;
import org.jacop.constraints.And;
import org.jacop.constraints.AndBool;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Conditional;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Distance;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.Eq;
import org.jacop.constraints.GCC;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.Implies;
import org.jacop.constraints.In;
import org.jacop.constraints.Increasing;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.NoGood;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.OrBool;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.Sort;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.Values;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.constraints.table.Table;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Differential fuzzing of lazy clause generation: random small models over a broad pool of
 * constraints are solved by {@link LcgSolver} with the explanation checker on and by JaCoP's
 * depth-first search, and the two must agree on satisfiability and on the optimum of a random
 * objective. The solution LCG reports must also extend to a solution of a fresh copy of the model.
 *
 * <p>The number of models is set by {@code lcg.fuzz.runs} (default 2000, 300 in the {@code min}
 * profile) and the first seed by {@code lcg.fuzz.seed} (default 1). A failure names the seed, which
 * rebuilds the same model.
 */
class LcgFuzzTest {

  private static final int RUNS = Integer.getInteger("lcg.fuzz.runs", 2000);

  private static final int SEED = Integer.getInteger("lcg.fuzz.seed", 1);

  /** A random model; built twice from the same seed, once for each solver. */
  private static final class Model {
    final Store store = new Store();
    final Random rnd;
    final List<IntVar> vars = new ArrayList<>();
    final List<String> posted = new ArrayList<>();
    IntVar[] x;
    IntVar[] b;
    IntVar objective;

    Model(long seed) {
      rnd = new Random(seed);
      int n = 4 + rnd.nextInt(4);
      x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = intVar("x" + i, rnd.nextInt(3) - 1, 2 + rnd.nextInt(3));
        if (rnd.nextInt(3) == 0 && x[i].max() - x[i].min() >= 2) {
          x[i].domain.subtractAdapt(x[i].min() + 1 + rnd.nextInt(x[i].max() - x[i].min() - 1));
        }
      }
      b = new IntVar[3 + rnd.nextInt(2)];
      for (int i = 0; i < b.length; i++) {
        if (rnd.nextBoolean()) {
          b[i] = new BooleanVar(store, "b" + i);
          vars.add(b[i]);
        } else {
          b[i] = intVar("b" + i, 0, 1);
        }
      }
      int m = 2 + rnd.nextInt(6);
      for (int i = 0; i < m; i++) {
        try {
          post(randomConstraint());
        } catch (IllegalArgumentException e) {
          // arguments the constraint rejects, such as a variable repeated; draw another one
          i--;
        }
      }
      if (rnd.nextBoolean()) {
        objective = rnd.nextBoolean() ? x[rnd.nextInt(n)] : sumObjective();
      }
    }

    private IntVar intVar(String name, int min, int max) {
      IntVar v = new IntVar(store, name, min, max);
      vars.add(v);
      return v;
    }

    private IntVar sumObjective() {
      IntVar[] list = pick(x, 3);
      int[] w = {1 + rnd.nextInt(3), -1 - rnd.nextInt(2), 1};
      IntVar sum = intVar("obj", -30, 30);
      store.impose(
          new LinearInt(
              new IntVar[] {list[0], list[1], list[2], sum},
              new int[] {w[0], w[1], w[2], -1},
              "==",
              0));
      posted.add(
          "obj = "
              + w[0]
              + "*"
              + list[0].id()
              + " + "
              + w[1]
              + "*"
              + list[1].id()
              + " + "
              + list[2].id());
      return sum;
    }

    private void post(Object c) {
      posted.add(c.toString());
      if (c instanceof Constraint constraint) {
        store.impose(constraint);
      } else {
        @SuppressWarnings("unchecked")
        DecomposedConstraint<Constraint> d = (DecomposedConstraint<Constraint>) c;
        store.imposeDecomposition(d);
      }
    }

    private IntVar[] pick(IntVar[] from, int k) {
      List<IntVar> pool = new ArrayList<>(List.of(from));
      IntVar[] result = new IntVar[Math.min(k, pool.size())];
      for (int i = 0; i < result.length; i++) {
        result[i] = pool.remove(rnd.nextInt(pool.size()));
      }
      return result;
    }

    private IntVar one() {
      return x[rnd.nextInt(x.length)];
    }

    private IntVar bool() {
      return b[rnd.nextInt(b.length)];
    }

    private int value() {
      return rnd.nextInt(5) - 1;
    }

    private IntVar[] chain(String name, int k, int min, int max) {
      IntVar[] y = new IntVar[k];
      for (int i = 0; i < k; i++) {
        y[i] = intVar(name + i, min, max);
      }
      return y;
    }

    PrimitiveConstraint primitive(int depth) {
      IntVar[] p = pick(x, 3);
      int c = value();
      return switch (rnd.nextInt(depth > 0 ? 18 : 14)) {
        case 0 -> new XeqY(p[0], p[1]);
        case 1 -> new XneqY(p[0], p[1]);
        case 2 -> new XltY(p[0], p[1]);
        case 3 -> new XlteqY(p[0], p[1]);
        case 4 -> new XeqC(p[0], c);
        case 5 -> new XneqC(p[0], c);
        case 6 -> new XlteqC(p[0], c);
        case 7 -> new XgtC(p[0], c);
        case 8 -> new XplusCeqZ(p[0], c, p[1]);
        case 9 -> new XplusYlteqZ(p[0], p[1], p[2]);
        case 10 ->
            new LinearInt(
                p, new int[] {1 + rnd.nextInt(2), -1, 2}, rnd.nextBoolean() ? "<=" : "!=", c + 2);
        case 11 -> new XplusYeqC(p[0], p[1], c + 2);
        case 12 -> new Member(pick(x, 3), p[0]);
        case 13 -> new XeqC(bool(), rnd.nextInt(2));
        case 14 -> new Not(primitive(depth - 1));
        case 15 -> new Or(primitive(depth - 1), primitive(depth - 1));
        case 16 -> new And(primitive(depth - 1), primitive(depth - 1));
        default -> new IfThen(primitive(depth - 1), primitive(depth - 1));
      };
    }

    Object randomConstraint() {
      IntVar[] p = pick(x, 3);
      IntVar[] q = pick(x, 2 + rnd.nextInt(3));
      return switch (rnd.nextInt(52)) {
        case 0 -> primitive(1);
        case 1 ->
            new LinearInt(p, new int[] {2, -1, 3}, rnd.nextBoolean() ? "<=" : ">=", value() + 2);
        case 2 -> new LinearInt(p, new int[] {1, 1, -1}, "==", value());
        case 3 -> new XplusYeqZ(p[0], p[1], p[2]);
        case 4 -> new XmulYeqZ(p[0], p[1], p[2]);
        case 5 -> new XmulCeqZ(p[0], 2 - rnd.nextInt(4), p[1]);
        case 6 -> new AbsXeqY(p[0], p[1]);
        case 7 -> new Distance(p[0], p[1], p[2]);
        case 8 -> new XexpYeqZ(p[0], intVar("e", 0, 2), p[1]);
        case 9 -> new Alldistinct(q);
        case 10 -> new Alldifferent(q);
        case 11 -> new Alldiff(q);
        case 12 -> new AlldifferentExcept(q, new IntervalDomain(0, 0));
        case 13 -> new Max(q, one());
        case 14 -> new Min(q, one());
        case 15 -> new ArgMin(q, intVar("i", 1, q.length));
        case 16 -> new ArgMax(q, intVar("i", 1, q.length));
        case 17 ->
            new ElementInteger(one(), new int[] {value(), value(), value(), value()}, one(), 0);
        case 18 -> new ElementVariable(one(), q, one(), 0);
        case 19 -> new Count(q, one(), value());
        case 20 -> new CountValues(q, pick(x, 2), new int[] {0, 1});
        case 21 -> new GCC(chain("g", 3, 0, 2), chain("c", 3, 0, 3));
        case 22 -> new Among(q, new IntervalDomain(0, 1), one());
        case 23 -> new AmongVar(q, pick(x, 2), one());
        case 24 -> new AtMost(q, 1 + rnd.nextInt(2), value());
        case 25 -> new AtLeast(q, rnd.nextInt(2), value());
        case 26 -> new Values(q, one());
        case 27 -> new Increasing(q, rnd.nextBoolean());
        case 28 -> new AllEqual(pick(x, 2));
        case 29 -> new ValuePrecede(0, 1, q);
        case 30 -> new Member(q, one());
        case 31 -> new In(one(), new IntervalDomain(-1, 1));
        case 32 -> new SumWeight(q, new int[] {1, 2, -1, 1}, one());
        case 33 -> new SumBool(b, rnd.nextBoolean() ? "<=" : "==", intVar("s", 0, 2));
        case 34 -> new AndBool(pick(b, 2), bool());
        case 35 -> new OrBool(pick(b, 3), bool());
        case 36 -> new XorBool(pick(b, 2), bool());
        case 37 -> new Reified(primitive(1), bool());
        case 38 -> new Implies(bool(), primitive(1));
        case 39 -> new Xor(primitive(1), bool());
        case 40 -> new Eq(primitive(0), primitive(0));
        case 41 -> new IfThenElse(primitive(0), primitive(0), primitive(0));
        case 42 ->
            new Conditional(pick(b, 2), new PrimitiveConstraint[] {primitive(0), primitive(0)});
        case 43 -> new NoGood(q, new int[] {0, 1, 2, 0});
        case 44 -> new Lex(new IntVar[][] {pick(x, 2), pick(x, 2)}, rnd.nextBoolean());
        case 45 -> new Sequence(q, new IntervalDomain(0, 1), 2, 0, 1);
        case 46 -> new Sort(pick(x, 2), pick(x, 2));
        case 47 -> new SimpleTable(pick(x, 2), new int[][] {{0, 1}, {1, 2}, {2, 0}, {-1, 3}});
        case 48 -> new Table(pick(x, 2), new int[][] {{0, 0}, {1, 3}, {3, 1}, {2, 2}});
        case 49 -> {
          IntVar[] next = chain("n", 3 + rnd.nextInt(2), 1, 4);
          for (IntVar v : next) {
            v.domain.in(store.level, v, 1, next.length);
          }
          posted.add("link " + next[0].id() + " <= " + p[0].id());
          store.impose(new XlteqY(next[0], p[0]));
          yield rnd.nextBoolean() ? new Circuit(next) : new Subcircuit(next);
        }
        case 50 -> {
          IntVar[] xs = chain("a", 3, 0, 2);
          IntVar[] ds = chain("d", 3, 0, 2);
          posted.add("link " + xs[0].id() + " = " + p[0].id());
          store.impose(new XeqY(xs[0], p[0]));
          yield new Assignment(xs, ds, 0, 0);
        }
        default ->
            switch (rnd.nextInt(3)) {
              case 0 -> {
                IntVar[] s = pick(x, 3);
                yield new Cumulative(
                    s, constants(3, 1, 3), constants(3, 1, 2), constant(2 + rnd.nextInt(2)));
              }
              case 1 ->
                  new Binpacking(
                      pick(x, 3), chain("l", 3, 0, 4), new int[] {1 + rnd.nextInt(3), 2, 1}, -1);
              default -> {
                IntVar[] o = pick(x, 3);
                IntVar[] o2 = pick(x, 3);
                yield new Diffn(o, o2, constants(3, 1, 2), constants(3, 1, 2));
              }
            };
      };
    }

    private IntVar constant(int c) {
      return new IntVar(store, c, c);
    }

    private IntVar[] constants(int k, int min, int max) {
      IntVar[] c = new IntVar[k];
      for (int i = 0; i < k; i++) {
        c[i] = constant(min + rnd.nextInt(max - min + 1));
      }
      return c;
    }

    IntVar[] decisionVars() {
      return vars.toArray(IntVar[]::new);
    }

    String describe() {
      StringBuilder s = new StringBuilder();
      for (IntVar v : vars) {
        s.append(v).append('\n');
      }
      for (String c : posted) {
        s.append(c).append('\n');
      }
      s.append("minimize ").append(objective == null ? "-" : objective.id());
      return s.toString();
    }
  }

  /** The reference answer: null when unsatisfiable, else the optimum (0 for satisfaction). */
  private static Integer reference(Model model) {
    if (!model.store.consistency()) {
      return null;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    SimpleSelect<IntVar> select =
        new SimpleSelect<>(model.decisionVars(), null, new IndomainMin<>());
    boolean found =
        model.objective == null
            ? search.labeling(model.store, select)
            : search.labeling(model.store, select, model.objective);
    if (!found) {
      return null;
    }
    return model.objective == null ? 0 : search.getCostValue();
  }

  /** Whether the given values of the model's variables extend to a solution of a fresh copy. */
  private static boolean extendsToSolution(long seed, int[] values) {
    Model model = new Model(seed);
    IntVar[] vars = model.decisionVars();
    for (int i = 0; i < vars.length; i++) {
      if (!vars[i].domain.contains(values[i])) {
        return false;
      }
      model.store.impose(new XeqC(vars[i], values[i]));
    }
    if (!model.store.consistency()) {
      return false;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    return search.labeling(model.store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
  }

  @Test
  void agreesWithSearchOnRandomModels() {
    Map<String, long[]> statistics = new TreeMap<>();
    int sat = 0;
    int unsat = 0;
    long checked = 0;
    for (int run = 0; run < RUNS; run++) {
      long seed = SEED + (long) run;
      Integer expected = reference(new Model(seed));
      Model model = new Model(seed);
      String where = "seed " + seed + "\n" + model.describe();
      int status;
      int[] values;
      try {
        LcgSolver solver = new LcgSolver(model.store);
        solver.setChecking(true);
        status = model.objective == null ? solver.solve() : solver.minimize(model.objective);
        checked += solver.checker().checked;
        IntVar[] vars = model.decisionVars();
        values = new int[vars.length];
        if (status == CdclSolver.SAT) {
          for (int i = 0; i < vars.length; i++) {
            values[i] = solver.value(vars[i]);
          }
          if (expected != null && model.objective != null) {
            assertThat(solver.value(model.objective)).as(where).isEqualTo(expected);
          }
        }
        solver
            .explanationStatistics()
            .forEach((k, v) -> statistics.merge(k, v.clone(), LcgFuzzTest::add));
      } catch (RuntimeException e) {
        throw new AssertionError(where, e);
      }
      assertThat(status).as(where).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(status == CdclSolver.SAT).as(where).isEqualTo(expected != null);
      if (status == CdclSolver.SAT && !extendsToSolution(seed, values)) {
        fail("the LCG solution " + Arrays.toString(values) + " is not a solution: " + where);
      }
      if (expected == null) {
        unsat++;
      } else {
        sat++;
      }
    }
    if (RUNS >= 1000) {
      System.out.printf(
          "lcg fuzz: %d runs, %d sat, %d unsat, %d explanations checked%n",
          RUNS, sat, unsat, checked);
      statistics.forEach(
          (k, v) ->
              System.out.printf(
                  "  %-24s reasons=%d generic=%d failures=%d generic=%d%n",
                  k, v[0], v[1], v[3], v[4]));
    }
    assertThat(sat).isPositive();
    assertThat(unsat).isPositive();
    assertThat(checked).isPositive();
  }

  private static long[] add(long[] a, long[] b) {
    for (int i = 0; i < a.length; i++) {
      a[i] += b[i];
    }
    return a;
  }
}
