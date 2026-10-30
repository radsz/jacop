/*
 * LinearRelaxationTest.java
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

package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.lcg.LcgSolver;
import org.jacop.lcg.LinearForm;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

/**
 * Tests the linear relaxation propagator against search without it on random small models of linear
 * constraints (with an alldiff now and then): it must keep every solution and the optimum, and
 * under lazy clause generation, with the explanation checker on, it must agree with depth-first
 * search. The number of models is set by {@code lp.test.runs} (default 1500).
 */
class LinearRelaxationTest {

  private static final int RUNS = Integer.getInteger("lp.test.runs", 1500);

  /** A random model; built again from the same seed for each solver. */
  private static final class Model {
    final Store store = new Store();
    final IntVar[] x;
    final List<LinearForm> rows = new ArrayList<>();
    IntVar objective;
    boolean maximize;
    LinearRelaxation.Simplex simplex = LinearRelaxation.Simplex.DENSE;

    Model(long seed) {
      this(seed, true);
    }

    // with linear false the rows are left to the relaxation alone
    Model(long seed, boolean linear) {
      Random rnd = new Random(seed);
      int n = 4 + rnd.nextInt(3);
      x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, -2 - rnd.nextInt(2), 2 + rnd.nextInt(3));
        if (rnd.nextInt(3) == 0) {
          x[i].domain.subtractAdapt(x[i].min() + 1 + rnd.nextInt(x[i].max() - x[i].min() - 1));
          x[i].refreshBounds();
        }
      }
      String[] relations = {"==", "<=", ">=", "<", ">", "!="};
      int m = 2 + rnd.nextInt(4);
      for (int r = 0; r < m; r++) {
        int k = 2 + rnd.nextInt(n - 1);
        List<IntVar> pool = new ArrayList<>(List.of(x));
        IntVar[] vars = new IntVar[k];
        int[] w = new int[k];
        long[] lw = new long[k];
        for (int i = 0; i < k; i++) {
          vars[i] = pool.remove(rnd.nextInt(pool.size()));
          w[i] = rnd.nextInt(9) - 4;
          if (w[i] == 0) {
            w[i] = 1;
          }
          lw[i] = w[i];
        }
        String rel = relations[rnd.nextInt(relations.length)];
        int c = rnd.nextInt(9) - 4;
        if (linear) {
          store.impose(new LinearInt(vars, w, rel, c));
        }
        int form =
            switch (rel) {
              case "==" -> LinearForm.EQ;
              case "<=", "<" -> LinearForm.LE;
              case ">=", ">" -> LinearForm.GE;
              default -> LinearForm.NE;
            };
        long rhs = rel.equals("<") ? c - 1 : rel.equals(">") ? c + 1 : c;
        rows.add(new LinearForm(vars, lw, rhs, form));
      }
      if (rnd.nextInt(4) == 0) {
        store.impose(new Alldiff(new IntVar[] {x[0], x[1], x[2]}));
      }
      if (rnd.nextBoolean()) {
        objective = new IntVar(store, "obj", -60, 60);
        IntVar[] vars = new IntVar[n + 1];
        int[] w = new int[n + 1];
        long[] lw = new long[n + 1];
        for (int i = 0; i < n; i++) {
          vars[i] = x[i];
          w[i] = rnd.nextInt(7) - 3;
          lw[i] = w[i];
        }
        vars[n] = objective;
        w[n] = -1;
        lw[n] = -1;
        if (linear) {
          store.impose(new LinearInt(vars, w, "==", 0));
        }
        rows.add(new LinearForm(vars, lw, 0, LinearForm.EQ));
        maximize = rnd.nextBoolean();
      }
    }

    LinearRelaxation relaxation() {
      LinearRelaxation r = new LinearRelaxation(rows, objective, maximize, simplex);
      store.impose(r);
      return r;
    }

    // the variable minimized: the objective, or its negation for maximization
    IntVar cost() {
      if (!maximize) {
        return objective;
      }
      IntVar negated = new IntVar(store, "neg", -60, 60);
      store.impose(new LinearInt(new IntVar[] {objective, negated}, new int[] {1, 1}, "==", 0));
      return negated;
    }
  }

  // the number of solutions of x, or 1 and the optimum, by depth-first search; Long.MIN_VALUE as
  // the second entry without a solution
  private static long[] search(Model model) {
    IntVar cost = model.objective == null ? null : model.cost();
    if (!model.store.consistency()) {
      return new long[] {0, Long.MIN_VALUE};
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    SimpleSelect<IntVar> select = new SimpleSelect<>(model.x, null, new IndomainMin<>());
    if (cost == null) {
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      search.labeling(model.store, select);
      int solutions = search.getSolutionListener().solutionsNo();
      return new long[] {solutions, solutions > 0 ? 0 : Long.MIN_VALUE};
    }
    boolean found = search.labeling(model.store, select, cost);
    return new long[] {found ? 1 : 0, found ? search.getCostValue() : Long.MIN_VALUE};
  }

  @ParameterizedTest
  @EnumSource(LinearRelaxation.Simplex.class)
  void keepsSolutionsAndOptima(LinearRelaxation.Simplex simplex) {
    long pruned = 0;
    long failures = 0;
    long cuts = 0;
    for (int run = 0; run < RUNS; run++) {
      long[] expected = search(new Model(run));
      Model model = new Model(run);
      model.simplex = simplex;
      LinearRelaxation r = model.relaxation();
      long[] actual = search(model);
      assertThat(actual).as("seed %d", run).isEqualTo(expected);
      pruned += r.prunings;
      failures += r.failures;
      cuts += r.cuts;
    }
    assertThat(pruned).isPositive();
    assertThat(failures).isPositive();
    assertThat(cuts).isPositive();
  }

  @Test
  void aloneAcceptsOnlyAssignmentsThatKeepTheRows() {
    for (int run = 0; run < RUNS / 5; run++) {
      Model model = new Model(run, false);
      model.relaxation();
      IntVar[] vars = model.x;
      if (model.objective != null) {
        vars = Arrays.copyOf(model.x, model.x.length + 1);
        vars[model.x.length] = model.objective;
      }
      List<String> broken = new ArrayList<>();
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.setSolutionListener(
          new SimpleSolutionListener<>() {
            @Override
            public boolean executeAfterSolution(
                Search<IntVar> s, SelectChoicePoint<IntVar> select) {
              for (LinearForm f : model.rows) {
                // rows with != are left out of the relaxation
                if (f.relation() != LinearForm.NE && !holds(f)) {
                  broken.add(f.toString());
                }
              }
              return super.executeAfterSolution(s, select);
            }
          });
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      if (model.store.consistency()) {
        search.labeling(model.store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
      }
      assertThat(broken).as("seed %d", run).isEmpty();
    }
  }

  private static boolean holds(LinearForm f) {
    long sum = 0;
    for (int k = 0; k < f.vars().length; k++) {
      sum += f.weights()[k] * f.vars()[k].value();
    }
    return switch (f.relation()) {
      case LinearForm.LE -> sum <= f.c();
      case LinearForm.GE -> sum >= f.c();
      default -> sum == f.c();
    };
  }

  /**
   * The relaxation's own pruning fixes every variable to an assignment that breaks a row; the
   * explanation checker, which copies the relaxation alone, found that assignment.
   */
  // seed 14768 under lazy clause generation, with the last row a cut the root found: the duals
  // made a combination with weights near 2^60, whose slack overflowed a long and failed a node with
  // a solution
  @Test
  void keepsASolutionWhenTheSlackOfACombinationOverflows() {
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", -3, 2);
    IntVar x1 = new IntVar(store, "x1", -3, 2);
    IntVar x2 = new IntVar(store, "x2", -2, 4);
    IntVar x3 = new IntVar(store, "x3", -3, 2);
    IntVar x4 = new IntVar(store, "x4", -3, -3);
    x4.addDom(-1, 2);
    IntVar x5 = new IntVar(store, "x5", -3, 1);
    x5.addDom(3, 4);
    IntVar obj = new IntVar(store, "obj", -25, 27);
    List<LinearForm> rows =
        List.of(
            new LinearForm(new IntVar[] {x1, x2, x5, x3}, new long[] {-3, 3, 4, 1}, 1, 1),
            new LinearForm(new IntVar[] {x5, x1, x2, x3}, new long[] {1, 1, 1, 2}, -1, 1),
            new LinearForm(
                new IntVar[] {x0, x1, x2, x3, x4, x5, obj},
                new long[] {0, 1, 1, -1, -3, -3, -1},
                0,
                2),
            new LinearForm(
                new IntVar[] {obj, x2, x4},
                new long[] {39254654638L, -78509047132L, 58881981957L},
                333665612999L,
                0));
    store.impose(new LinearRelaxation(rows, obj, true));
    assertThat(store.consistency()).isTrue();
    store.setLevel(1);
    obj.domain.in(1, obj, -7, -7);
    x2.domain.inMax(1, x2, 0);
    // x = (-3, -3, -2, 2, -3, 3), obj = -7 meets every row
    assertThat(store.consistency()).isTrue();
    assertThat(x2.min()).isLessThanOrEqualTo(-2);
  }

  // the rows of Max (m >= x_i) tie the objective to the linear constraint: the root bound is 12 / 3
  @Test
  void readsTheRowsOfConstraintsThatAreNotLinear() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 10);
    }
    IntVar m = new IntVar(store, "m", 0, 10);
    store.impose(new LinearInt(x, new int[] {1, 1, 1}, ">=", 13));
    store.impose(new org.jacop.constraints.Max(x, m));
    LinearRelaxation r = LinearRelaxation.of(store, m, false);
    assertThat(r).isNotNull();
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    assertThat(r.rootBound).isCloseTo(13.0 / 3, org.assertj.core.data.Offset.offset(1e-6));
    // the bound is rounded up by the propagation of the combination
    assertThat(m.min()).isEqualTo(5);
  }

  @Test
  void keepsEverySolutionWithOnlyRowsOfConstraintsThatAreNotLinear() {
    // no linear relation at all: the first solve has no row, and its size was a division by zero
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar c = new IntVar(store, "c", 0, 1);
    store.impose(new org.jacop.constraints.Reified(new org.jacop.constraints.XltC(x, 2), b));
    store.impose(new org.jacop.constraints.Reified(new org.jacop.constraints.XltY(x, y), c));
    LinearRelaxation r = LinearRelaxation.of(store, null, false);
    assertThat(r).isNotNull();
    assertThat(r.rows()).isZero();
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    org.jacop.search.DepthFirstSearch<IntVar> search = new org.jacop.search.DepthFirstSearch<>();
    org.jacop.search.SelectChoicePoint<IntVar> select =
        new org.jacop.search.InputOrderSelect<>(
            store, new IntVar[] {x, y, b, c}, new org.jacop.search.IndomainMin<>());
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setPrintInfo(false);
    assertThat(search.labeling(store, select)).isTrue();
    // b and c follow from x and y
    assertThat(search.getSolutionListener().solutionsNo()).isEqualTo(16);
  }

  @Test
  void rejectsAnAssignmentItsOwnPruningFixed() {
    lazyClauseGeneration(5_901_220L, new TreeMap<>(), LinearRelaxation.Simplex.DENSE);
  }

  @ParameterizedTest
  @EnumSource(LinearRelaxation.Simplex.class)
  void agreesWithSearchUnderLazyClauseGeneration(LinearRelaxation.Simplex simplex) {
    Map<String, long[]> statistics = new TreeMap<>();
    long checked = 0;
    for (int run = 0; run < RUNS; run++) {
      checked += lazyClauseGeneration(run, statistics, simplex);
    }
    long[] lp = statistics.get("LinearRelaxation");
    assertThat(lp).isNotNull();
    // reasons and failures explained by the relaxation's own inequalities
    assertThat(lp[0] - lp[1] + lp[3] - lp[4]).isPositive();
    assertThat(checked).isPositive();
  }

  // solves a model under lazy clause generation with the explanation checker on and compares with
  // depth-first search; returns the explanations checked
  private static long lazyClauseGeneration(
      long run, Map<String, long[]> statistics, LinearRelaxation.Simplex simplex) {
    {
      long[] expected = search(new Model(run));
      Model model = new Model(run);
      model.simplex = simplex;
      model.relaxation();
      IntVar cost = model.objective == null ? null : model.cost();
      LcgSolver solver = new LcgSolver(model.store);
      solver.setChecking(true);
      int status = cost == null ? solver.solve() : solver.minimize(cost);
      long checked = solver.checker().checked;
      assertThat(status).as("seed %d", run).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(status == CdclSolver.SAT).as("seed %d", run).isEqualTo(expected[0] > 0);
      if (cost != null && status == CdclSolver.SAT) {
        assertThat((long) solver.value(cost)).as("seed %d", run).isEqualTo(expected[1]);
      }
      solver
          .explanationStatistics()
          .forEach(
              (k, v) ->
                  statistics.merge(
                      k,
                      v.clone(),
                      (a, b) -> {
                        for (int i = 0; i < a.length; i++) {
                          a[i] += b[i];
                        }
                        return a;
                      }));
      return checked;
    }
  }

  /**
   * Long rows split into block sums, as lazy clause generation splits them, and clauses given as
   * extra rows: the relaxation substitutes the block sums back, so it has one row per original row
   * and clause, and alone with the blocks it keeps exactly the solutions of the model.
   */
  @Test
  void substitutesSplitSumsAndAddsExtraRows() {
    for (int run = 0; run < RUNS / 10; run++) {
      Random rnd = new Random(run);
      Store plain = new Store();
      Store split = new Store();
      IntVar[] x = new IntVar[6];
      IntVar[] y = new IntVar[6];
      for (int i = 0; i < 6; i++) {
        int min = -1 - rnd.nextInt(2);
        int max = 1 + rnd.nextInt(2);
        x[i] = new IntVar(plain, "x" + i, min, max);
        y[i] = new IntVar(split, "x" + i, min, max);
      }
      IntVar[] b = new IntVar[3];
      IntVar[] c = new IntVar[3];
      for (int i = 0; i < 3; i++) {
        b[i] = new IntVar(plain, "b" + i, 0, 1);
        c[i] = new IntVar(split, "b" + i, 0, 1);
      }
      List<IntVar> sums = new ArrayList<>();
      String[] relations = {"<=", ">=", "=="};
      int rows = 2 + rnd.nextInt(2);
      for (int r = 0; r < rows; r++) {
        List<Integer> pool = new ArrayList<>(List.of(0, 1, 2, 3, 4, 5));
        int k = 5 + rnd.nextInt(2);
        int[] at = new int[k];
        int[] w = new int[k];
        for (int i = 0; i < k; i++) {
          at[i] = pool.remove(rnd.nextInt(pool.size()));
          w[i] = rnd.nextBoolean() ? 1 + rnd.nextInt(3) : -1 - rnd.nextInt(3);
        }
        String rel = relations[rnd.nextInt(relations.length)];
        int rhs = rnd.nextInt(7) - 3;
        IntVar[] xs = new IntVar[k];
        for (int i = 0; i < k; i++) {
          xs[i] = x[at[i]];
        }
        plain.impose(new LinearInt(xs, w, rel, rhs));
        // blocks of two terms, each defining a sum, and the sum of the blocks
        List<IntVar> top = new ArrayList<>();
        for (int from = 0; from < k; from += 2) {
          int to = Math.min(k, from + 2);
          long min = 0;
          long max = 0;
          IntVar[] bv = new IntVar[to - from + 1];
          int[] bw = new int[to - from + 1];
          for (int i = from; i < to; i++) {
            IntVar v = y[at[i]];
            min += Math.min(w[i] * v.min(), w[i] * v.max());
            max += Math.max(w[i] * v.min(), w[i] * v.max());
            bv[i - from] = v;
            bw[i - from] = w[i];
          }
          IntVar sum = new IntVar(split, (int) min, (int) max);
          bv[to - from] = sum;
          bw[to - from] = -1;
          split.impose(new LinearInt(bv, bw, "==", 0));
          top.add(sum);
          sums.add(sum);
        }
        int[] ones = new int[top.size()];
        Arrays.fill(ones, 1);
        split.impose(new LinearInt(top.toArray(new IntVar[0]), ones, rel, rhs));
      }
      // clauses over the 0/1 variables and a sign of x0: in the plain store as constraints, for
      // the split one only as rows of the relaxation
      List<LinearForm> clauses = new ArrayList<>();
      int clauseCount = 1 + rnd.nextInt(2);
      for (int r = 0; r < clauseCount; r++) {
        int neg = rnd.nextInt(3);
        IntVar[] p = new IntVar[3 - neg];
        IntVar[] q = new IntVar[neg];
        IntVar[] pc = new IntVar[3 - neg];
        IntVar[] qc = new IntVar[neg];
        long[] cw = new long[3];
        IntVar[] cv = new IntVar[3];
        for (int i = 0; i < 3; i++) {
          if (i < 3 - neg) {
            p[i] = b[i];
            pc[i] = c[i];
            cw[i] = 1;
          } else {
            q[i - 3 + neg] = b[i];
            qc[i - 3 + neg] = c[i];
            cw[i] = -1;
          }
          cv[i] = c[i];
        }
        plain.impose(new BoolClause(p, q));
        clauses.add(new LinearForm(cv, cw, 1L - neg, LinearForm.GE));
      }
      LinearRelaxation r = LinearRelaxation.of(split, null, false, clauses, new HashSet<>(sums));
      assertThat(r).as("seed %d", run).isNotNull();
      assertThat(r.rows()).as("seed %d", run).isEqualTo(rows + clauseCount);
      split.impose(r);
      assertThat(solutions(split, y, c)).as("seed %d", run).isEqualTo(solutions(plain, x, b));
    }
  }

  // the number of solutions over the given variables
  private static int solutions(Store store, IntVar[] x, IntVar[] b) {
    if (!store.consistency()) {
      return 0;
    }
    IntVar[] vars = Arrays.copyOf(x, x.length + b.length);
    System.arraycopy(b, 0, vars, x.length, b.length);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
    return search.getSolutionListener().solutionsNo();
  }
}
