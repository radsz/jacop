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
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import org.jacop.constraints.Alldiff;
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
      LinearRelaxation r = new LinearRelaxation(rows, objective, maximize);
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

  @Test
  void keepsSolutionsAndOptima() {
    long pruned = 0;
    long failures = 0;
    for (int run = 0; run < RUNS; run++) {
      long[] expected = search(new Model(run));
      Model model = new Model(run);
      LinearRelaxation r = model.relaxation();
      long[] actual = search(model);
      assertThat(actual).as("seed %d", run).isEqualTo(expected);
      pruned += r.prunings;
      failures += r.failures;
    }
    assertThat(pruned).isPositive();
    assertThat(failures).isPositive();
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
  @Test
  void rejectsAnAssignmentItsOwnPruningFixed() {
    lazyClauseGeneration(5_901_220L, new TreeMap<>());
  }

  @Test
  void agreesWithSearchUnderLazyClauseGeneration() {
    Map<String, long[]> statistics = new TreeMap<>();
    long checked = 0;
    for (int run = 0; run < RUNS; run++) {
      checked += lazyClauseGeneration(run, statistics);
    }
    long[] lp = statistics.get("LinearRelaxation");
    assertThat(lp).isNotNull();
    // reasons and failures explained by the relaxation's own inequalities
    assertThat(lp[0] - lp[1] + lp[3] - lp[4]).isPositive();
    assertThat(checked).isPositive();
  }

  // solves a model under lazy clause generation with the explanation checker on and compares with
  // depth-first search; returns the explanations checked
  private static long lazyClauseGeneration(long run, Map<String, long[]> statistics) {
    {
      long[] expected = search(new Model(run));
      Model model = new Model(run);
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
}
