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
import static org.assertj.core.api.Assertions.offset;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import org.jacop.api.VarMap;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Count;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.GCC;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Linearizations;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Routes;
import org.jacop.constraints.TableCliques;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.Table;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.lcg.LcgSolver;
import org.jacop.lcg.LinearForm;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.LpGuidedSelect;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
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

  /**
   * Restarts: each solution found tightens the bound of the cost at the root level, where the
   * relaxation propagates its root reduced costs and solves again with new cut rounds; whatever it
   * deduces there must keep the optimum.
   */
  @ParameterizedTest
  @EnumSource(LinearRelaxation.Simplex.class)
  void keepsTheOptimumOverRestarts(LinearRelaxation.Simplex simplex) {
    boolean was = LinearRelaxation.restartSolvesOn;
    try {
      LinearRelaxation.restartSolvesOn = false;
      assertThat(restarts(simplex)[1]).isPositive();
      LinearRelaxation.restartSolvesOn = true;
      long[] counts = restarts(simplex);
      assertThat(counts[0]).isPositive();
      assertThat(counts[1]).isPositive();
    } finally {
      LinearRelaxation.restartSolvesOn = was;
    }
  }

  // solves each model with restarts after each solution; returns the restart solves and the root
  // reduced-cost prunings
  private static long[] restarts(LinearRelaxation.Simplex simplex) {
    long restarts = 0;
    long rootPruned = 0;
    for (int run = 0; run < RUNS; run++) {
      long[] expected = search(new Model(run));
      Model model = new Model(run);
      if (model.objective == null) {
        continue;
      }
      model.simplex = simplex;
      LinearRelaxation r = model.relaxation();
      IntVar cost = model.cost();
      IntVar[] vars = Arrays.copyOf(model.x, model.x.length + 1);
      vars[model.x.length] = cost;
      long best = Long.MIN_VALUE;
      while (model.store.consistency()) {
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        search.setAssignSolution(false);
        search.getSolutionListener().recordSolutions(true);
        if (!search.labeling(model.store, new SimpleSelect<>(vars, null, new IndomainMin<>()))) {
          break;
        }
        best = search.getSolution()[model.x.length].valueEnumeration().nextElement();
        if (best == cost.min()) {
          break;
        }
        // a restart: the bound of the cost tightens at the root level
        cost.domain.inMax(model.store.level, cost, (int) best - 1);
      }
      assertThat(new long[] {best == Long.MIN_VALUE ? 0 : 1, best})
          .as("seed %d", run)
          .isEqualTo(expected);
      restarts += r.restartSolves;
      rootPruned += r.rootPrunings;
    }
    return new long[] {restarts, rootPruned};
  }

  @Test
  void gomoryCutsOverTheSlacksKeepTheOptimum() {
    int stronger = 0;
    int weaker = 0;
    for (int run = 0; run < RUNS; run++) {
      Model probe = new Model(run);
      if (probe.objective == null) {
        continue;
      }
      long[] expected = search(probe);
      if (expected[0] == 0) {
        continue;
      }
      double[] bound = new double[2];
      for (int k = 0; k < 2; k++) {
        Model model = new Model(run);
        LinearRelaxation r = new LinearRelaxation(model.rows, model.objective, model.maximize);
        r.setSlackGomory(k == 1);
        model.store.impose(r);
        if (!model.store.consistency()) {
          bound[k] = Double.NaN;
          continue;
        }
        bound[k] = r.cutBound;
        // the optimum of the cost minimized: the objective, or its negation
        double optimum = model.maximize ? -expected[1] : expected[1];
        if (!Double.isNaN(bound[k])) {
          assertThat(model.maximize ? bound[k] : bound[k])
              .as("seed %d slack %b", run, k == 1)
              .satisfies(
                  b ->
                      assertThat(model.maximize ? b >= optimum - 1e-6 : b <= optimum + 1e-6)
                          .as("bound %s optimum %s", b, optimum)
                          .isTrue());
        }
      }
      if (!Double.isNaN(bound[0]) && !Double.isNaN(bound[1])) {
        double gain = probe.maximize ? bound[0] - bound[1] : bound[1] - bound[0];
        stronger += gain > 1e-6 ? 1 : 0;
        weaker += gain < -1e-6 ? 1 : 0;
      }
    }
    assertThat(stronger).as("stronger %d weaker %d", stronger, weaker).isGreaterThan(weaker);
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

  /**
   * The dense simplex is asked for, but a relaxation of 100 rows or more is solved by the sparse
   * one, and so is one over the dense size cap, which before got no relaxation at all
   * (roster-shifts-bool, physician-scheduling and table-layout of the Challenge had no LP).
   */
  @Test
  void choosesTheSparseSimplexForLargeRelaxations() {
    assertThat(chain(5).simplex()).isEqualTo(LinearRelaxation.Simplex.DENSE);
    assertThat(chain(150).simplex()).isEqualTo(LinearRelaxation.Simplex.SPARSE);
    // 2,000 rows over 2,001 columns: a dense tableau of 8 million entries, over its cap of 4
    LinearRelaxation large = chain(2000);
    assertThat(large).isNotNull();
    assertThat(large.simplex()).isEqualTo(LinearRelaxation.Simplex.SPARSE);
    assertThat(large.rows()).isEqualTo(2000);
  }

  /**
   * The sparse relaxation over the dense cap proves the bound: x_i + x_(i+1) >= 1 sums to 1,000.
   */
  @Test
  void boundsTheObjectiveOverTheDenseCap() {
    Store store = new Store();
    int n = 2000;
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    for (int i = 0; i + 1 < n; i += 2) {
      store.impose(new LinearInt(new IntVar[] {x[i], x[i + 1]}, new int[] {1, 1}, ">=", 1));
    }
    IntVar cost = new IntVar(store, "cost", 0, n);
    IntVar[] all = Arrays.copyOf(x, n + 1);
    all[n] = cost;
    int[] w = new int[n + 1];
    Arrays.fill(w, 1);
    w[n] = -1;
    store.impose(new LinearInt(all, w, "==", 0));
    LinearRelaxation r = LinearRelaxation.of(store, cost, false);
    assertThat(r).isNotNull();
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    assertThat(cost.min()).isEqualTo(n / 2);
  }

  // shifts that overlap pairwise: the pair rows x_i + x_j <= 1 allow half of each set of shifts
  // that
  // share a time in the LP, the clique rows of those sets 1 (the graph of intervals is perfect, so
  // the bound is the optimum); some pairs are stated over a fixed variable, x_i + x_j - one <= 0,
  // and some over a negated literal, x_i - y <= 0 with y = 1 - x_j
  @Test
  void mergesThePairsOfConflictingShiftsIntoCliques() {
    int[][] shifts = {{0, 4}, {1, 5}, {2, 6}, {3, 8}, {5, 9}, {6, 10}, {7, 12}, {9, 13}, {11, 14}};
    int[] value = {3, 2, 4, 5, 2, 3, 4, 2, 3};
    Store store = new Store();
    int n = shifts.length;
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    IntVar one = new IntVar(store, "one", 1, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    store.impose(new LinearInt(new IntVar[] {x[8], y}, new int[] {1, 1}, "==", 1));
    int pairs = 0;
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (shifts[i][0] < shifts[j][1] && shifts[j][0] < shifts[i][1]) {
          IntVar[] row;
          int[] w;
          int side;
          if (j == 8) {
            row = new IntVar[] {x[i], y};
            w = new int[] {1, -1};
            side = 0;
          } else if (pairs % 2 == 0) {
            row = new IntVar[] {x[i], x[j], one};
            w = new int[] {1, 1, -1};
            side = 0;
          } else {
            row = new IntVar[] {x[i], x[j]};
            w = new int[] {1, 1};
            side = 1;
          }
          store.impose(new LinearInt(row, w, "<=", side));
          pairs++;
        }
      }
    }
    IntVar cost = new IntVar(store, "cost", 0, 100);
    IntVar[] all = Arrays.copyOf(x, n + 1);
    all[n] = cost;
    int[] w = Arrays.copyOf(value, n + 1);
    w[n] = -1;
    store.impose(new LinearInt(all, w, "==", 0));
    // the optimum, by enumeration
    int best = 0;
    for (int mask = 0; mask < 1 << n; mask++) {
      boolean ok = true;
      int sum = 0;
      for (int i = 0; i < n && ok; i++) {
        if ((mask >> i & 1) == 1) {
          sum += value[i];
          for (int j = i + 1; j < n; j++) {
            if ((mask >> j & 1) == 1
                && shifts[i][0] < shifts[j][1]
                && shifts[j][0] < shifts[i][1]) {
              ok = false;
            }
          }
        }
      }
      if (ok) {
        best = Math.max(best, sum);
      }
    }
    LinearRelaxation r = LinearRelaxation.of(store, cost, true);
    assertThat(r).isNotNull();
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    assertThat(cost.max()).isEqualTo(best);
  }

  // rows x_i + x_(i+1) <= 3 over a chain of m + 1 variables
  private static LinearRelaxation chain(int m) {
    Store store = new Store();
    IntVar[] x = new IntVar[m + 1];
    for (int i = 0; i <= m; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 2);
    }
    for (int i = 0; i < m; i++) {
      store.impose(new LinearInt(new IntVar[] {x[i], x[i + 1]}, new int[] {1, 1}, "<=", 3));
    }
    return LinearRelaxation.of(store, x[0], true);
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
      // the clauses are added at the first solve
      assertThat(r.rows()).as("seed %d", run).isEqualTo(rows);
      split.impose(r);
      assertThat(solutions(split, y, c)).as("seed %d", run).isEqualTo(solutions(plain, x, b));
    }
  }

  /**
   * Many extra rows that do not change the root bound are not kept: on rel2onto under lazy clause
   * generation the clauses made 1,135 rows of a relaxation that had 65, and the large relaxation
   * stalled at its pivot limit and pruned nothing.
   */
  @Test
  void dropsManyExtraRowsThatDoNotHelp() {
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 5);
    }
    IntVar cost = new IntVar(store, "cost", 0, 30);
    store.impose(
        new LinearInt(
            new IntVar[] {x[0], x[1], x[2], x[3], cost}, new int[] {1, 1, 1, 1, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {x[0], x[1]}, new int[] {1, 1}, ">=", 3));
    // clauses over Booleans that the objective does not depend on
    List<LinearForm> clauses = new ArrayList<>();
    IntVar[] b = new IntVar[40];
    for (int i = 0; i < b.length; i++) {
      b[i] = new IntVar(store, "b" + i, 0, 1);
    }
    for (int i = 0; i < 150; i++) {
      IntVar[] v = {b[i % b.length], b[(i * 7 + 1) % b.length]};
      clauses.add(new LinearForm(v, new long[] {1, 1}, 1, LinearForm.GE));
    }
    LinearRelaxation r = LinearRelaxation.of(store, cost, false, clauses, Set.of());
    assertThat(r).isNotNull();
    assertThat(r.rows()).isEqualTo(2);
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    assertThat(cost.min()).isEqualTo(3);
    assertThat(r.rows()).isEqualTo(2);
  }

  /**
   * A copy keeps the extra rows its original kept. The copy decided again at its own first solve,
   * and over other domains (the LCG checker copies over the reason of a pruning) the same rows no
   * longer raised the bound and were dropped: the pruning the original had found with them looked
   * unsound (p1f/15 under --lcg -f, "wrong explanation ... by LinearRelaxation").
   */
  @Test
  void copyKeepsTheExtraRowsItsOriginalKept() {
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 5);
    }
    IntVar cost = new IntVar(store, "cost", 0, 30);
    IntVar[] row = {x[0], x[1], x[2], x[3], cost};
    store.impose(new LinearInt(row, new int[] {1, 1, 1, 1, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {x[0], x[1]}, new int[] {1, 1}, ">=", 3));
    // more extra rows than are kept for being few: one raises the bound, the rest do not
    List<LinearForm> extra = new ArrayList<>();
    extra.add(new LinearForm(x, new long[] {1, 1, 1, 1}, 12, LinearForm.GE));
    IntVar[] b = new IntVar[40];
    for (int i = 0; i < b.length; i++) {
      b[i] = new IntVar(store, "b" + i, 0, 1);
    }
    for (int i = 0; i < 150; i++) {
      IntVar[] v = {b[i % b.length], b[(i * 7 + 1) % b.length]};
      extra.add(new LinearForm(v, new long[] {1, 1}, 1, LinearForm.GE));
    }
    LinearRelaxation r = LinearRelaxation.of(store, cost, false, extra, Set.of());
    assertThat(r).isNotNull();
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    assertThat(cost.min()).isEqualTo(12);
    int rows = r.rows();
    assertThat(rows).isEqualTo(2 + extra.size());

    // a copy over domains on which the extra rows do not raise the bound
    Store other = new Store();
    Map<Var, Var> copies = new HashMap<>();
    for (IntVar v : x) {
      copies.put(v, new IntVar(other, v.id(), 3, 3));
    }
    copies.put(cost, new IntVar(other, "cost", 0, 30));
    for (IntVar v : b) {
      copies.put(v, new IntVar(other, v.id(), 0, 1));
    }
    LinearRelaxation copy =
        r.copy(
            new VarMap() {
              @Override
              public Store target() {
                return other;
              }

              @Override
              @SuppressWarnings("unchecked")
              public <V extends Var> V get(V v) {
                return (V) copies.get(v);
              }
            });
    other.impose(copy);
    assertThat(other.consistency()).isTrue();
    assertThat(copy.rows()).isEqualTo(rows);
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

  @Test
  void lpGuidedSelectFollowsTheFractionalSolution() {
    // three 0/1 variables that conflict pairwise, maximize their sum: the relaxation sets each to
    // 1/2, so the selection takes one of them and rounds it up
    Store store = new Store();
    IntVar[] b = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      b[i] = new IntVar(store, "b" + i, 0, 1);
    }
    for (int i = 0; i < 3; i++) {
      store.impose(new LinearInt(new IntVar[] {b[i], b[(i + 1) % 3]}, new int[] {1, 1}, "<=", 1));
    }
    IntVar sum = new IntVar(store, "sum", 0, 3);
    store.impose(
        new LinearInt(new IntVar[] {b[0], b[1], b[2], sum}, new int[] {1, 1, 1, -1}, "==", 0));
    LinearRelaxation lp = LinearRelaxation.of(store, sum, true);
    store.impose(lp);
    LpGuidedSelect select = new LpGuidedSelect(lp, null);
    assertThat(select.getChoiceVariable(0)).isNull();
    assertThat(store.consistency()).isTrue();
    assertThat(sum.max()).isEqualTo(1);
    Var v = select.getChoiceVariable(0);
    assertThat(v).isIn((Object[]) b);
    assertThat(select.getChoiceValue()).isEqualTo(1);
    assertThat(select.lpDecisions).isEqualTo(1);
  }

  /**
   * A random capacitated concert hall model: offers in halls or declined (hall 0), offers that
   * overlap at the start of one of them in different halls (all-different except 0), a Boolean per
   * accepted offer, and the total price of the accepted offers maximized.
   */
  private static final class Halls {
    final Store store = new Store();
    final IntVar[] assign;
    final IntVar objective;
    final IntVar cost;

    Halls(long seed) {
      Random rnd = new Random(seed);
      int n = 5 + rnd.nextInt(3);
      int halls = 2 + rnd.nextInt(2);
      int[] start = new int[n];
      int[] end = new int[n];
      assign = new IntVar[n];
      IntVar[] accepted = new IntVar[n];
      int[] price = new int[n + 1];
      for (int o = 0; o < n; o++) {
        start[o] = rnd.nextInt(6);
        end[o] = start[o] + 1 + rnd.nextInt(4);
        // the halls large enough for the offer: the largest ones
        int smallest = 1 + rnd.nextInt(halls);
        assign[o] = new IntVar(store, "a" + o, 0, 0);
        assign[o].addDom(smallest, halls);
        accepted[o] = new IntVar(store, "b" + o, 0, 1);
        price[o] = 1 + rnd.nextInt(20);
        if (rnd.nextBoolean()) {
          store.impose(new Reified(new XgteqC(assign[o], 1), accepted[o]));
        } else {
          store.impose(new Reified(new XlteqC(assign[o], 0), accepted[o]));
          price[o] = -price[o];
        }
      }
      for (int o = 0; o < n; o++) {
        List<IntVar> clique = new ArrayList<>();
        for (int p = 0; p < n; p++) {
          if (start[p] <= start[o] && start[o] < end[p]) {
            clique.add(assign[p]);
          }
        }
        if (clique.size() >= 2) {
          store.impose(new AlldifferentExceptZero(clique.toArray(new IntVar[0])));
        }
      }
      objective = new IntVar(store, "obj", -200, 200);
      IntVar[] vars = Arrays.copyOf(accepted, n + 1);
      vars[n] = objective;
      price[n] = -1;
      store.impose(new LinearInt(vars, price, "==", 0));
      cost = new IntVar(store, "cost", -200, 200);
      store.impose(new LinearInt(new IntVar[] {objective, cost}, new int[] {1, 1}, "==", 0));
    }

    // the most objective by depth-first search
    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      assertThat(
              search.labeling(store, new SimpleSelect<>(assign, null, new IndomainMin<>()), cost))
          .isTrue();
      return -search.getCostValue();
    }
  }

  /**
   * The value encodings of all-different-except over LP-only columns (concert-hall-cap): the
   * relaxation of hall assignments has them, keeps the optimum under depth-first search and under
   * lazy clause generation with the explanation checker on, and its root bound is often far below
   * that of the model's own rows.
   */
  @Test
  void valueColumnsKeepTheOptimumOfHallAssignments() {
    int tighter = 0;
    long checked = 0;
    for (int run = 0; run < RUNS / 5; run++) {
      long expected = new Halls(run).optimum();

      Halls dfs = new Halls(run);
      LinearRelaxation r = LinearRelaxation.of(dfs.store, dfs.objective, true);
      assertThat(r).as("seed %d", run).isNotNull();
      dfs.store.impose(r);
      assertThat(r.valueColumns).as("seed %d", run).isPositive();
      assertThat(dfs.optimum()).as("seed %d", run).isEqualTo(expected);
      assertThat(r.rootBound).as("seed %d", run).isGreaterThanOrEqualTo(expected - 1e-6);
      tighter += r.rootBound < r.baseBound - 0.5 ? 1 : 0;

      Halls lcg = new Halls(run);
      LinearRelaxation l = LinearRelaxation.of(lcg.store, lcg.objective, true);
      lcg.store.impose(l);
      LcgSolver solver = new LcgSolver(lcg.store);
      solver.setChecking(true);
      assertThat(solver.minimize(lcg.cost)).as("seed %d", run).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(lcg.objective)).as("seed %d", run).isEqualTo(expected);
      checked += solver.checker().checked;
    }
    assertThat(tighter).isGreaterThan(RUNS / 50);
    assertThat(checked).isPositive();
  }

  /**
   * A random assignment model: tasks get distinct values ({@link Alldiff}, {@link Alldistinct} or a
   * {@link GCC} with counters of at most 1), each task pays the cost of its value ({@link
   * ElementInteger} or {@link ElementIntegerFast}), some value is taken a given number of times
   * ({@link Count}), and the total cost is minimized.
   */
  private static final class Assignment {
    final Store store = new Store();
    final IntVar[] x;
    final List<IntVar> searched = new ArrayList<>();
    final IntVar cost;

    Assignment(long seed) {
      Random rnd = new Random(seed);
      int n = 3 + rnd.nextInt(3);
      int m = n + rnd.nextInt(2);
      x = new IntVar[n];
      IntVar[] c = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 1, m);
        searched.add(x[i]);
        int[] costs = new int[m];
        for (int v = 0; v < m; v++) {
          costs[v] = rnd.nextInt(20);
        }
        c[i] = new IntVar(store, "c" + i, 0, 20);
        store.impose(
            rnd.nextBoolean()
                ? new ElementInteger(x[i], costs, c[i], 0)
                : new ElementIntegerFast(x[i], costs, c[i], 0));
      }
      switch (rnd.nextInt(3)) {
        case 0 -> store.impose(new Alldiff(x));
        case 1 -> store.impose(new Alldistinct(x));
        default -> {
          IntVar[] counters = new IntVar[m];
          for (int v = 0; v < m; v++) {
            counters[v] = new IntVar(store, "n" + v, 0, 1);
          }
          store.impose(new GCC(x, counters));
        }
      }
      if (rnd.nextBoolean()) {
        IntVar[] y = new IntVar[n];
        for (int i = 0; i < n; i++) {
          y[i] = new IntVar(store, "y" + i, 1, 3);
          store.impose(new XneqY(y[i], x[i]));
          searched.add(y[i]);
        }
        store.impose(new Count(y, new IntVar(store, "k", 1, 1 + rnd.nextInt(n - 1)), 2));
      }
      cost = new IntVar(store, "cost", 0, 20 * n);
      int[] ones = new int[n + 1];
      Arrays.fill(ones, 1);
      ones[n] = -1;
      IntVar[] vars = Arrays.copyOf(c, n + 1);
      vars[n] = cost;
      store.impose(new LinearInt(vars, ones, "==", 0));
    }

    // the least cost by depth-first search
    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      IntVar[] all = searched.toArray(new IntVar[0]);
      assertThat(search.labeling(store, new SimpleSelect<>(all, null, new IndomainMin<>()), cost))
          .isTrue();
      return search.getCostValue();
    }
  }

  /**
   * The value encodings of counting, all-different and element constraints over LP-only columns:
   * the relaxation of random assignment models has them, keeps the optimum under depth-first search
   * and under lazy clause generation with the explanation checker on, and its root bound is often
   * above that of the model's own rows.
   */
  @Test
  void valueEncodingsKeepTheOptimumOfAssignments() {
    int tighter = 0;
    long checked = 0;
    for (int run = 0; run < RUNS / 5; run++) {
      long expected = new Assignment(run).optimum();

      Assignment dfs = new Assignment(run);
      LinearRelaxation r = LinearRelaxation.of(dfs.store, dfs.cost, false);
      assertThat(r).as("seed %d", run).isNotNull();
      dfs.store.impose(r);
      assertThat(r.valueColumns).as("seed %d", run).isPositive();
      assertThat(dfs.optimum()).as("seed %d", run).isEqualTo(expected);
      assertThat(r.rootBound).as("seed %d", run).isLessThanOrEqualTo(expected + 1e-6);
      tighter += r.extraRows > 0 && r.rootBound > r.baseBound + 0.5 ? 1 : 0;

      Assignment lcg = new Assignment(run);
      LinearRelaxation l = LinearRelaxation.of(lcg.store, lcg.cost, false);
      lcg.store.impose(l);
      LcgSolver solver = new LcgSolver(lcg.store);
      solver.setChecking(true);
      assertThat(solver.minimize(lcg.cost)).as("seed %d", run).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(lcg.cost)).as("seed %d", run).isEqualTo(expected);
      checked += solver.checker().checked;
    }
    assertThat(tighter).isGreaterThan(RUNS / 50);
    assertThat(checked).isPositive();
  }

  /**
   * Every task is cheapest at value 1: the bounds of the costs give 4, the assignment polytope of
   * the value encodings gives the optimum 31, which the root propagation sets as the bound.
   */
  @Test
  void valueEncodingsBoundAnAssignmentByItsOptimum() {
    Store store = new Store();
    int n = 4;
    IntVar[] x = new IntVar[n];
    IntVar[] vars = new IntVar[n + 1];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 1, n);
      vars[i] = new IntVar(store, "c" + i, 0, 10);
      store.impose(new ElementInteger(x[i], new int[] {1, 10, 10, 10}, vars[i], 0));
    }
    store.impose(new Alldiff(x));
    IntVar cost = new IntVar(store, "cost", 0, 100);
    vars[n] = cost;
    store.impose(new LinearInt(vars, new int[] {1, 1, 1, 1, -1}, "==", 0));
    LinearRelaxation r = LinearRelaxation.of(store, cost, false);
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    assertThat(r.baseBound).isEqualTo(4.0);
    assertThat(cost.min()).isEqualTo(31);
  }

  /**
   * On a relaxation with value columns the LP-guided selection decides store variables only: a
   * value column [x = v] becomes the decision x = v, never a decision on the column, and the value
   * is in the domain. The selection that follows the root solution decides the same at the root.
   */
  @Test
  void lpGuidedSelectDecidesTheValuesOfValueColumns() {
    int halls = 0;
    for (int run = 0; run < RUNS / 5; run++) {
      Halls h = new Halls(run);
      LinearRelaxation r = LinearRelaxation.of(h.store, h.objective, true);
      h.store.impose(r);
      LpGuidedSelect last = new LpGuidedSelect(r, null);
      LpGuidedSelect root = new LpGuidedSelect(r, null, true);
      assertThat(root.getChoiceVariable(0)).isNull(); // no solution yet
      assertThat(h.store.consistency()).as("seed %d", run).isTrue();
      assertThat(r.rootSolutionColumns()).as("seed %d", run).isEqualTo(r.solutionColumns());
      for (LpGuidedSelect select : List.of(last, root)) {
        Var v = select.getChoiceVariable(0);
        if (v == null) {
          continue;
        }
        assertThat(v).as("seed %d", run).isNotInstanceOf(LpColumn.class);
        IntVar x = (IntVar) v;
        assertThat(x.singleton()).as("seed %d", run).isFalse();
        assertThat(x.domain.contains(select.getChoiceValue())).as("seed %d", run).isTrue();
        halls += Arrays.asList(h.assign).contains(x) && select.getChoiceValue() > 0 ? 1 : 0;
      }
    }
    // the decision is often a hall for an offer, from a value column
    assertThat(halls).isPositive();
  }

  /**
   * Following the root solution, the selection decides only when the relaxation has value columns
   * and its root solution is near integral on them: on 0/1 columns alone it gives no decision,
   * where the last solution decides. Seat-moving 2021 sm-10-13-00, whose root solution had none of
   * its value columns, took twice as long with activity runs started from its 0/1 columns.
   */
  @Test
  void rootGuideNeedsValueColumns() {
    Store store = new Store();
    IntVar[] b = new IntVar[3];
    for (int i = 0; i < b.length; i++) {
      b[i] = new IntVar(store, "b" + i, 0, 1);
    }
    IntVar z = new IntVar(store, "z", 0, 10);
    store.impose(new LinearInt(b, new int[] {1, 1, 1}, "==", 1));
    store.impose(
        new LinearInt(new IntVar[] {b[0], b[1], b[2], z}, new int[] {2, 3, 5, -1}, "==", 0));
    LinearRelaxation r = LinearRelaxation.of(store, z, false);
    store.impose(r);
    LpGuidedSelect last = new LpGuidedSelect(r, null);
    LpGuidedSelect root = new LpGuidedSelect(r, null, true);
    assertThat(store.consistency()).isTrue();
    assertThat(r.rootSolutionColumns()).isPositive();
    assertThat(last.getChoiceVariable(0)).isSameAs(b[0]);
    assertThat(last.getChoiceValue()).isEqualTo(1);
    assertThat(root.getChoiceVariable(0)).isNull();
  }

  /**
   * Fixed search with restarts whose activity runs start from the relaxation's root solution keeps
   * the optimum of hall assignments, with the explanation checker on. Most of these models are
   * solved before the first activity run; the guide's decisions are checked on the selection above.
   */
  @Test
  void activityRunsGuidedByTheRelaxationKeepTheOptimum() {
    for (int run = 0; run < RUNS / 5; run++) {
      long expected = new Halls(run).optimum();
      Halls h = new Halls(run);
      LinearRelaxation l = LinearRelaxation.of(h.store, h.objective, true);
      h.store.impose(l);
      LcgSolver solver = new LcgSolver(h.store);
      solver.setChecking(true);
      solver.setAnnotation(new SimpleSelect<>(h.assign, null, new IndomainMin<>()), false);
      solver.setFixedRestarts(LcgSolver.FixedRestarts.TURNS, false);
      solver.setActivityGuide(new LpGuidedSelect(l, null, true));
      assertThat(solver.minimize(h.cost)).as("seed %d", run).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(h.objective)).as("seed %d", run).isEqualTo(expected);
    }
  }

  /**
   * The flow model of a layered graph (Regular over random, possibly non-deterministic automata, or
   * ExtensionalSupportMdd over random tables) makes the root bound of a linear cost over its
   * variables the optimum, since the flow polytope of a layered graph is integral; the optimum is
   * kept under depth-first search and under lazy clause generation with the explanation checker on,
   * which also checks the facts behind the bounds of the arc columns.
   */
  @Test
  void flowEncodingsBoundLayeredGraphsByTheirOptimum() {
    int raised = 0;
    int models = 0;
    long checked = 0;
    for (int run = 0; run < RUNS / 10; run++) {
      Long expected = new Paths(run).optimum();
      if (expected == null) {
        continue;
      }
      models++;
      Paths dfs = new Paths(run);
      LinearRelaxation r = LinearRelaxation.of(dfs.store, dfs.cost, false);
      assertThat(r).as("seed %d", run).isNotNull();
      dfs.store.impose(r);
      assertThat(dfs.optimum()).as("seed %d", run).isEqualTo(expected);
      assertThat(r.rootBound).as("seed %d", run).isCloseTo(expected, offset(1e-6));
      raised += r.extraRows > 0 && r.rootBound > r.baseBound + 0.5 ? 1 : 0;

      Paths lcg = new Paths(run);
      LinearRelaxation l = LinearRelaxation.of(lcg.store, lcg.cost, false);
      lcg.store.impose(l);
      LcgSolver solver = new LcgSolver(lcg.store);
      solver.setChecking(true);
      assertThat(solver.minimize(lcg.cost)).as("seed %d", run).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(lcg.cost)).as("seed %d", run).isEqualTo(expected);
      checked += solver.checker().checked;
    }
    assertThat(models).isGreaterThan(RUNS / 40);
    assertThat(raised).isGreaterThan(RUNS / 100);
    assertThat(checked).isPositive();
  }

  /**
   * The convex hulls of tables over tuple columns, with the rows that tie a conjunction of their
   * values to the tuples, bound a linear cost of the table variables and a reward for the
   * conjunction by its optimum: a table over three variables without a key, an element table with
   * its index as the key, and z = [x0 = a] and [x1 = b]. The LCG search finds the same optimum with
   * every explanation checked.
   */
  @Test
  void tableHullsBoundTablesByTheirOptimum() {
    int raised = 0;
    int models = 0;
    long checked = 0;
    for (int run = 0; run < RUNS / 10; run++) {
      Long expected = new Hulls(run).optimum();
      if (expected == null) {
        continue;
      }
      models++;
      Hulls dfs = new Hulls(run);
      LinearRelaxation r = dfs.relaxation();
      assertThat(r).as("seed %d", run).isNotNull();
      dfs.store.impose(r);
      assertThat(dfs.optimum()).as("seed %d", run).isEqualTo(expected);
      assertThat(r.rootBound).as("seed %d", run).isCloseTo(expected, offset(1e-6));
      raised += r.extraRows > 0 && r.rootBound > r.baseBound + 0.5 ? 1 : 0;

      Hulls lcg = new Hulls(run);
      lcg.store.impose(lcg.relaxation());
      LcgSolver solver = new LcgSolver(lcg.store);
      solver.setChecking(true);
      assertThat(solver.minimize(lcg.cost)).as("seed %d", run).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(lcg.cost)).as("seed %d", run).isEqualTo(expected);
      checked += solver.checker().checked;
    }
    assertThat(models).isGreaterThan(RUNS / 40);
    assertThat(raised).isGreaterThan(RUNS / 100);
    assertThat(checked).isPositive();
  }

  // two tables, a conjunction of two values of the first and a linear cost
  private static final class Hulls {
    final Store store = new Store();
    final IntVar[] x = new IntVar[3];
    final IntVar y;
    final IntVar index;
    final IntVar z;
    final IntVar cost;
    final List<TableCliques.Table> tables = new ArrayList<>();

    Hulls(long seed) {
      Random rnd = new Random(seed);
      for (int i = 0; i < 2; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 3);
      }
      // a result with a large domain, so that only its value is tied to the tuples
      x[2] = new IntVar(store, "x2", 0, 100);
      int[][] t = new int[2 + rnd.nextInt(8)][3];
      for (int[] tuple : t) {
        tuple[0] = rnd.nextInt(4);
        tuple[1] = rnd.nextInt(4);
        tuple[2] = 5 * rnd.nextInt(21);
      }
      store.impose(new Table(x, t));
      tables.add(new TableCliques.Table(x, t));
      // y = a[index], merged with index into a table as the element table detector does
      index = new IntVar(store, "index", 0, 3);
      y = new IntVar(store, "y", 0, 100);
      int[][] e = new int[4][];
      for (int v = 0; v < 4; v++) {
        e[v] = new int[] {v, 5 * rnd.nextInt(21)};
      }
      IntVar[] ey = {index, y};
      store.impose(new Table(ey, e));
      tables.add(new TableCliques.Table(ey, e));
      IntVar b0 = new IntVar(store, "b0", 0, 1);
      IntVar b1 = new IntVar(store, "b1", 0, 1);
      store.impose(new Reified(new XeqC(x[0], rnd.nextInt(4)), b0));
      store.impose(new Reified(new XeqC(x[1], rnd.nextInt(4)), b1));
      z = new IntVar(store, "z", 0, 1);
      store.impose(new AndBoolSimple(b0, b1, z));
      // cost = w0 x0 + w1 x1 + x2 + y - reward z, the reward making z as large as the LP allows
      int[] w = {rnd.nextInt(11) - 5, rnd.nextInt(11) - 5, 1, 1, -(1 + rnd.nextInt(60)), -1};
      cost = new IntVar(store, "cost", -100, 300);

      store.impose(new LinearInt(new IntVar[] {x[0], x[1], x[2], y, z, cost}, w, "==", 0));
    }

    LinearRelaxation relaxation() {
      TableCliques.Result rows = TableCliques.rows(tables);
      return LinearRelaxation.of(
          store, cost, false, List.of(), rows.all(), Set.of(), LinearRelaxation.Simplex.DENSE);
    }

    // the least cost by depth-first search, null when there is no solution
    Long optimum() {
      if (!store.consistency()) {
        return null;
      }
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      IntVar[] vars = {x[0], x[1], x[2], index, y, z};
      if (!search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()), cost)) {
        return null;
      }
      return (long) search.getCostValue();
    }
  }

  /**
   * The columns of the simplex, which decide the auto LP guide of the flatzinc front end, are the
   * relaxation's columns before the first solve, and leave out the columns of the tried encodings
   * the root trial dropped: on gbac UD8 the guide over such columns found 342 instead of 89.
   */
  @Test
  void simplexValueColumnsLeaveOutDroppedEncodings() {
    // the all-different encoding does not raise the bound 1 of min x0: dropped
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 3);
    }
    store.impose(new Alldiff(x));
    IntVar cost = new IntVar(store, "cost", 0, 10);
    store.impose(new LinearInt(new IntVar[] {x[0], cost}, new int[] {1, -1}, "==", 0));
    LinearRelaxation plain = LinearRelaxation.of(store, cost, false);
    assertThat(plain).isNotNull();
    assertThat(plain.valueColumns).isPositive();
    store.impose(plain);
    assertThat(plain.simplexValueColumns()).isEqualTo(plain.valueColumns);
    assertThat(store.consistency()).isTrue();
    assertThat(plain.simplexValueColumns()).isZero();

    int kept = 0;
    for (int run = 0; run < RUNS / 5; run++) {
      Assignment a = new Assignment(run);
      LinearRelaxation r = LinearRelaxation.of(a.store, a.cost, false);
      assertThat(r).as("seed %d", run).isNotNull();
      assertThat(r.valueColumns).as("seed %d", run).isPositive();
      a.store.impose(r);
      assertThat(r.simplexValueColumns()).as("seed %d", run).isEqualTo(r.valueColumns);
      if (!a.store.consistency()) {
        continue;
      }
      int inSimplex = r.simplexValueColumns();
      assertThat(inSimplex).as("seed %d", run).isBetween(0, r.valueColumns);
      kept += inSimplex > 0 ? 1 : 0;
    }
    assertThat(kept).isPositive();
  }

  /** Without an objective the counting, all-different and element encodings are not made. */
  @Test
  void satisfactionModelsGetNoTriedValueEncodings() {
    Assignment a = new Assignment(3);
    LinearRelaxation withCost = LinearRelaxation.of(a.store, a.cost, false);
    assertThat(withCost.valueColumns).isPositive();
    LinearRelaxation without = LinearRelaxation.of(new Assignment(3).store, null, false);
    assertThat(without == null || without.valueColumns == 0).isTrue();
  }

  // a linear cost over the variables of a Regular or an ExtensionalSupportMdd
  private static final class Paths {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    Paths(long seed) {
      Random rnd = new Random(seed);
      int n = 3 + rnd.nextInt(4);
      x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 3);
      }
      if (rnd.nextBoolean()) {
        int states = 2 + rnd.nextInt(4);
        FsmState[] s = new FsmState[states];
        Fsm fsm = new Fsm();
        for (int q = 0; q < states; q++) {
          s[q] = new FsmState();
          fsm.allStates.add(s[q]);
        }
        fsm.initState = s[0];
        for (int q = 0; q < states; q++) {
          if (rnd.nextInt(3) > 0) {
            fsm.finalStates.add(s[q]);
          }
          boolean[][] has = new boolean[4][states];
          for (int t = rnd.nextInt(2 * states + 3); t > 0; t--) {
            int c = rnd.nextInt(4);
            int next = rnd.nextInt(states);
            if (!has[c][next]) {
              has[c][next] = true;
              s[q].addTransition(new FsmTransition(new IntervalDomain(c, c), s[next]));
            }
          }
        }
        store.impose(new Regular(fsm, x));
      } else {
        int[][] table = new int[1 + rnd.nextInt(12)][n];
        for (int[] t : table) {
          for (int i = 0; i < n; i++) {
            t[i] = rnd.nextInt(4);
          }
        }
        store.impose(new ExtensionalSupportMdd(x, table));
      }
      int[] w = new int[n + 1];
      int lo = 0;
      int hi = 0;
      for (int i = 0; i < n; i++) {
        w[i] = rnd.nextInt(11) - 5;
        lo += Math.min(0, 3 * w[i]);
        hi += Math.max(0, 3 * w[i]);
      }
      w[n] = -1;
      cost = new IntVar(store, "cost", lo, hi);
      IntVar[] vars = Arrays.copyOf(x, n + 1);
      vars[n] = cost;
      store.impose(new LinearInt(vars, w, "==", 0));
    }

    // the least cost by depth-first search, null when there is no solution
    Long optimum() {
      if (!store.consistency()) {
        return null;
      }
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      if (!search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()), cost)) {
        return null;
      }
      return (long) search.getCostValue();
    }
  }

  /** A copy of a relaxation with LP-only columns gets its own columns over the copied variables. */
  @Test
  void copyMakesItsOwnValueColumns() {
    Halls h = new Halls(3);
    LinearRelaxation r = LinearRelaxation.of(h.store, h.objective, true);
    h.store.impose(r);
    assertThat(h.store.consistency()).isTrue();
    Store target = new Store();
    Map<Var, Var> copies = new HashMap<>();
    VarMap map =
        new VarMap() {
          @Override
          public Store target() {
            return target;
          }

          @Override
          @SuppressWarnings("unchecked")
          public <V extends Var> V get(V v) {
            return (V)
                copies.computeIfAbsent(
                    v, u -> new IntVar(target, u.id(), ((IntVar) u).dom().cloneLight()));
          }
        };
    LinearRelaxation c = r.copy(map);
    assertThat(c.valueColumns).isEqualTo(r.valueColumns);
    for (int j = 0; j < c.columns(); j++) {
      IntVar v = c.column(j);
      if (v instanceof LpColumn lc) {
        assertThat(copies).containsValue(lc.variable());
      } else {
        assertThat(copies).containsValue(v);
      }
    }
  }

  /**
   * The sorting-network rows and the Hall cuts of all-different constraints keep the optimum of
   * random permutation and assignment models under lazy clause generation with the explanation
   * checker on: the free columns of the network leave every explanation at their fixed bounds.
   */
  @Test
  void alldifferentRowsKeepTheOptimumUnderLcg() {
    long checked = 0;
    int used = 0;
    for (int run = 0; run < 16; run++) {
      boolean permutation = run % 2 == 0;
      long expected = new Permutation(run, permutation).optimum();

      Permutation lcg = new Permutation(run, permutation);
      LinearRelaxation l =
          LinearRelaxation.of(
              lcg.store,
              lcg.cost,
              false,
              List.of(),
              permutation ? Linearizations.alldifferentNetwork(lcg.x) : List.of(),
              Set.of(),
              LinearRelaxation.Simplex.DENSE);
      assertThat(l).as("seed %d", run).isNotNull();
      lcg.store.impose(l);
      LcgSolver solver = new LcgSolver(lcg.store);
      solver.setChecking(true);
      assertThat(solver.minimize(lcg.cost)).as("seed %d", run).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(lcg.cost)).as("seed %d", run).isEqualTo(expected);
      checked += solver.checker().checked;
      used += l.alldiffCuts > 0 || l.simplexFreeColumns() > 0 ? 1 : 0;
    }
    assertThat(checked).isPositive();
    assertThat(used).isPositive();
  }

  /**
   * A random all-different over 5 to 7 variables, a permutation of spread values or domains from a
   * larger pool, with a linear cost {@code cost = sum c_i x_i}.
   */
  private static final class Permutation {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    Permutation(int seed, boolean permutation) {
      Random rnd = new Random(seed * 104_729L + 1);
      int n = 5 + rnd.nextInt(3);
      int size = permutation ? n : n + 2;
      int[] values = new int[size];
      for (int i = 0, at = rnd.nextInt(4); i < size; i++) {
        at += 1 + rnd.nextInt(3);
        values[i] = at;
      }
      x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntervalDomain d = new IntervalDomain();
        for (int v : values) {
          if (permutation || rnd.nextInt(4) > 0) {
            d.unionAdapt(v, v);
          }
        }
        if (d.isEmpty()) {
          d.unionAdapt(values[i], values[i]);
        }
        x[i] = new IntVar(store, "x" + i, d);
      }
      int[] w = new int[n + 1];
      IntVar[] vars = Arrays.copyOf(x, n + 1);
      int range = 0;
      for (int i = 0; i < n; i++) {
        w[i] = rnd.nextInt(19) - 9;
        range += Math.abs(w[i]) * values[size - 1];
      }
      cost = new IntVar(store, "cost", -range, range);
      vars[n] = cost;
      w[n] = -1;
      store.impose(new LinearInt(vars, w, "==", 0));
      store.impose(new Alldistinct(x));
    }

    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      assertThat(search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()), cost))
          .isTrue();
      return search.getCostValue();
    }
  }

  /**
   * The rounded capacity cuts of a Routes raise the root bound of random capacitated vehicle
   * routing models (the degree rows alone give a weak bound), and keep the optimum under
   * depth-first search and under lazy clause generation with the explanation checker on.
   */
  @Test
  void capacityCutsKeepTheOptimumOfVehicleRouting() {
    int raised = 0;
    long checked = 0;
    long searched = 0;
    for (int run = 0; run < 12; run++) {
      long expected = new Cvrp(run).optimum();

      Cvrp dfs = new Cvrp(run);
      LinearRelaxation r = LinearRelaxation.of(dfs.store, dfs.cost, false);
      assertThat(r).as("seed %d", run).isNotNull();
      dfs.store.impose(r);
      assertThat(dfs.optimum()).as("seed %d", run).isEqualTo(expected);
      assertThat(r.cutBound).as("seed %d", run).isLessThanOrEqualTo(expected + 1e-6);
      raised += r.capacityCuts > 0 && r.capacityBound > r.rootBound + 0.5 ? 1 : 0;

      Cvrp lcg = new Cvrp(run);
      LinearRelaxation l = LinearRelaxation.of(lcg.store, lcg.cost, false);
      lcg.store.impose(l);
      LcgSolver solver = new LcgSolver(lcg.store);
      solver.setChecking(true);
      assertThat(solver.minimize(lcg.cost)).as("seed %d", run).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(lcg.cost)).as("seed %d", run).isEqualTo(expected);
      checked += solver.checker().checked;
      searched += r.capacitySearchCuts + l.capacitySearchCuts;
    }
    assertThat(searched).as("capacity cuts made in search").isPositive();
    assertThat(raised).isGreaterThan(3);
    assertThat(checked).isPositive();
  }

  /**
   * A random capacitated vehicle routing model: customers in the plane with demands, an arc between
   * every two nodes, one arc out of and one into each customer as linear rows, a Routes with the
   * demands and the capacity, and the length of the arcs used minimized.
   */
  private static final class Cvrp {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    Cvrp(long seed) {
      Random rnd = new Random(seed);
      int n = 6 + rnd.nextInt(2);
      int[] px = new int[n];
      int[] py = new int[n];
      int[] demands = new int[n];
      for (int v = 0; v < n; v++) {
        px[v] = rnd.nextInt(20);
        py[v] = rnd.nextInt(20);
        demands[v] = v == 0 ? 0 : 1 + rnd.nextInt(4);
      }
      int capacity = 5 + rnd.nextInt(3);
      int m = n * (n - 1);
      int[] tails = new int[m];
      int[] heads = new int[m];
      int[] length = new int[m + 1];
      x = new IntVar[m];
      int a = 0;
      for (int t = 0; t < n; t++) {
        for (int h = 0; h < n; h++) {
          if (t != h) {
            tails[a] = t;
            heads[a] = h;
            length[a] = (int) Math.round(Math.hypot(px[t] - px[h], py[t] - py[h]));
            x[a] = new IntVar(store, "x" + t + "_" + h, 0, 1);
            a++;
          }
        }
      }
      for (int v = 1; v < n; v++) {
        List<IntVar> out = new ArrayList<>();
        List<IntVar> in = new ArrayList<>();
        for (int k = 0; k < m; k++) {
          if (tails[k] == v) {
            out.add(x[k]);
          }
          if (heads[k] == v) {
            in.add(x[k]);
          }
        }
        int[] ones = new int[n - 1];
        Arrays.fill(ones, 1);
        store.impose(new LinearInt(out.toArray(new IntVar[0]), ones, "==", 1));
        store.impose(new LinearInt(in.toArray(new IntVar[0]), ones, "==", 1));
      }
      Routes r = new Routes(tails, heads, x, demands, capacity);
      r.setDegrees(false);
      store.impose(r);
      cost = new IntVar(store, "cost", 0, 2000);
      IntVar[] vars = Arrays.copyOf(x, m + 1);
      vars[m] = cost;
      length[m] = -1;
      store.impose(new LinearInt(vars, length, "==", 0));
    }

    // the least cost by depth-first search
    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      assertThat(search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()), cost))
          .isTrue();
      return search.getCostValue();
    }
  }

  /**
   * The energy cuts of a cumulative resource raise the root bound of random total completion time
   * models with release dates (the rows alone give the sum of the release dates and durations), and
   * keep the optimum under depth-first search and under lazy clause generation with the explanation
   * checker on.
   */
  @Test
  void energyCutsKeepTheOptimumOfScheduling() {
    int raised = 0;
    long checked = 0;
    for (int run = 0; run < 12; run++) {
      long expected = new Completion(run).optimum();

      Completion dfs = new Completion(run);
      LinearRelaxation r = LinearRelaxation.of(dfs.store, dfs.cost, false);
      assertThat(r).as("seed %d", run).isNotNull();
      dfs.store.impose(r);
      assertThat(dfs.optimum()).as("seed %d", run).isEqualTo(expected);
      assertThat(r.capacityBound).as("seed %d", run).isLessThanOrEqualTo(expected + 1e-6);
      raised += r.energyCuts > 0 && r.capacityBound > r.rootBound + 0.5 ? 1 : 0;

      Completion lcg = new Completion(run);
      LinearRelaxation l = LinearRelaxation.of(lcg.store, lcg.cost, false);
      lcg.store.impose(l);
      LcgSolver solver = new LcgSolver(lcg.store);
      solver.setChecking(true);
      assertThat(solver.minimize(lcg.cost)).as("seed %d", run).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(lcg.cost)).as("seed %d", run).isEqualTo(expected);
      checked += solver.checker().checked;
    }
    assertThat(raised).isGreaterThan(3);
    assertThat(checked).isPositive();
  }

  /**
   * A random scheduling model: tasks with release dates, durations and usages on one cumulative
   * resource, and the sum of their completion times, a linear row, minimized.
   */
  private static final class Completion {
    final Store store = new Store();
    final IntVar[] s;
    final IntVar cost;

    Completion(long seed) {
      Random rnd = new Random(seed);
      int n = 5 + rnd.nextInt(2);
      int cap = 1 + rnd.nextInt(2);
      s = new IntVar[n];
      IntVar[] d = new IntVar[n];
      IntVar[] u = new IntVar[n];
      int[] w = new int[n + 1];
      for (int j = 0; j < n; j++) {
        int p = 1 + rnd.nextInt(4);
        s[j] = new IntVar(store, "s" + j, rnd.nextInt(4), 30);
        d[j] = new IntVar(store, "d" + j, p, p);
        int use = 1 + rnd.nextInt(cap);
        u[j] = new IntVar(store, "u" + j, use, use);
        w[j] = 1;
      }
      store.impose(new Cumulative(s, d, u, new IntVar(store, "cap", cap, cap)));
      // the completion times, rows of their own, and their sum
      IntVar[] vars = new IntVar[n + 1];
      for (int j = 0; j < n; j++) {
        vars[j] = new IntVar(store, "c" + j, 0, 40);
        store.impose(
            new LinearInt(new IntVar[] {vars[j], s[j]}, new int[] {1, -1}, "==", d[j].value()));
      }
      cost = new IntVar(store, "cost", 0, 1000);
      vars[n] = cost;
      w[n] = -1;
      store.impose(new LinearInt(vars, w, "==", 0));
    }

    // the least cost by depth-first search
    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      assertThat(search.labeling(store, new SimpleSelect<>(s, null, new IndomainMin<>()), cost))
          .isTrue();
      return search.getCostValue();
    }
  }

  @Test
  void candidatesNearestTheObjectiveComeFirst() {
    // obj = x + y; a chain y - z <= 0, z - w <= 0 and an unconnected row u - v <= 0
    Store store = new Store();
    IntVar obj = new IntVar(store, "obj", 0, 20);
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", 0, 10);
    IntVar z = new IntVar(store, "z", 0, 10);
    IntVar w = new IntVar(store, "w", 0, 10);
    IntVar u = new IntVar(store, "u", 0, 10);
    IntVar v = new IntVar(store, "v", 0, 10);
    LinearForm def =
        new LinearForm(new IntVar[] {x, y, obj}, new long[] {1, 1, -1}, 0, LinearForm.EQ);
    LinearForm far = new LinearForm(new IntVar[] {u, v}, new long[] {1, -1}, 0, LinearForm.LE);
    LinearForm two = new LinearForm(new IntVar[] {z, w}, new long[] {1, -1}, 0, LinearForm.LE);
    LinearForm one = new LinearForm(new IntVar[] {y, z}, new long[] {1, -1}, 0, LinearForm.LE);
    assertThat(LinearRelaxation.byDistance(List.of(def), List.of(far, two, one), obj))
        .containsExactly(one, two, far);
  }

  @Test
  void triedValueEncodingsStayAfterTheOtherRowsWhenNotAllFit() {
    // the retry without the value encodings takes the extra rows before them: an encoding over
    // the objective must not be sorted before a plain row far from it
    Store store = new Store();
    IntVar obj = new IntVar(store, "obj", 0, 20);
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", 0, 10);
    IntVar u = new IntVar(store, "u", 0, 10);
    IntVar v = new IntVar(store, "v", 0, 10);
    IntVar e = new IntVar(store, "e", 0, 10);
    LinearForm def =
        new LinearForm(new IntVar[] {x, y, obj}, new long[] {1, 1, -1}, 0, LinearForm.EQ);
    LinearForm kept = new LinearForm(new IntVar[] {e, x}, new long[] {1, -1}, 0, LinearForm.LE);
    LinearForm far = new LinearForm(new IntVar[] {u, v}, new long[] {1, -1}, 0, LinearForm.LE);
    LinearForm near = new LinearForm(new IntVar[] {x, y}, new long[] {1, -1}, 0, LinearForm.LE);
    LinearForm encoding =
        new LinearForm(new IntVar[] {obj, x}, new long[] {1, -1}, 0, LinearForm.GE);
    Set<LinearForm> tried = Collections.newSetFromMap(new IdentityHashMap<>());
    tried.add(encoding);
    assertThat(
            LinearRelaxation.fitOrder(
                List.of(def), List.of(kept, encoding, far, near), 1, tried, obj))
        .containsExactly(kept, near, far, encoding);
  }
}
