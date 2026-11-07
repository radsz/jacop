/*
 * FlowSumsLcgTest.java
 * <p>
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

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.FlowSums;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Lazy clause generation with {@link FlowSums}: random small competitions (games of two or three
 * teams whose points add up to a range, team totals with points so far, a few dangling edges and
 * holes in the domains) and random row and column sums of small integer matrices, with a weighted
 * sum of the totals as objective, are solved with the explanation checker on and by depth-first
 * search, which must agree on satisfiability and the optimum. The constraint is posted alone in
 * half of the models, so its own reasons do all the work there, and with the sums in the other
 * half.
 *
 * <p>The number of models is set by {@code flowsums.lcg.runs} (default 1500).
 */
class FlowSumsLcgTest {

  private static final int RUNS = Integer.getInteger("flowsums.lcg.runs", 1500);

  private static final class Model {
    final Store store = new Store();
    final Random rnd;
    final List<IntVar> vars = new ArrayList<>();
    final List<IntVar> totals = new ArrayList<>();
    IntVar objective;

    Model(long seed, boolean reference) {
      rnd = new Random(seed);
      int nl = 2 + rnd.nextInt(4);
      int nr = 2 + rnd.nextInt(3);
      boolean games = rnd.nextBoolean();
      List<int[]> edges = new ArrayList<>();
      for (int i = 0; i < nl; i++) {
        if (games) {
          // a game between two or three teams
          int k = rnd.nextInt(5) == 0 && nr >= 3 ? 3 : 2;
          List<Integer> teams = new ArrayList<>();
          for (int j = 0; j < nr; j++) {
            teams.add(j);
          }
          java.util.Collections.shuffle(teams, rnd);
          for (int c = 0; c < k; c++) {
            edges.add(new int[] {i, teams.get(c)});
          }
        } else {
          for (int j = 0; j < nr; j++) {
            if (rnd.nextInt(3) > 0) {
              edges.add(new int[] {i, j});
            }
          }
        }
      }
      if (rnd.nextInt(4) == 0) {
        edges.add(new int[] {-1, rnd.nextInt(nr)});
      }
      if (rnd.nextInt(4) == 0) {
        edges.add(new int[] {rnd.nextInt(nl), -1});
      }
      int m = edges.size();
      IntVar[] x = new IntVar[m];
      int[] left = new int[m];
      int[] right = new int[m];
      int[] lsum = new int[nl];
      int[] rsum = new int[nr];
      for (int e = 0; e < m; e++) {
        if (games) {
          x[e] = var("p" + e, 0, 3);
          x[e].domain.subtractAdapt(2);
          x[e].refreshBounds();
        } else {
          x[e] = var("x" + e, 0, 1 + rnd.nextInt(2));
        }
        left[e] = edges.get(e)[0];
        right[e] = edges.get(e)[1];
        if (left[e] >= 0) {
          lsum[left[e]] += x[e].max();
        }
        if (right[e] >= 0) {
          rsum[right[e]] += x[e].max();
        }
      }
      FlowSums.Node[] l = new FlowSums.Node[nl];
      for (int i = 0; i < nl; i++) {
        if (games) {
          l[i] = FlowSums.Node.of(2, 3);
        } else if (rnd.nextBoolean()) {
          int a = rnd.nextInt(lsum[i] + 1);
          l[i] = FlowSums.Node.of(a, a + rnd.nextInt(2));
        } else {
          l[i] = FlowSums.Node.of(total("row" + i, 0, lsum[i]), 0);
        }
      }
      FlowSums.Node[] r = new FlowSums.Node[nr];
      for (int j = 0; j < nr; j++) {
        int base = games ? rnd.nextInt(4) : 0;
        if (!games && rnd.nextBoolean()) {
          int a = rnd.nextInt(rsum[j] + 1);
          r[j] = FlowSums.Node.of(a, a + rnd.nextInt(2));
        } else {
          int lo = base + rnd.nextInt(2);
          int hi = base + rsum[j] - rnd.nextInt(2);
          r[j] = FlowSums.Node.of(total("t" + j, lo, Math.max(lo, hi)), -base);
        }
      }
      boolean withSums = rnd.nextBoolean();
      if (reference) {
        decomposition(x, left, right, l, r);
      } else {
        store.impose(new FlowSums(x, left, right, l, r));
        if (withSums) {
          decomposition(x, left, right, l, r);
        }
      }
      // a side constraint: two totals apart
      if (totals.size() >= 2 && rnd.nextBoolean()) {
        store.impose(
            new LinearInt(new IntVar[] {totals.get(0), totals.get(1)}, new int[] {1, -1}, ">=", 1));
      }
      IntVar[] obj = totals.isEmpty() ? new IntVar[] {x[0]} : totals.toArray(IntVar[]::new);
      int[] w = new int[obj.length + 1];
      for (int k = 0; k < obj.length; k++) {
        w[k] = rnd.nextInt(5) - 2;
      }
      w[obj.length] = -1;
      objective = var("obj", -200, 200);
      IntVar[] terms = Arrays.copyOf(obj, obj.length + 1);
      terms[obj.length] = objective;
      store.impose(new LinearInt(terms, w, "==", 0));
    }

    private void decomposition(
        IntVar[] x, int[] left, int[] right, FlowSums.Node[] l, FlowSums.Node[] r) {
      for (int side = 0; side < 2; side++) {
        FlowSums.Node[] nodes = side == 0 ? l : r;
        int[] of = side == 0 ? left : right;
        for (int i = 0; i < nodes.length; i++) {
          List<IntVar> s = new ArrayList<>();
          for (int e = 0; e < x.length; e++) {
            if (of[e] == i) {
              s.add(x[e]);
            }
          }
          FlowSums.Node node = nodes[i];
          if (s.isEmpty()) {
            // a team without games keeps its points; a range of an empty row holds 0
            if (node.total() != null) {
              store.impose(new XeqC(node.total(), -node.offset()));
            }
            continue;
          }
          if (node.total() != null) {
            s.add(node.total());
          }
          IntVar[] t = s.toArray(IntVar[]::new);
          int[] c = new int[t.length];
          Arrays.fill(c, 1);
          if (node.total() != null) {
            c[t.length - 1] = -1;
            store.impose(new LinearInt(t, c, "==", node.offset()));
          } else {
            store.impose(new LinearInt(t, c, ">=", node.min()));
            store.impose(new LinearInt(t, c, "<=", node.max()));
          }
        }
      }
    }

    private IntVar total(String name, int min, int max) {
      IntVar v = var(name, min, max);
      totals.add(v);
      return v;
    }

    private IntVar var(String name, int min, int max) {
      IntVar v = new IntVar(store, name, min, max);
      vars.add(v);
      return v;
    }

    IntVar[] decisionVars() {
      return vars.toArray(IntVar[]::new);
    }
  }

  // the optimum by depth-first search over the sums, without the constraint
  private static Integer reference(long seed) {
    Model model = new Model(seed, true);
    if (!model.store.consistency()) {
      return null;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    boolean found =
        search.labeling(
            model.store,
            new SimpleSelect<>(model.decisionVars(), null, new IndomainMin<>()),
            model.objective);
    return found ? search.getCostValue() : null;
  }

  private static boolean extendsToSolution(long seed, int[] values) {
    Model model = new Model(seed, true);
    IntVar[] vars = model.decisionVars();
    for (int i = 0; i < vars.length; i++) {
      if (!vars[i].domain.contains(values[i])) {
        return false;
      }
      model.store.impose(new XeqC(vars[i], values[i]));
    }
    return model.store.consistency();
  }

  @Test
  void agreesWithSearch() {
    long own = 0;
    long generic = 0;
    int sat = 0;
    for (int run = 0; run < RUNS; run++) {
      long seed = 1 + run;
      Integer expected = reference(seed);
      Model model = new Model(seed, false);
      LcgSolver solver = new LcgSolver(model.store);
      solver.setChecking(true);
      int status = solver.minimize(model.objective);
      assertThat(status).as("seed %d", seed).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(status == CdclSolver.SAT)
          .as(
              "seed %d expected %s status %d store %s",
              seed, expected, status, new Model(seed, false).store)
          .isEqualTo(expected != null);
      if (status == CdclSolver.SAT) {
        sat++;
        assertThat(solver.value(model.objective)).as("seed %d", seed).isEqualTo(expected);
        IntVar[] vars = model.decisionVars();
        int[] values = new int[vars.length];
        for (int i = 0; i < vars.length; i++) {
          values[i] = solver.value(vars[i]);
        }
        assertThat(extendsToSolution(seed, values)).as("seed %d", seed).isTrue();
      }
      long[] s = solver.explanationStatistics().get("FlowSums");
      if (s != null) {
        own += s[0] - s[1] - s[6] + s[3] - s[4] - s[7];
        generic += s[1] + s[6] + s[4] + s[7];
      }
    }
    System.out.printf(
        "flow sums lcg: %d runs, %d sat, %d own reasons, %d generic or replayed%n",
        RUNS, sat, own, generic);
    assertThat(sat).isPositive();
    assertThat(own).isPositive();
  }
}
