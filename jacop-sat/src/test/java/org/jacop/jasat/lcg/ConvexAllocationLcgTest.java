/*
 * ConvexAllocationLcgTest.java
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
import java.util.List;
import java.util.Random;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.ConvexAllocation;
import org.jacop.constraints.ConvexCost;
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
 * Lazy clause generation with {@link ConvexAllocation}: random balancing models (one or two
 * allocations with random convex costs, a variable or fixed total, side constraints, the cost as
 * objective) are solved with the explanation checker on and by depth-first search, which must agree
 * on satisfiability and the optimum. Most explanations then come from the constraint's own
 * Lagrangian reasons, which the checker verifies one by one.
 *
 * <p>The number of models is set by {@code convex.lcg.runs} (default 1500).
 */
class ConvexAllocationLcgTest {

  private static final int RUNS = Integer.getInteger("convex.lcg.runs", 1500);

  private static final class Model {
    final Store store = new Store();
    final Random rnd;
    final List<IntVar> vars = new ArrayList<>();
    IntVar objective;

    Model(long seed) {
      rnd = new Random(seed);
      int n = 3 + rnd.nextInt(4);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = var("x" + i, -1 + rnd.nextInt(2), 3 + rnd.nextInt(3));
        if (rnd.nextInt(3) == 0) {
          x[i].domain.subtractAdapt(x[i].min() + 1);
          x[i].refreshBounds();
        }
      }
      IntVar[] costs = new IntVar[1 + rnd.nextInt(2)];
      for (int k = 0; k < costs.length; k++) {
        int m = Math.min(n, 2 + rnd.nextInt(n));
        IntVar[] p = new IntVar[m];
        List<IntVar> pool = new ArrayList<>(List.of(x));
        for (int i = 0; i < m; i++) {
          p[i] = pool.remove(rnd.nextInt(pool.size()));
        }
        ConvexCost[] f = new ConvexCost[m];
        for (int i = 0; i < m; i++) {
          f[i] = cost();
        }
        IntVar total =
            rnd.nextBoolean() ? var("t" + k, m, m) : var("t" + k, rnd.nextInt(m + 1), m + 3 * m);
        costs[k] = var("c" + k, 0, 200);
        ConvexAllocation a = new ConvexAllocation(p, f, total, costs[k]);
        a.lagrangianOnly(rnd.nextInt(4) == 0);
        store.impose(a);
      }
      if (rnd.nextBoolean()) {
        store.impose(new Alldistinct(new IntVar[] {x[0], x[1], x[2]}));
      }
      if (rnd.nextBoolean()) {
        store.impose(
            new LinearInt(new IntVar[] {x[0], x[n - 1]}, new int[] {1, -1}, ">=", rnd.nextInt(3)));
      }
      if (costs.length == 1) {
        objective = costs[0];
      } else {
        objective = var("obj", 0, 400);
        store.impose(
            new LinearInt(
                new IntVar[] {costs[0], costs[1], objective}, new int[] {1, 1, -1}, "==", 0));
      }
    }

    private ConvexCost cost() {
      long w = 1 + rnd.nextInt(3);
      long c = rnd.nextInt(5) - 1;
      return switch (rnd.nextInt(5)) {
        case 0 -> ConvexCost.abs(w, 1 + rnd.nextInt(2), -c);
        case 1 -> ConvexCost.square(w, 1, -c);
        case 2 -> ConvexCost.squaredMax(w, new long[] {1, -1}, new long[] {-c, c - rnd.nextInt(2)});
        case 3 -> ConvexCost.max(w, new long[] {1, -1, 0}, new long[] {-c - 1, c, 0});
        default -> ConvexCost.linear(rnd.nextInt(5) - 2, 0).plus(ConvexCost.square(1, 1, -c));
      };
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

  private static Integer reference(Model model) {
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
    Model model = new Model(seed);
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
      Integer expected = reference(new Model(seed));
      Model model = new Model(seed);
      LcgSolver solver = new LcgSolver(model.store);
      solver.setChecking(true);
      int status = solver.minimize(model.objective);
      assertThat(status).as("seed %d", seed).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(status == CdclSolver.SAT).as("seed %d", seed).isEqualTo(expected != null);
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
      long[] s = solver.explanationStatistics().get("ConvexAllocation");
      if (s != null) {
        own += s[0] - s[1] - s[6] + s[3] - s[4] - s[7];
        generic += s[1] + s[6] + s[4] + s[7];
      }
    }
    System.out.printf(
        "convex allocation lcg: %d runs, %d sat, %d own reasons, %d generic or replayed%n",
        RUNS, sat, own, generic);
    assertThat(sat).isPositive();
    assertThat(own).isPositive();
  }
}
