/*
 * LargeRelaxationTest.java
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
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.LpGuidedSelect;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

/**
 * Large relaxations, over the size caps of the sparse simplex in search: they are solved at the
 * root only and keep the optimum of random capacitated facility location models with incompatible
 * pairs of stores (the store x warehouse MIP form of the 2026 Challenge warehouse model), also when
 * the search follows their root solution. The size cap is lowered to make these small models large.
 */
class LargeRelaxationTest {

  private static final int INSTANCES = Integer.getInteger("lp.large.instances", 40);

  private final int savedCap = LinearRelaxation.sparseMaxRows;

  @AfterEach
  void restoreCap() {
    LinearRelaxation.sparseMaxRows = savedCap;
  }

  /** A random facility location model: x[i][j] goods of store i from warehouse j. */
  private static final class Model {
    final Store store = new Store();
    final List<IntVar> vars = new ArrayList<>();
    final IntVar cost;

    Model(int seed) {
      Random rnd = new Random(seed * 31L + 3);
      int w = 2 + rnd.nextInt(2);
      int s = 2 + rnd.nextInt(2);
      int[] goods = new int[s];
      int[] cap = new int[w];
      int total = 0;
      for (int i = 0; i < s; i++) {
        goods[i] = 1 + rnd.nextInt(3);
        total += goods[i];
      }
      for (int j = 0; j < w; j++) {
        cap[j] = 1 + total / w + rnd.nextInt(3);
      }
      IntVar[][] x = new IntVar[s][w];
      IntVar[][] z = new IntVar[s][w];
      IntVar[] y = new IntVar[w];
      List<IntVar> terms = new ArrayList<>();
      List<Integer> weights = new ArrayList<>();
      for (int j = 0; j < w; j++) {
        y[j] = new BooleanVar(store, "y" + j);
        terms.add(y[j]);
        weights.add(5 + rnd.nextInt(10));
      }
      for (int i = 0; i < s; i++) {
        for (int j = 0; j < w; j++) {
          x[i][j] = new IntVar(store, "x" + i + "_" + j, 0, goods[i]);
          z[i][j] = new BooleanVar(store, "z" + i + "_" + j);
          terms.add(x[i][j]);
          weights.add(1 + rnd.nextInt(6));
          // x <= goods z, z <= y
          store.impose(
              new LinearInt(new IntVar[] {x[i][j], z[i][j]}, new int[] {1, -goods[i]}, "<=", 0));
          store.impose(new LinearInt(new IntVar[] {z[i][j], y[j]}, new int[] {1, -1}, "<=", 0));
        }
        store.impose(new LinearInt(x[i], ones(w), "==", goods[i]));
      }
      for (int j = 0; j < w; j++) {
        IntVar[] col = new IntVar[s + 1];
        int[] cw = new int[s + 1];
        for (int i = 0; i < s; i++) {
          col[i] = x[i][j];
          cw[i] = 1;
        }
        col[s] = y[j];
        cw[s] = -cap[j];
        store.impose(new LinearInt(col, cw, "<=", 0));
        // the first two stores are incompatible
        store.impose(new LinearInt(new IntVar[] {z[0][j], z[1][j]}, new int[] {1, 1}, "<=", 1));
      }
      cost = new IntVar(store, "cost", 0, 10_000);
      terms.add(cost);
      weights.add(-1);
      store.impose(
          new LinearInt(
              terms.toArray(new IntVar[0]),
              weights.stream().mapToInt(Integer::intValue).toArray(),
              "==",
              0));
      for (int i = 0; i < s; i++) {
        for (int j = 0; j < w; j++) {
          vars.add(x[i][j]);
          vars.add(z[i][j]);
        }
      }
      vars.addAll(List.of(y));
    }

    private static int[] ones(int n) {
      int[] r = new int[n];
      java.util.Arrays.fill(r, 1);
      return r;
    }

    long optimum(LinearRelaxation guide) {
      InputOrderSelect<IntVar> order =
          new InputOrderSelect<>(store, vars.toArray(new IntVar[0]), new IndomainMin<>());
      if (guide == null) {
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        return search.labeling(store, order, cost) ? search.getCostValue() : Long.MIN_VALUE;
      }
      DepthFirstSearch<Var> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      return search.labeling(store, new LpGuidedSelect(guide, order), cost)
          ? search.getCostValue()
          : Long.MIN_VALUE;
    }
  }

  @Test
  void largeRelaxationKeepsTheOptimum() {
    int guided = 0;
    for (int run = 0; run < INSTANCES; run++) {
      long expected = new Model(run).optimum(null);
      LinearRelaxation.sparseMaxRows = 3;
      Model m = new Model(run);
      LinearRelaxation r = LinearRelaxation.of(m.store, m.cost, false);
      assertThat(r).as("run %d", run).isNotNull();
      assertThat(r.large()).as("run %d", run).isTrue();
      assertThat(r.largeByRows()).as("run %d", run).isTrue();
      m.store.impose(r);
      boolean guide = run % 2 == 1;
      long got = m.optimum(guide ? r : null);
      LinearRelaxation.sparseMaxRows = savedCap;
      assertThat(got).as("run %d", run).isEqualTo(expected);
      assertThat(r.rootBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
      // solved at the root only
      assertThat(r.calls).as("run %d", run).isLessThanOrEqualTo(1);
      guided += guide && r.solutionColumns() > 0 ? 1 : 0;
    }
    assertThat(guided).isPositive();
  }

  @Test
  void smallRelaxationIsNotLarge() {
    Model m = new Model(1);
    LinearRelaxation r = LinearRelaxation.of(m.store, m.cost, false);
    assertThat(r).isNotNull();
    assertThat(r.large()).isFalse();
  }
}
