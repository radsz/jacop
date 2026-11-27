/*
 * RootExtendTest.java
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

import java.util.Arrays;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

/**
 * A root solve of an optimisation relaxation in the sparse simplex that stops at its pivot budget
 * goes on within a share of the time of a large relaxation, so that it still bounds the objective.
 * The models are coverings by windows, as the Drinking model of XCSP 2024: x[i] = 1 drinks at time
 * i, each of the forced times needs a drink in the 8 minutes up to it, and the drinks are
 * minimised. The pivot budget of the root solves is lowered to make it bind on these small models.
 */
class RootExtendTest {

  private static final int INSTANCES = Integer.getInteger("lp.rootExtend.instances", 10);

  private final int savedPivots = LinearRelaxation.rootPivots;
  private final double savedShare = LinearRelaxation.rootExtendShare;

  @AfterEach
  void restore() {
    LinearRelaxation.rootPivots = savedPivots;
    LinearRelaxation.rootExtendShare = savedShare;
  }

  /** A random covering of forced times by windows of 8 positions. */
  private static final class Model {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    Model(int seed) {
      Random rnd = new Random(seed * 17L + 5);
      int n = 40 + rnd.nextInt(30);
      x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new BooleanVar(store, "x" + i);
      }
      for (int t = 0; t < n; t++) {
        if (t % 5 == 0 || t % 7 == 0 || rnd.nextInt(10) == 0) {
          int from = Math.max(0, t - 7);
          IntVar[] w = Arrays.copyOfRange(x, from, t + 1);
          int[] ones = new int[w.length];
          Arrays.fill(ones, 1);
          store.impose(new LinearInt(w, ones, ">=", 1));
        }
      }
      cost = new IntVar(store, "cost", 0, n);
      IntVar[] all = Arrays.copyOf(x, n + 1);
      all[n] = cost;
      int[] w = new int[n + 1];
      Arrays.fill(w, 1);
      w[n] = -1;
      store.impose(new LinearInt(all, w, "==", 0));
    }

    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      InputOrderSelect<IntVar> order = new InputOrderSelect<>(store, x, new IndomainMin<>());
      return search.labeling(store, order, cost) ? search.getCostValue() : Long.MIN_VALUE;
    }
  }

  // the root bound of the relaxation of the model of the seed, after its root propagation
  private static double rootBound(int seed) {
    Model m = new Model(seed);
    LinearRelaxation r =
        LinearRelaxation.of(m.store, m.cost, false, LinearRelaxation.Simplex.SPARSE);
    assertThat(r).isNotNull();
    m.store.impose(r);
    assertThat(m.store.consistency()).isTrue();
    return r.rootBound;
  }

  @Test
  void rootSolveStoppedByItsPivotsGoesOn() {
    int stopped = 0;
    for (int run = 0; run < INSTANCES; run++) {
      double full = rootBound(run);
      assertThat(full).as("run %d", run).isPositive();
      LinearRelaxation.rootPivots = 5;
      LinearRelaxation.rootExtendShare = 0;
      double cut = rootBound(run);
      LinearRelaxation.rootExtendShare = savedShare;
      double extended = rootBound(run);
      LinearRelaxation.rootPivots = savedPivots;
      // without the extension the budget gives no bound; with it, the bound of the full solve
      stopped += Double.isNaN(cut) ? 1 : 0;
      assertThat(extended)
          .as("run %d", run)
          .isCloseTo(full, org.assertj.core.data.Offset.offset(1e-6));
    }
    assertThat(stopped).isEqualTo(INSTANCES);
  }

  @Test
  void extendedRootSolveKeepsTheOptimum() {
    for (int run = 0; run < INSTANCES; run++) {
      long expected = new Model(run).optimum();
      LinearRelaxation.rootPivots = 5;
      Model m = new Model(run);
      LinearRelaxation r =
          LinearRelaxation.of(m.store, m.cost, false, LinearRelaxation.Simplex.SPARSE);
      m.store.impose(r);
      long got = m.optimum();
      LinearRelaxation.rootPivots = savedPivots;
      assertThat(got).as("run %d", run).isEqualTo(expected);
      assertThat(r.rootBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
      assertThat(r.rootExtendNanos()).as("run %d", run).isPositive();
    }
  }

  // -Dorg.jacop.lp.rootPivots=0 or 1, below the least pivots of a root solve (5): the solves take
  // 5 (before: Math.clamp(n, 5, 0) threw, and every model with a linear relaxation stopped)
  @Test
  void rootPivotsBelowTheLeastKeepTheOptimum() {
    for (int pivots : new int[] {0, 1}) {
      for (int run = 0; run < INSTANCES; run++) {
        long expected = new Model(run).optimum();
        LinearRelaxation.rootPivots = pivots;
        Model m = new Model(run);
        LinearRelaxation r =
            LinearRelaxation.of(m.store, m.cost, false, LinearRelaxation.Simplex.SPARSE);
        m.store.impose(r);
        long got = m.optimum();
        LinearRelaxation.rootPivots = savedPivots;
        assertThat(got).as("pivots %d, run %d", pivots, run).isEqualTo(expected);
      }
    }
  }
}
