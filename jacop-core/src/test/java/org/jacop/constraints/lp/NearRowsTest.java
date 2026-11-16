/*
 * NearRowsTest.java
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
import java.util.Set;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

/**
 * The rows over the terms of the objective that do not fit the dense tableau go to the sparse
 * simplex (CSPLib warehouses): a facility location model whose clauses {@code b[i][j] -> open[j]}
 * are rows outside the store, as lazy clause generation hands them over, and whose costs are
 * elements over the store's facility.
 */
class NearRowsTest {

  private final boolean saved = LinearRelaxation.nearRowsOn;

  @AfterEach
  void restore() {
    LinearRelaxation.nearRowsOn = saved;
  }

  // n stores and facilities, fixed cost f; the root bound of its relaxation, and the cost of the
  // best solution with one facility open (an upper bound of the optimum)
  private static double[] rootBound(int n, int f, int seed, boolean near) {
    LinearRelaxation.nearRowsOn = near;
    Random rnd = new Random(seed);
    Store store = new Store();
    int[][] c = new int[n][n];
    IntVar[] open = new IntVar[n];
    List<LinearForm> clauses = new ArrayList<>();
    IntVar[] terms = new IntVar[2 * n + 1];
    int[] weights = new int[2 * n + 1];
    for (int j = 0; j < n; j++) {
      open[j] = new BooleanVar(store, "open" + j);
      terms[j] = open[j];
      weights[j] = f;
    }
    for (int i = 0; i < n; i++) {
      IntVar supplier = new IntVar(store, "s" + i, 1, n);
      IntVar[] b = new IntVar[n];
      int max = 0;
      for (int j = 0; j < n; j++) {
        c[i][j] = 100 + rnd.nextInt(900);
        max = Math.max(max, c[i][j]);
        b[j] = new BooleanVar(store, "b" + i + "_" + j);
        clauses.add(
            new LinearForm(new IntVar[] {b[j], open[j]}, new long[] {1, -1}, 0, LinearForm.LE));
      }
      store.impose(new ChannelReif(supplier, b));
      IntVar cost = new IntVar(store, "c" + i, 0, max);
      store.impose(new ElementInteger(supplier, c[i], cost, 0));
      terms[n + i] = cost;
      weights[n + i] = 1;
    }
    IntVar total = new IntVar(store, "total", 0, 10_000_000);
    terms[2 * n] = total;
    weights[2 * n] = -1;
    store.impose(new LinearInt(terms, weights, "==", 0));
    assertThat(store.consistency()).isTrue();
    LinearRelaxation r =
        LinearRelaxation.of(store, total, false, clauses, Set.of(), LinearRelaxation.Simplex.DENSE);
    assertThat(r).isNotNull();
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    long single = Long.MAX_VALUE;
    for (int j = 0; j < n; j++) {
      long sum = f;
      for (int i = 0; i < n; i++) {
        sum += c[i][j];
      }
      single = Math.min(single, sum);
    }
    return new double[] {r.rootBound, single, r.nearRows};
  }

  @Test
  void rowsOverTheObjectiveTermsRaiseTheRootBound() {
    // 40 x 40: the 1,600 clause rows with the encodings do not fit the dense tableau
    for (int seed = 0; seed < 1; seed++) {
      double[] near = rootBound(40, 2_000, seed, true);
      double[] dense = rootBound(40, 2_000, seed, false);
      assertThat(near[2]).as("seed %d", seed).isPositive();
      assertThat(dense[2]).as("seed %d", seed).isZero();
      assertThat(near[0]).as("seed %d", seed).isGreaterThan(dense[0] + 1);
      assertThat(near[0]).as("seed %d", seed).isLessThanOrEqualTo(near[1]);
    }
  }
}
