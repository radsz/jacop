/*
 * AssignmentEncodingTest.java
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

import java.util.List;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

/**
 * The value encodings of a generalized assignment model (OR-Library gap: job j goes to agent
 * agent[j], {@code b[i][j] <-> agent[j] = i}, capacity rows over the b, cost {@code cost[i][j]} by
 * element) are the rows of its LP: each job has one agent and its cost is {@code sum cost[i][j]
 * b[i][j]}. Without them the root bound is the sum of the cheapest costs.
 */
class AssignmentEncodingTest {

  private final boolean saved = LinearRelaxation.encodingRowsOn;

  @AfterEach
  void restore() {
    LinearRelaxation.encodingRowsOn = saved;
  }

  // m agents, n jobs, capacities at 60 % of an even share of the resources; the root bound, the
  // sum of the cheapest costs, and the cost of a feasible assignment (an upper bound of the
  // optimum), or Long.MAX_VALUE when the greedy assignment found none
  private static double[] rootBound(int m, int n, int seed, boolean on) {
    LinearRelaxation.encodingRowsOn = on;
    Random rnd = new Random(seed);
    Store store = new Store();
    int[][] cost = new int[m][n];
    int[][] res = new int[m][n];
    long cheapest = 0;
    for (int j = 0; j < n; j++) {
      int min = Integer.MAX_VALUE;
      for (int i = 0; i < m; i++) {
        cost[i][j] = 10 + rnd.nextInt(41);
        res[i][j] = 5 + rnd.nextInt(21);
        min = Math.min(min, cost[i][j]);
      }
      cheapest += min;
    }
    int cap = (int) (0.8 * 15 * n / m) + 25;
    IntVar[][] b = new IntVar[m][n];
    IntVar[] terms = new IntVar[n + 1];
    int[] ones = new int[n + 1];
    for (int j = 0; j < n; j++) {
      IntVar agent = new IntVar(store, "a" + j, 1, m);
      IntVar[] bj = new IntVar[m];
      int max = 0;
      int[] column = new int[m];
      for (int i = 0; i < m; i++) {
        b[i][j] = new BooleanVar(store, "b" + i + "_" + j);
        bj[i] = b[i][j];
        column[i] = cost[i][j];
        max = Math.max(max, cost[i][j]);
      }
      store.impose(new ChannelReif(agent, bj));
      IntVar c = new IntVar(store, "c" + j, 0, max);
      store.impose(new ElementInteger(agent, column, c, 0));
      terms[j] = c;
      ones[j] = 1;
    }
    for (int i = 0; i < m; i++) {
      store.impose(new LinearInt(b[i], res[i], "<=", cap));
    }
    IntVar total = new IntVar(store, "total", 0, 1_000_000);
    terms[n] = total;
    ones[n] = -1;
    store.impose(new LinearInt(terms, ones, "==", 0));
    assertThat(store.consistency()).isTrue();
    LinearRelaxation r =
        LinearRelaxation.of(
            store, total, false, List.of(), Set.of(), LinearRelaxation.Simplex.DENSE);
    assertThat(r).isNotNull();
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    // a feasible assignment: each job to the cheapest agent with room left
    int[] used = new int[m];
    long greedy = 0;
    for (int j = 0; j < n && greedy != Long.MAX_VALUE; j++) {
      int best = -1;
      for (int i = 0; i < m; i++) {
        if (used[i] + res[i][j] <= cap && (best < 0 || cost[i][j] < cost[best][j])) {
          best = i;
        }
      }
      if (best < 0) {
        greedy = Long.MAX_VALUE;
      } else {
        used[best] += res[best][j];
        greedy += cost[best][j];
      }
    }
    return new double[] {r.rootBound, cheapest, greedy};
  }

  @Test
  void encodingsGiveTheAssignmentBound() {
    double[] on = rootBound(10, 100, 2, true);
    double[] off = rootBound(10, 100, 2, false);
    // with the hull rows of the elements and the dense simplex (as before) the bound stays at the
    // cheapest costs; with the encodings in their place the capacities count (1,349.7 against
    // 1,315, a feasible assignment costs 1,527)
    assertThat(off[0]).isLessThanOrEqualTo(off[1] + 1e-6);
    assertThat(on[0]).isGreaterThan(on[1] + 10);
    if (on[2] != Long.MAX_VALUE) {
      assertThat(on[0]).isLessThanOrEqualTo(on[2] + 1e-6);
    }
  }
}
