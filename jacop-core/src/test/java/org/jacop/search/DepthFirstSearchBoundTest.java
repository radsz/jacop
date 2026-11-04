/*
 * DepthFirstSearchBoundTest.java
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

package org.jacop.search;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * The bounds that depth-first search reports at the nodes whose subtree is all that is left: under
 * branch and bound each must hold for every solution not found yet, so none is above the optimum,
 * and they rise up to it when the search ends.
 */
class DepthFirstSearchBoundTest {

  @Test
  void lastSubtreeBoundsHoldAndRise() {
    Random r = new Random(41);
    int raised = 0;
    for (int instance = 0; instance < 300; instance++) {
      Store store = new Store();
      int n = 5;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 4);
      }
      List<int[]> ne = new ArrayList<>();
      for (int k = 0; k < 4; k++) {
        int i = r.nextInt(n);
        int j = r.nextInt(n);
        if (i != j) {
          store.impose(new XneqY(x[i], x[j]));
          ne.add(new int[] {i, j});
        }
      }
      int[] a = new int[n];
      for (int i = 0; i < n; i++) {
        a[i] = r.nextInt(7) - 3;
      }
      int rhs = r.nextInt(6);
      store.impose(new LinearInt(x, a, "<=", rhs));
      int[] w = new int[n + 1];
      IntVar cost = new IntVar(store, "cost", -1000, 1000);
      IntVar[] terms = new IntVar[n + 1];
      for (int i = 0; i < n; i++) {
        w[i] = r.nextInt(21) - 10;
        terms[i] = x[i];
      }
      w[n] = -1;
      terms[n] = cost;
      store.impose(new LinearInt(terms, w, "==", 0));

      long optimum = optimum(a, rhs, w, ne, new int[n], 0);

      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      List<Integer> bounds = new ArrayList<>();
      search.setLastSubtreeListener(() -> bounds.add(cost.min()));
      SelectChoicePoint<IntVar> select =
          r.nextBoolean()
              ? new SimpleSelect<>(x, null, new IndomainMin<>())
              : new SimpleSelect<>(x, new SmallestDomain<>(), new IndomainMax<>());
      boolean found = search.labeling(store, select, cost);
      if (optimum == Long.MAX_VALUE) {
        assertThat(found).isFalse();
        continue;
      }
      assertThat(found).isTrue();
      assertThat(search.getCostValue()).as("instance %d", instance).isEqualTo((int) optimum);
      for (int k = 0; k < bounds.size(); k++) {
        assertThat((long) bounds.get(k)).as("instance %d", instance).isLessThanOrEqualTo(optimum);
        if (k > 0) {
          assertThat(bounds.get(k)).isGreaterThanOrEqualTo(bounds.get(k - 1));
        }
      }
      if (bounds.size() > 1 && bounds.get(bounds.size() - 1) > bounds.get(0)) {
        raised++;
      }
    }
    assertThat(raised).isGreaterThan(10);
  }

  // the smallest cost over the assignments of 0..4 that satisfy the constraints
  private static long optimum(int[] a, int rhs, int[] w, List<int[]> ne, int[] t, int i) {
    if (i == t.length) {
      long lhs = 0;
      long cost = 0;
      for (int k = 0; k < t.length; k++) {
        lhs += (long) a[k] * t[k];
        cost += (long) w[k] * t[k];
      }
      if (lhs > rhs) {
        return Long.MAX_VALUE;
      }
      for (int[] p : ne) {
        if (t[p[0]] == t[p[1]]) {
          return Long.MAX_VALUE;
        }
      }
      return cost;
    }
    long best = Long.MAX_VALUE;
    for (int v = 0; v <= 4; v++) {
      t[i] = v;
      best = Math.min(best, optimum(a, rhs, w, ne, t, i + 1));
    }
    return best;
  }
}
