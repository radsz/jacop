/*
 * MinOfSumsLcgTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Arrays;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.MinOfSums;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.junit.jupiter.api.Test;

/** MinOfSums under lazy clause generation, with every explanation checked. */
class MinOfSumsLcgTest {

  // one minimum of sums over the variables: m (an index) and its terms (y index -1 for none)
  private record Mins(int m, int[] tx, int[] ty) {
    boolean holds(int[] t) {
      long least = Long.MAX_VALUE;
      for (int i = 0; i < tx.length; i++) {
        least = Math.min(least, (long) t[tx[i]] + (ty[i] < 0 ? 0 : t[ty[i]]));
      }
      return t[m] == least;
    }
  }

  @Test
  void minimizesWithCheckedExplanations() {
    int proved = 0;
    for (int instance = 0; instance < 400; instance++) {
      Random rnd = new Random(instance);
      Store store = new Store();
      int n = 4 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, rnd.nextInt(3) - 1, 3 + rnd.nextInt(4));
        if (rnd.nextInt(3) == 0) {
          x[i].domain.subtractAdapt(x[i].min() + 1 + rnd.nextInt(x[i].max() - x[i].min() - 1));
          x[i].refreshBounds();
        }
      }
      Mins[] mins = new Mins[1 + rnd.nextInt(2)];
      for (int c = 0; c < mins.length; c++) {
        int m = rnd.nextInt(n);
        int k = 1 + rnd.nextInt(4);
        int[] tx = new int[k];
        int[] ty = new int[k];
        for (int i = 0; i < k; i++) {
          do {
            tx[i] = rnd.nextInt(n);
          } while (tx[i] == m);
          ty[i] = rnd.nextInt(3) == 0 ? -1 : rnd.nextInt(n);
          if (ty[i] == m || ty[i] == tx[i]) {
            ty[i] = -1;
          }
        }
        mins[c] = new Mins(m, tx, ty);
        IntVar[] a = new IntVar[k];
        IntVar[] b = new IntVar[k];
        for (int i = 0; i < k; i++) {
          a[i] = x[tx[i]];
          b[i] = ty[i] < 0 ? null : x[ty[i]];
        }
        store.impose(new MinOfSums(a, b, x[m]));
      }
      int[] w = new int[n + 1];
      for (int i = 0; i < n; i++) {
        w[i] = rnd.nextInt(7) - 3;
      }
      w[n] = -1;
      long best = best(x, mins, w);
      IntVar cost = new IntVar(store, "cost", -1000, 1000);
      IntVar[] terms = Arrays.copyOf(x, n + 1);
      terms[n] = cost;
      store.impose(new LinearInt(terms, w, "==", 0));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setSeed(instance % 3);
      int status = solver.minimize(cost);
      if (best == Long.MAX_VALUE) {
        assertThat(status).as("instance %d", instance).isEqualTo(CdclSolver.UNSAT);
        continue;
      }
      assertThat(status).as("instance %d", instance).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(cost)).as("instance %d", instance).isEqualTo(best);
      int[] t = new int[n];
      for (int i = 0; i < n; i++) {
        t[i] = solver.value(x[i]);
      }
      for (Mins c : mins) {
        assertThat(c.holds(t)).as("instance %d", instance).isTrue();
      }
      proved++;
    }
    assertThat(proved).isGreaterThan(100);
  }

  // the least weighted sum over the assignments of x that satisfy the minimums, MAX_VALUE for none
  private static long best(IntVar[] x, Mins[] mins, int[] w) {
    int n = x.length;
    int[] t = new int[n];
    long best = Long.MAX_VALUE;
    for (int i = 0; i < n; i++) {
      t[i] = x[i].min();
    }
    while (true) {
      boolean ok = true;
      for (int i = 0; i < n && ok; i++) {
        ok = x[i].domain.contains(t[i]);
      }
      for (int c = 0; c < mins.length && ok; c++) {
        ok = mins[c].holds(t);
      }
      if (ok) {
        long s = 0;
        for (int i = 0; i < n; i++) {
          s += (long) w[i] * t[i];
        }
        best = Math.min(best, s);
      }
      int i = 0;
      while (i < n && t[i] == x[i].max()) {
        t[i] = x[i].min();
        i++;
      }
      if (i == n) {
        return best;
      }
      t[i]++;
    }
  }
}
