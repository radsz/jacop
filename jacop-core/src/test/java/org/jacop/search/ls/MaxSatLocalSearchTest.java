/*
 * MaxSatLocalSearchTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with Section 7 of this License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.search.ls;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Checks MaxSAT local search on small random weighted partial MaxSAT instances: the incremental
 * counts, scores and cost stay equal to their values recomputed from the clauses after every flip,
 * the best cost is never below the optimum of an enumeration, and the search reaches it.
 */
class MaxSatLocalSearchTest {

  private static boolean satisfied(int[] clause, int assignment) {
    for (int lit : clause) {
      if (((assignment >> (lit >> 1)) & 1) == ((lit & 1) == 0 ? 1 : 0)) {
        return true;
      }
    }
    return false;
  }

  // the least weight of falsified soft clauses over the assignments satisfying the hard clauses
  private static long optimum(int n, List<int[]> hard, List<int[]> soft, long[] w) {
    long best = Long.MAX_VALUE;
    for (int a = 0; a < (1 << n); a++) {
      boolean ok = true;
      for (int[] c : hard) {
        ok &= satisfied(c, a);
      }
      if (!ok) {
        continue;
      }
      long cost = 0;
      for (int k = 0; k < soft.size(); k++) {
        cost += satisfied(soft.get(k), a) ? 0 : w[k];
      }
      best = Math.min(best, cost);
    }
    return best;
  }

  private static int[] randomClause(Random random, int n, int maxLength) {
    int[] c = new int[1 + random.nextInt(maxLength)];
    for (int j = 0; j < c.length; j++) {
      c[j] = random.nextInt(2 * n);
    }
    return c;
  }

  @Test
  void searchKeepsItsScoresAndReachesTheOptimum() {
    Random random = new Random(7);
    for (int trial = 0; trial < 300; trial++) {
      int n = 2 + random.nextInt(11);
      List<int[]> hard = new ArrayList<>();
      List<int[]> soft = new ArrayList<>();
      int hards = random.nextInt(20);
      int softs = 1 + random.nextInt(15);
      long[] w = new long[softs];
      for (int i = 0; i < hards; i++) {
        hard.add(randomClause(random, n, 4));
      }
      for (int i = 0; i < softs; i++) {
        soft.add(randomClause(random, n, 3));
        w[i] = 1 + random.nextInt(9);
      }
      MaxSatLocalSearch ls =
          new MaxSatLocalSearch(n, hard, soft, w, 1 + random.nextInt(20), trial).smoothing(0.2);
      boolean[] start = new boolean[n];
      for (int i = 0; i < n; i++) {
        start[i] = random.nextBoolean();
      }
      ls.start(start);
      assertTrue(ls.consistent(), "trial " + trial + " at the start");
      for (int step = 0; step < 200; step++) {
        ls.run(1, () -> false);
        assertTrue(ls.consistent(), "trial " + trial + " step " + step);
      }
      long optimum = optimum(n, hard, soft, w);
      ls.run(20_000, () -> false);
      assertEquals(optimum, ls.bestCost(), "trial " + trial);
      if (optimum < Long.MAX_VALUE) {
        boolean[] best = ls.bestAssignment();
        int a = 0;
        for (int i = 0; i < n; i++) {
          a |= best[i] ? 1 << i : 0;
        }
        long cost = 0;
        for (int[] c : hard) {
          assertTrue(satisfied(c, a), "trial " + trial + " breaks a hard clause");
        }
        for (int k = 0; k < softs; k++) {
          cost += satisfied(soft.get(k), a) ? 0 : w[k];
        }
        assertEquals(optimum, cost, "trial " + trial + " best assignment");
      }
    }
  }
}
