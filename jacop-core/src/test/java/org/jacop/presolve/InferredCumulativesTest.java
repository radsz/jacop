/*
 * InferredCumulativesTest.java
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

package org.jacop.presolve;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests the inference of redundant cumulatives by lifting covers.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class InferredCumulativesTest {

  @Test
  void paperExample() {
    // Example 9 of Sidorov (CP 2026): uses 5, 3, 2, 4 and capacity 7 give x1 + x2 + x3 + x4 <= 2
    InferredCumulatives ic = new InferredCumulatives(new int[] {3, 3, 3, 3});
    ic.resource(new int[] {0, 1, 2, 3}, new int[] {5, 3, 2, 4}, 7);
    List<InferredCumulatives.Inferred> found = ic.infer(100, 5, null);
    assertEquals(1, found.size());
    InferredCumulatives.Inferred inf = found.get(0);
    assertArrayEquals(new int[] {0, 1, 2, 3}, inf.tasks());
    assertArrayEquals(new int[] {1, 1, 1, 1}, inf.use());
    assertEquals(2, inf.capacity());
    assertEquals(6.0, inf.bound(), 1e-9);
  }

  @Test
  void twoResourcesTogether() {
    // each resource alone lets two of the three tasks run together, both together only one
    InferredCumulatives ic = new InferredCumulatives(new int[] {4, 4, 4, 1});
    ic.resource(new int[] {0, 1, 2, 3}, new int[] {2, 2, 1, 1}, 3);
    ic.resource(new int[] {0, 1, 2, 3}, new int[] {1, 2, 2, 1}, 3);
    ic.resource(new int[] {0, 1, 2, 3}, new int[] {2, 1, 2, 1}, 3);
    List<InferredCumulatives.Inferred> found = ic.infer(100, 5, null);
    assertTrue(
        found.stream().anyMatch(i -> i.unary() && i.tasks().length == 3 && i.tasks()[2] == 2),
        found.toString());
  }

  @Test
  void inferredInequalitiesAreValid() {
    Random random = new Random(7);
    int inferred = 0;
    for (int trial = 0; trial < 3000; trial++) {
      int n = 4 + random.nextInt(5);
      int[] duration = new int[n];
      for (int t = 0; t < n; t++) {
        duration[t] = 1 + random.nextInt(9);
      }
      // a small work limit cuts some liftings short, which must stay valid
      long work = random.nextInt(4) == 0 ? 50 + random.nextInt(2000) : 1_000_000;
      InferredCumulatives ic = new InferredCumulatives(duration, work);
      List<int[]> rows = new ArrayList<>();
      List<Integer> caps = new ArrayList<>();
      int m = 1 + random.nextInt(3);
      for (int r = 0; r < m; r++) {
        int cap = 2 + random.nextInt(8);
        int[] use = new int[n];
        int[] tasks = new int[n];
        for (int t = 0; t < n; t++) {
          tasks[t] = t;
          use[t] = random.nextInt(3) == 0 ? 0 : 1 + random.nextInt(cap);
        }
        ic.resource(tasks, use, cap);
        rows.add(use);
        caps.add(cap);
      }
      long[][] adj = new long[n][1];
      for (int k = random.nextInt(4); k > 0; k--) {
        int i = random.nextInt(n);
        int j = random.nextInt(n);
        if (i != j) {
          adj[i][0] |= 1L << j;
          adj[j][0] |= 1L << i;
        }
      }
      ic.disjoint(adj);
      for (InferredCumulatives.Inferred inf : ic.infer(100, 50, null)) {
        inferred++;
        int[] pi = new int[n];
        for (int k = 0; k < inf.tasks().length; k++) {
          pi[inf.tasks()[k]] = inf.use()[k];
        }
        // every set of tasks that can run at one time point satisfies the inequality
        for (int x = 0; x < 1 << n; x++) {
          if (feasible(x, n, rows, caps, adj)) {
            int lhs = 0;
            for (int t = 0; t < n; t++) {
              if ((x & (1 << t)) != 0) {
                lhs += pi[t];
              }
            }
            assertTrue(lhs <= inf.capacity(), "trial " + trial + " point " + x + " " + inf);
          }
        }
      }
    }
    assertTrue(inferred > 100, "inferred " + inferred);
  }

  private static boolean feasible(
      int x, int n, List<int[]> rows, List<Integer> caps, long[][] adj) {
    for (int r = 0; r < rows.size(); r++) {
      int load = 0;
      for (int t = 0; t < n; t++) {
        if ((x & (1 << t)) != 0) {
          load += rows.get(r)[t];
        }
      }
      if (load > caps.get(r)) {
        return false;
      }
    }
    for (int i = 0; i < n; i++) {
      if ((x & (1 << i)) != 0 && (adj[i][0] & x) != 0) {
        return false;
      }
    }
    return true;
  }
}
