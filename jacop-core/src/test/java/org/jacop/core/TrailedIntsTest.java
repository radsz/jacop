/*
 * TrailedIntsTest.java
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

package org.jacop.core;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Random;
import org.junit.jupiter.api.Test;

class TrailedIntsTest {

  /** Random sets at random depths give back, after each backtrack, the values of that level. */
  @Test
  void restoresTheValuesOfEachLevelOnBacktracking() {
    Random random = new Random(3);
    for (int run = 0; run < 200; run++) {
      Store store = new Store();
      int n = 1 + random.nextInt(4);
      TrailedInts values = new TrailedInts(store, n);
      // the values at the end of each level above the current one
      Deque<int[]> saved = new ArrayDeque<>();
      int[] expected = new int[n];
      for (int step = 0; step < 300; step++) {
        int action = random.nextInt(4);
        if (action == 0) {
          saved.push(expected.clone());
          store.setLevel(store.level + 1);
        } else if (action == 1 && !saved.isEmpty()) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          expected = saved.pop();
        } else {
          int i = random.nextInt(n);
          int value = random.nextInt(3);
          values.set(i, value);
          expected[i] = value;
        }
        for (int i = 0; i < n; i++) {
          assertThat(values.get(i))
              .as("run %d step %d value %d", run, step, i)
              .isEqualTo(expected[i]);
        }
      }
    }
  }
}
