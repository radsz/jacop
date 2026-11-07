/*
 * TrailedTupleSetTest.java
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
package org.jacop.constraints.table;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * It checks the trail of TrailedTupleSet against snapshots of its records on random searches,
 * including levels that change no record, levels skipped by the owner and changes made at a level
 * again after backtracking to it.
 */
class TrailedTupleSetTest {

  @Test
  void removeLevelRestoresTheRecordsOfEveryLevel() {
    Random random = new Random(7);
    for (int run = 0; run < 2000; run++) {
      int tuples = 1 + random.nextInt(300);
      int records = random.nextInt(4);
      TrailedTupleSet set = new TrailedTupleSet(tuples, records);
      int length = set.state.length;
      // The snapshots of the records when each level was entered, from level from.
      List<long[]> snapshots = new ArrayList<>();
      List<Integer> levels = new ArrayList<>();
      List<Integer> from = new ArrayList<>();
      int level = 0;
      for (int step = 0; step < 300; step++) {
        int action = random.nextInt(10);
        if (action < 3) {
          from.add(level);
          level += 1 + (random.nextInt(4) == 0 ? random.nextInt(3) : 0);
          snapshots.add(set.state.clone());
          levels.add(level);
        } else if (action < 5 && !levels.isEmpty()) {
          int k = random.nextInt(levels.size());
          // Any level above the one the snapshot was taken at, so also skipped levels.
          int removed = from.get(k) + 1 + random.nextInt(levels.get(k) - from.get(k));
          long[] expected = snapshots.get(k);
          set.removeLevel(removed);
          assertThat(set.state).as("run %d step %d", run, step).isEqualTo(expected);
          snapshots.subList(k, snapshots.size()).clear();
          levels.subList(k, levels.size()).clear();
          from.subList(k, from.size()).clear();
          level = removed - 1;
        } else if (action < 8) {
          set.newEpochIfNeeded(level);
          long[] mask = new long[set.words];
          for (int w = 0; w < mask.length; w++) {
            mask[w] = random.nextInt(3) == 0 ? random.nextLong() : -1L;
          }
          set.clearMask();
          set.addToMask(mask);
          set.intersectWithMask();
        } else if (records > 0) {
          set.newEpochIfNeeded(level);
          set.set(set.limitRecord + 1 + random.nextInt(records), random.nextInt(100));
        }
        assertIndex(set);
      }
    }
  }

  @Test
  void changedSinceTellsWhetherALevelChangedSomeRecord() {
    TrailedTupleSet set = new TrailedTupleSet(130, 1);
    assertThat(set.changedSince(0)).isFalse();
    set.newEpochIfNeeded(2);
    set.set(set.limitRecord + 1, 5);
    assertThat(set.changedSince(2)).isTrue();
    assertThat(set.changedSince(3)).isFalse();
    set.removeLevel(4);
    assertThat(set.changedSince(2)).isTrue();
    set.removeLevel(2);
    assertThat(set.changedSince(0)).isFalse();
    assertThat(set.state[set.limitRecord + 1]).isZero();
  }

  /** The non-zero words are exactly index[0..limit]. */
  private static void assertIndex(TrailedTupleSet set) {
    int limit = set.limit();
    boolean[] listed = new boolean[set.words];
    for (int p = 0; p <= limit; p++) {
      listed[set.index[p]] = true;
    }
    for (int w = 0; w < set.words; w++) {
      assertThat(set.state[w] != 0L).as("word %d", w).isEqualTo(listed[w]);
    }
    int[] sorted = set.index.clone();
    Arrays.sort(sorted);
    for (int w = 0; w < set.words; w++) {
      assertThat(sorted[w]).isEqualTo(w);
    }
  }
}
