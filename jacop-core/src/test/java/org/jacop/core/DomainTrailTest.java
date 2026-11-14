/*
 * DomainTrailTest.java
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

import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Test;

/**
 * Checks that the entries of a {@link DomainTrail} keep their values across the segments the trail
 * grows by, and that popping a level gives back its entries newest first.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class DomainTrailTest {

  /** Records the entries it is given back, with the values read from them. */
  static final class Recorder implements DomainTrail.Entry {
    final List<long[]> undone = new ArrayList<>();

    @Override
    public void undoWord(int word, int stamp, long value) {
      undone.add(new long[] {word, stamp, value});
    }

    @Override
    public void undo(DomainTrail trail, int entry, int kind) {
      int n = -kind;
      long[] u = new long[2 + 2 * n];
      u[0] = kind;
      u[1] = trail.getObject(entry, 0) == this ? 1 : 0;
      for (int k = 0; k < n; k++) {
        u[2 + k] = trail.getInt(entry, k);
        u[2 + n + k] = (Integer) trail.getObject(entry, k + 1);
      }
      undone.add(u);
    }
  }

  /** The values the i-th push of fill writes, as the recorder reads them back. */
  private static long[] expected(int i, int level) {
    if (i % 3 != 0) {
      return new long[] {i % 1000, level, 1L << 40 | i};
    }
    int n = 1 + i % 7;
    long[] u = new long[2 + 2 * n];
    u[0] = -n;
    u[1] = 1;
    for (int k = 0; k < n; k++) {
      u[2 + k] = i * 10L + k;
      u[2 + n + k] = -(i * 10L + k);
    }
    return u;
  }

  /** Pushes perLevel entries for each level from first to last, mixing word and other entries. */
  private static int fill(DomainTrail trail, Recorder r, int first, int last, int perLevel) {
    int i = (first - 1) * perLevel;
    for (int level = first; level <= last; level++) {
      for (int k = 0; k < perLevel; k++, i++) {
        if (i % 3 != 0) {
          trail.pushWord(r, i % 1000, level, level, 1L << 40 | i);
        } else {
          int n = 1 + i % 7;
          int entry = trail.push(r, -n, level, n, n);
          for (int j = 0; j < n; j++) {
            trail.setInt(entry, j, i * 10 + j);
            trail.setObject(entry, j + 1, -(i * 10 + j));
          }
        }
      }
    }
    return i;
  }

  @Test
  void entriesSurviveGrowthAndPopNewestFirst() {
    DomainTrail trail = new DomainTrail();
    Recorder r = new Recorder();
    assertThat(trail.isEmpty()).isTrue();
    // 20 levels of 1000 mixed entries cross the first segments of both streams
    int levels = 20;
    int perLevel = 1000;
    fill(trail, r, 1, levels, perLevel);

    trail.removeLevel(levels - 1);
    assertThat(r.undone).hasSize(2 * perLevel);
    for (int j = 0; j < r.undone.size(); j++) {
      int i = levels * perLevel - 1 - j;
      assertThat(r.undone.get(j)).containsExactly(expected(i, i / perLevel + 1));
    }

    // the space of popped entries is used again, then everything pops in order
    fill(trail, r, levels - 1, levels + 5, perLevel);
    r.undone.clear();
    trail.removeLevel(1);
    assertThat(trail.isEmpty()).isTrue();
    assertThat(r.undone).hasSize((levels + 5) * perLevel);
    for (int j = 0; j < r.undone.size(); j++) {
      int i = (levels + 5) * perLevel - 1 - j;
      assertThat(r.undone.get(j)).containsExactly(expected(i, i / perLevel + 1));
    }
    r.undone.clear();
    trail.removeLevel(0);
    assertThat(r.undone).isEmpty();
  }

  @Test
  void savedWordsGivesTheOldestWordAfterAnEntry() {
    DomainTrail trail = new DomainTrail();
    Recorder a = new Recorder();
    Recorder b = new Recorder();
    for (int i = 0; i < 5000; i++) {
      trail.pushWord(b, i % 4, 1, 0, -1L);
    }
    int entry = trail.push(a, -1, 2, 1, 1);
    for (int i = 0; i < 5000; i++) {
      // a's words 0..3 first saved with values 100 + word, then overwritten by later saves
      trail.pushWord(a, i % 4, 2 + i / 100, 0, 100 + i);
      trail.pushWord(b, i % 4, 2 + i / 100, 0, -2L);
      trail.push(b, -3, 2 + i / 100, 3, 2);
    }
    long[] words = new long[5];
    trail.savedWords(a, entry, words);
    assertThat(words).containsExactly(100, 101, 102, 103, 0);
  }
}
