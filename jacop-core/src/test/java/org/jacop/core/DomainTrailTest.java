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
    public void undo(DomainTrail trail, int entry) {
      undone.add(
          new long[] {
            entry,
            trail.getInt(entry, 0),
            trail.getInt(entry, 1),
            trail.getInt(entry, DomainTrail.INTS - 1),
            trail.getLong(entry),
            trail.getObject(entry, DomainTrail.OBJECTS - 1) instanceof Integer i ? i : -1
          });
    }
  }

  @Test
  void entriesSurviveGrowthAndPopNewestFirst() {
    DomainTrail trail = new DomainTrail();
    Recorder r = new Recorder();
    // 10 levels of 1000 entries cross the first segments (256, 512, 1024, ... entries)
    int levels = 10;
    int perLevel = 1000;
    for (int level = 1; level <= levels; level++) {
      for (int k = 0; k < perLevel; k++) {
        int entry = trail.push(r, k, level);
        assertThat(entry).isEqualTo((level - 1) * perLevel + k);
        trail.setInt(entry, DomainTrail.INTS - 1, -entry);
        trail.setLong(entry, 1L << 40 | entry);
        trail.setObject(entry, DomainTrail.OBJECTS - 1, entry * 3);
      }
    }
    assertThat(trail.size()).isEqualTo(levels * perLevel);

    trail.removeLevel(levels - 1);
    assertThat(trail.size()).isEqualTo((levels - 2) * perLevel);
    assertThat(r.undone).hasSize(2 * perLevel);
    for (int i = 0; i < r.undone.size(); i++) {
      long[] u = r.undone.get(i);
      int entry = levels * perLevel - 1 - i;
      int level = entry / perLevel + 1;
      assertThat(u)
          .containsExactly(entry, entry % perLevel, level, -entry, 1L << 40 | entry, entry * 3L);
    }

    // the space of popped entries is used again, with no stale objects
    int entry = trail.push(r, 7, levels);
    assertThat(entry).isEqualTo((levels - 2) * perLevel);
    assertThat(trail.getObject(entry, DomainTrail.OBJECTS - 1)).isNull();
    assertThat(trail.getInt(entry - 1, DomainTrail.INTS - 1)).isEqualTo(-(entry - 1));

    r.undone.clear();
    trail.removeLevel(1);
    assertThat(trail.size()).isZero();
    assertThat(r.undone).hasSize((levels - 2) * perLevel + 1);
  }
}
