/*
 * AliveCounts.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2026 Radoslaw Szymanek
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

package org.jacop.constraints.regular;

import java.util.Arrays;

/**
 * The numbers of alive edges of the levels of a layered graph, trailed so that backtracking
 * restores them. A count is saved at most once per store level: the trail holds pairs of level and
 * previous count, with a mark where each store level begins.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class AliveCounts {

  /** The number of alive edges of each level. */
  final int[] alive;

  private final int[] savedEpoch;
  private int epoch;
  private int epochLevel = -1;
  private int currentLevel;
  private int[] trail = new int[64];
  private int trailTop;
  private int[] markLevel = new int[16];
  private int[] markPosition = new int[16];
  private int markTop;

  AliveCounts(int[] alive) {
    this.alive = alive;
    this.savedEpoch = new int[alive.length];
  }

  /** It starts a consistency call at the given store level. */
  void begin(int storeLevel) {
    currentLevel = storeLevel;
    if (epochLevel != currentLevel) {
      if (++epoch == Integer.MAX_VALUE) {
        Arrays.fill(savedEpoch, 0);
        epoch = 1;
      }
      epochLevel = currentLevel;
    }
  }

  /** It sets the number of alive edges of a level, trailing the previous number. */
  void set(int level, int count) {
    if (savedEpoch[level] != epoch) {
      savedEpoch[level] = epoch;
      if (markTop == 0 || markLevel[markTop - 1] != currentLevel) {
        if (markTop == markLevel.length) {
          markLevel = Arrays.copyOf(markLevel, 2 * markTop);
          markPosition = Arrays.copyOf(markPosition, 2 * markTop);
        }
        markLevel[markTop] = currentLevel;
        markPosition[markTop++] = trailTop;
      }
      if (trailTop + 2 > trail.length) {
        trail = Arrays.copyOf(trail, 2 * trail.length);
      }
      trail[trailTop] = level;
      trail[trailTop + 1] = alive[level];
      trailTop += 2;
    }
    alive[level] = count;
  }

  /** It restores the counts saved at the given store level and above. */
  void removeLevel(int level) {
    while (markTop > 0 && markLevel[markTop - 1] >= level) {
      int start = markPosition[--markTop];
      while (trailTop > start) {
        trailTop -= 2;
        alive[trail[trailTop]] = trail[trailTop + 1];
      }
    }
    epochLevel = -1;
  }
}
