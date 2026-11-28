/*
 * SumInt.java
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

package org.jacop.constraints;

import java.util.Arrays;
import org.jacop.api.Stateful;
import org.jacop.core.Store;

/**
 * The part of a sum's state that drops fixed variables from propagation: how many variables of each
 * of (at most) two groups are still free, and the sum of the terms of the dropped ones. The owner
 * keeps the free variables of a group first in its array and moves a variable behind them when it
 * becomes fixed; only the counts and the sum have to be restored when the store backtracks. Like a
 * timestamp, the state is restored only when a level at which it changed is removed, so a sum that
 * drops nothing costs nothing on backtracking.
 */
final class DroppedTerms implements Stateful {

  /** The number of free variables in the first group. */
  int freeFirst;

  /** The end of the free variables in the second group. */
  int freeSecond;

  /** The sum of the terms of the dropped variables. */
  long fixedSum;

  private final Store store;
  private int size;
  private int[] levels = new int[8];
  private int[] firsts = new int[8];
  private int[] seconds = new int[8];
  private long[] sums = new long[8];

  DroppedTerms(Store store, int freeFirst, int freeSecond) {
    this.store = store;
    this.freeFirst = freeFirst;
    this.freeSecond = freeSecond;
  }

  /**
   * Drops a fixed variable's term: adds it to fixedSum, after recording the state before its first
   * change at the current level.
   *
   * @param term the term of the fixed variable.
   */
  void drop(long term) {
    int level = store.level;
    if (size == 0 || levels[size - 1] != level) {
      if (size == levels.length) {
        int capacity = size * 2;
        levels = Arrays.copyOf(levels, capacity);
        firsts = Arrays.copyOf(firsts, capacity);
        seconds = Arrays.copyOf(seconds, capacity);
        sums = Arrays.copyOf(sums, capacity);
      }
      levels[size] = level;
      firsts[size] = freeFirst;
      seconds[size] = freeSecond;
      sums[size] = fixedSum;
      size++;
      store.recordChange(this);
    }
    fixedSum += term;
  }

  /**
   * Restores the state the store had before the given level.
   *
   * @param level the level being removed.
   */
  @Override
  public void removeLevel(int level) {
    while (size > 0 && levels[size - 1] >= level) {
      size--;
      freeFirst = firsts[size];
      freeSecond = seconds[size];
      fixedSum = sums[size];
    }
  }
}
