/*
 * EntryIndex.java
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

package org.jacop.lcg;

import java.util.Arrays;

/**
 * The {@code !=} entries of an {@link AtomicTrail} by variable and value: an open-addressing table
 * with linear probing whose size follows the entries on the trail, so whether a value was removed
 * is found without walking the variable's entries.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class EntryIndex {

  private static final int EMPTY = -1;

  private long[] keys = new long[16];
  private int[] entries = new int[16];
  private int size;

  EntryIndex() {
    Arrays.fill(entries, EMPTY);
  }

  private static long key(int variable, int value) {
    return ((long) variable << 32) | (value & 0xffffffffL);
  }

  private int home(long key) {
    return (int) ((key * 0x9E3779B97F4A7C15L) >>> 32) & (keys.length - 1);
  }

  /** Returns the entry of a variable's value, or -1 when there is none. */
  int get(int variable, int value) {
    long k = key(variable, value);
    int mask = keys.length - 1;
    for (int p = home(k); entries[p] != EMPTY; p = (p + 1) & mask) {
      if (keys[p] == k) {
        return entries[p];
      }
    }
    return EMPTY;
  }

  /** Records the entry of a variable's value, replacing the one recorded before. */
  void put(int variable, int value, int entry) {
    if (2 * (size + 1) > keys.length) {
      grow();
    }
    long k = key(variable, value);
    int mask = keys.length - 1;
    int p = home(k);
    while (entries[p] != EMPTY) {
      if (keys[p] == k) {
        entries[p] = entry;
        return;
      }
      p = (p + 1) & mask;
    }
    keys[p] = k;
    entries[p] = entry;
    size++;
  }

  /** Forgets the entry of a variable's value. */
  void remove(int variable, int value) {
    long k = key(variable, value);
    int mask = keys.length - 1;
    int p = home(k);
    while (entries[p] != EMPTY && keys[p] != k) {
      p = (p + 1) & mask;
    }
    if (entries[p] == EMPTY) {
      return;
    }
    size--;
    // shifts back the entries after the hole that may sit there, so no probe stops early
    for (int j = (p + 1) & mask; entries[j] != EMPTY; j = (j + 1) & mask) {
      int h = home(keys[j]);
      if (((j - h) & mask) >= ((j - p) & mask)) {
        keys[p] = keys[j];
        entries[p] = entries[j];
        p = j;
      }
    }
    entries[p] = EMPTY;
  }

  private void grow() {
    long[] oldKeys = keys;
    int[] oldEntries = entries;
    keys = new long[2 * oldKeys.length];
    entries = new int[2 * oldKeys.length];
    Arrays.fill(entries, EMPTY);
    size = 0;
    for (int p = 0; p < oldKeys.length; p++) {
      if (oldEntries[p] != EMPTY) {
        put((int) (oldKeys[p] >>> 32), (int) oldKeys[p], oldEntries[p]);
      }
    }
  }
}
