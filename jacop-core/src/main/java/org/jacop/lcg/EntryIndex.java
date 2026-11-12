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

  // slot p at 2p (the key) and 2p + 1 (the entry, EMPTY when free), so a probe reads one line
  private long[] table = newTable(16);
  private int size;

  EntryIndex() {}

  private static long[] newTable(int slots) {
    long[] t = new long[2 * slots];
    for (int p = 1; p < t.length; p += 2) {
      t[p] = EMPTY;
    }
    return t;
  }

  private static long key(int variable, int value) {
    return ((long) variable << 32) | (value & 0xffffffffL);
  }

  // the home slot of a key in a table of mask + 1 slots
  private static int home(long key, int mask) {
    return (int) ((key * 0x9E3779B97F4A7C15L) >>> 32) & mask;
  }

  /** Returns the entry of a variable's value, or -1 when there is none. */
  int get(int variable, int value) {
    long k = key(variable, value);
    long[] t = table;
    int mask = (t.length >>> 1) - 1;
    for (int p = home(k, mask); t[2 * p + 1] != EMPTY; p = (p + 1) & mask) {
      if (t[2 * p] == k) {
        return (int) t[2 * p + 1];
      }
    }
    return EMPTY;
  }

  /** Records the entry of a variable's value, replacing the one recorded before. */
  void put(int variable, int value, int entry) {
    if (4 * (size + 1) > table.length) {
      grow();
    }
    long k = key(variable, value);
    long[] t = table;
    int mask = (t.length >>> 1) - 1;
    int p = home(k, mask);
    while (t[2 * p + 1] != EMPTY) {
      if (t[2 * p] == k) {
        t[2 * p + 1] = entry;
        return;
      }
      p = (p + 1) & mask;
    }
    t[2 * p] = k;
    t[2 * p + 1] = entry;
    size++;
  }

  /** Forgets the entry of a variable's value. */
  void remove(int variable, int value) {
    long k = key(variable, value);
    long[] t = table;
    int mask = (t.length >>> 1) - 1;
    int p = home(k, mask);
    while (t[2 * p + 1] != EMPTY && t[2 * p] != k) {
      p = (p + 1) & mask;
    }
    if (t[2 * p + 1] == EMPTY) {
      return;
    }
    size--;
    // shifts back the entries after the hole that may sit there, so no probe stops early
    for (int j = (p + 1) & mask; t[2 * j + 1] != EMPTY; j = (j + 1) & mask) {
      int h = home(t[2 * j], mask);
      if (((j - h) & mask) >= ((j - p) & mask)) {
        t[2 * p] = t[2 * j];
        t[2 * p + 1] = t[2 * j + 1];
        p = j;
      }
    }
    t[2 * p + 1] = EMPTY;
  }

  private void grow() {
    long[] old = table;
    table = newTable(old.length);
    size = 0;
    for (int p = 0; p < old.length; p += 2) {
      if (old[p + 1] != EMPTY) {
        put((int) (old[p] >>> 32), (int) old[p], (int) old[p + 1]);
      }
    }
  }
}
