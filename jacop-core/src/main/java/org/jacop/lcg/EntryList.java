/*
 * EntryList.java
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
 * A growable list of atomic trail entries, reused between explanations.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class EntryList {

  private int[] entries = new int[16];
  private int size;

  // how much weaker than its entry's bound each position's atom may be; null while all are 0
  private int[] slacks;

  /**
   * Adds an entry.
   *
   * @param entry the entry
   */
  public void add(int entry) {
    addLifted(entry, 0);
  }

  /**
   * Adds the entry of a bound together with how much weaker the bound may be: a reason holds with
   * {@code x >= value - slack} in place of a {@code x >= value} entry, and with {@code x <= value +
   * slack} in place of a {@code x <= value} one. The solver may cite such a weaker atom when it has
   * a literal for it.
   *
   * @param entry the entry
   * @param slack how much weaker the bound may be, at least 0
   */
  public void addLifted(int entry, int slack) {
    if (size == entries.length) {
      entries = Arrays.copyOf(entries, 2 * size);
      if (slacks != null) {
        slacks = Arrays.copyOf(slacks, 2 * size);
      }
    }
    if (slack != 0 && slacks == null) {
      slacks = new int[entries.length];
    }
    if (slacks != null) {
      slacks[size] = slack;
    }
    entries[size++] = entry;
  }

  /**
   * Adds the entry at a position of another list, with its slack.
   *
   * @param other the list
   * @param position the position, below its size
   */
  public void addFrom(EntryList other, int position) {
    addLifted(other.get(position), other.slack(position));
  }

  /**
   * Returns how much weaker than its entry the atom at a position may be (see {@link #addLifted}).
   *
   * @param position the position, below {@link #size()}
   * @return the slack, 0 when the atom is the entry's
   */
  public int slack(int position) {
    return slacks == null ? 0 : slacks[position];
  }

  /**
   * Returns the entry at a position.
   *
   * @param position the position, below {@link #size()}
   * @return the entry
   */
  public int get(int position) {
    return entries[position];
  }

  /**
   * Replaces the entry at a position.
   *
   * @param position the position, below {@link #size()}
   * @param entry the entry
   */
  public void set(int position, int entry) {
    entries[position] = entry;
  }

  /**
   * Returns the number of entries.
   *
   * @return the size
   */
  public int size() {
    return size;
  }

  /**
   * Keeps only the first entries.
   *
   * @param newSize the number of entries kept, at most {@link #size()}
   */
  public void truncate(int newSize) {
    size = newSize;
  }

  /**
   * Sorts the entries from a position on and removes the repeated ones among them.
   *
   * @param from the first position sorted
   */
  public void sortUnique(int from) {
    if (size - from < 2) {
      return;
    }
    if (slacks != null) {
      sortUniqueLifted(from);
      return;
    }
    Arrays.sort(entries, from, size);
    int kept = from + 1;
    for (int k = from + 1; k < size; k++) {
      if (entries[k] != entries[kept - 1]) {
        entries[kept++] = entries[k];
      }
    }
    size = kept;
  }

  // sorts entries with their slacks; a repeated entry keeps its smallest slack, the strongest atom
  private void sortUniqueLifted(int from) {
    long[] pairs = new long[size - from];
    for (int k = from; k < size; k++) {
      pairs[k - from] = ((long) entries[k] << 32) | (slacks[k] & 0xffffffffL);
    }
    Arrays.sort(pairs);
    int kept = from;
    for (long pair : pairs) {
      int entry = (int) (pair >>> 32);
      if (kept == from || entries[kept - 1] != entry) {
        entries[kept] = entry;
        slacks[kept++] = (int) pair;
      }
    }
    size = kept;
  }

  /** Removes all entries. */
  public void clear() {
    size = 0;
  }
}
