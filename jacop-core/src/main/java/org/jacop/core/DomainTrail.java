/*
 * DomainTrail.java
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

/**
 * One trail shared by the domains of a store that are changed in place ({@link LazyBitSetDomain}).
 * A domain pushes an entry before its first change at a level, and the store pops the entries of a
 * level when it removes the level, giving each entry back to its domain.
 *
 * <p>Keeping the entries of all domains in one array, in the order they were made, makes saving and
 * restoring a sequential walk over memory, where a trail per domain would touch a separate array
 * per changed variable.
 *
 * <p>An entry has {@link #INTS} ints (a kind and the level, then values chosen by the domain), one
 * long and {@link #OBJECTS} objects (the domain, then objects chosen by the domain).
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class DomainTrail {

  /** A domain whose state is saved on a {@link DomainTrail}. */
  interface Entry {

    /**
     * Restores the state saved in an entry, which is being popped.
     *
     * @param trail the trail.
     * @param entry the index of the entry.
     */
    void undo(DomainTrail trail, int entry);
  }

  /** The number of ints of an entry. */
  static final int INTS = 8;

  /** The number of objects of an entry. */
  static final int OBJECTS = 4;

  /** The log of the number of entries of the first segment. */
  private static final int FIRST_SHIFT = 8;

  /** The number of entries of the first segment; segment s has FIRST << s entries. */
  private static final int FIRST = 1 << FIRST_SHIFT;

  /** The number of segments; the last one has 2^27 entries, so its ints still fit an array. */
  private static final int SEGMENTS = 20;

  /**
   * The entries are kept in segments of doubling size, so the trail grows without copying: on a
   * deep search the trail can hold millions of entries, and copying them into ever larger arrays
   * touches twice the memory they need.
   */
  private final int[][] ints = new int[SEGMENTS][];

  /** Per entry: a value of the domain. */
  private final long[][] longs = new long[SEGMENTS][];

  /** Per entry: the domain, then the domain's objects. */
  private final Object[][] objects = new Object[SEGMENTS][];

  private int size;

  /** The number of entries the allocated segments hold. */
  private int capacity;

  /**
   * Pushes an entry; the caller fills in its values.
   *
   * @param domain the domain the entry belongs to.
   * @param kind the kind of the entry, read back by the domain.
   * @param level the level the entry belongs to.
   * @return the index of the entry.
   */
  int push(Entry domain, int kind, int level) {
    if (size == capacity) {
      grow();
    }
    int entry = size++;
    int s = segment(entry);
    int i = offset(entry, s);
    int[] in = ints[s];
    in[i * INTS] = kind;
    in[i * INTS + 1] = level;
    objects[s][i * OBJECTS] = domain;
    return entry;
  }

  private void grow() {
    int s = segment(capacity);
    if (s >= SEGMENTS) {
      throw new IllegalStateException("Trail too large");
    }
    int n = FIRST << s;
    ints[s] = new int[n * INTS];
    longs[s] = new long[n];
    objects[s] = new Object[n * OBJECTS];
    capacity += n;
  }

  /**
   * The segment of an entry: segment s holds entries FIRST * (2^s - 1) to FIRST * (2^(s+1) - 1).
   */
  private static int segment(int entry) {
    return 31 - FIRST_SHIFT - Integer.numberOfLeadingZeros(entry + FIRST);
  }

  /** The position of an entry in its segment. */
  private static int offset(int entry, int segment) {
    return entry + FIRST - (FIRST << segment);
  }

  /**
   * Returns an int of an entry.
   *
   * @param entry the index of the entry.
   * @param k the index of the int, 0 for the kind and 1 for the level.
   * @return the int.
   */
  int getInt(int entry, int k) {
    int s = segment(entry);
    return ints[s][offset(entry, s) * INTS + k];
  }

  /**
   * Sets an int of an entry.
   *
   * @param entry the index of the entry.
   * @param k the index of the int, at least 2.
   * @param value the int.
   */
  void setInt(int entry, int k, int value) {
    int s = segment(entry);
    ints[s][offset(entry, s) * INTS + k] = value;
  }

  /**
   * Returns the long of an entry.
   *
   * @param entry the index of the entry.
   * @return the long.
   */
  long getLong(int entry) {
    int s = segment(entry);
    return longs[s][offset(entry, s)];
  }

  /**
   * Sets the long of an entry.
   *
   * @param entry the index of the entry.
   * @param value the long.
   */
  void setLong(int entry, long value) {
    int s = segment(entry);
    longs[s][offset(entry, s)] = value;
  }

  /**
   * Returns an object of an entry.
   *
   * @param entry the index of the entry.
   * @param k the index of the object, 0 for the domain.
   * @return the object.
   */
  Object getObject(int entry, int k) {
    int s = segment(entry);
    return objects[s][offset(entry, s) * OBJECTS + k];
  }

  /**
   * Sets an object of an entry.
   *
   * @param entry the index of the entry.
   * @param k the index of the object, at least 1.
   * @param value the object.
   */
  void setObject(int entry, int k, Object value) {
    int s = segment(entry);
    objects[s][offset(entry, s) * OBJECTS + k] = value;
  }

  /**
   * Pops the entries of the given level and of the levels above it, newest first.
   *
   * @param level the lowest level removed.
   */
  void removeLevel(int level) {
    // kept small so that it inlines into the store's backtracking, which most stores do without
    // ever pushing an entry
    if (size > 0) {
      pop(level);
    }
  }

  private void pop(int level) {
    while (size > 0) {
      int entry = size - 1;
      int s = segment(entry);
      int i = offset(entry, s);
      if (ints[s][i * INTS + 1] < level) {
        return;
      }
      size = entry;
      Object[] in = objects[s];
      int o = i * OBJECTS;
      ((Entry) in[o]).undo(this, entry);
      in[o] = null;
      in[o + 1] = null;
      in[o + 2] = null;
      in[o + 3] = null;
    }
  }

  /**
   * Returns the number of entries.
   *
   * @return the number of entries on the trail.
   */
  int size() {
    return size;
  }
}
