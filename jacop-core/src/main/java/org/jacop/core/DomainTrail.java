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

import java.util.Arrays;

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

  /** Per entry: kind, level, then the domain's values. */
  int[] ints = new int[INTS * 256];

  /** Per entry: a value of the domain. */
  long[] longs = new long[256];

  /** Per entry: the domain, then the domain's objects. */
  Object[] objects = new Object[OBJECTS * 256];

  private int size;

  /**
   * Pushes an entry; the caller fills in its values.
   *
   * @param domain the domain the entry belongs to.
   * @param kind the kind of the entry, read back by the domain.
   * @param level the level the entry belongs to.
   * @return the index of the entry.
   */
  int push(Entry domain, int kind, int level) {
    if (size == longs.length) {
      grow();
    }
    int entry = size++;
    ints[entry * INTS] = kind;
    ints[entry * INTS + 1] = level;
    objects[entry * OBJECTS] = domain;
    return entry;
  }

  private void grow() {
    if (size > (Integer.MAX_VALUE / INTS - 64) / 2) {
      throw new IllegalStateException("Trail too large");
    }
    int capacity = 2 * size + 64;
    ints = Arrays.copyOf(ints, capacity * INTS);
    longs = Arrays.copyOf(longs, capacity);
    objects = Arrays.copyOf(objects, capacity * OBJECTS);
  }

  /**
   * Pops the entries of the given level and of the levels above it, newest first.
   *
   * @param level the lowest level removed.
   */
  void removeLevel(int level) {
    while (size > 0 && ints[(size - 1) * INTS + 1] >= level) {
      int entry = --size;
      int o = entry * OBJECTS;
      ((Entry) objects[o]).undo(this, entry);
      objects[o] = null;
      objects[o + 1] = null;
      objects[o + 2] = null;
      objects[o + 3] = null;
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
