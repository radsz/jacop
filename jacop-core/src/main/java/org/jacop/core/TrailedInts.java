/*
 * TrailedInts.java
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
import org.jacop.api.Stateful;

/**
 * A fixed number of int values that are restored when the store backtracks. The first change at a
 * level saves all values once, so a constraint keeps several counters with one entry per level and
 * one call per removed level, without boxing them as {@link TimeStamp} does.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class TrailedInts implements Stateful {

  private final Store store;

  private final int[] values;

  /** Entries of the level at which the values changed, followed by the values before the change. */
  private int[] trail;

  private int size;

  /**
   * Creates the values, all zero, and registers them in the store.
   *
   * @param store the store whose levels the values follow.
   * @param n the number of values.
   */
  public TrailedInts(Store store, int n) {
    this.store = store;
    this.values = new int[n];
    this.trail = new int[8 * (n + 1)];
    store.putMutableVar(this);
  }

  /**
   * Returns a value.
   *
   * @param i the index of the value.
   * @return the current value.
   */
  public int get(int i) {
    return values[i];
  }

  /**
   * Sets a value at the current level of the store.
   *
   * @param i the index of the value.
   * @param value the new value.
   */
  public void set(int i, int value) {
    if (values[i] != value) {
      save();
      values[i] = value;
    }
  }

  private void save() {
    int entry = values.length + 1;
    int level = store.level;
    if (size > 0 && trail[size - entry] == level) {
      return;
    }
    if (size == trail.length) {
      trail = Arrays.copyOf(trail, 2 * size);
    }
    trail[size] = level;
    System.arraycopy(values, 0, trail, size + 1, values.length);
    size += entry;
  }

  @Override
  public void removeLevel(int level) {
    int entry = values.length + 1;
    while (size > 0 && trail[size - entry] >= level) {
      size -= entry;
      System.arraycopy(trail, size + 1, values, 0, values.length);
    }
  }

  @Override
  public String toString() {
    return "TrailedInts" + Arrays.toString(values);
  }
}
