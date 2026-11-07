/*
 * VarIntMap.java
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
package org.jacop.util;

import org.jacop.core.Var;

/**
 * A map from variables, compared by identity and hashed by their store index, to non-negative ints,
 * such as the position of a variable in a constraint. It is meant for lookups on the hot path of a
 * constraint, such as {@code queueVariable}: keys and values are kept in flat arrays with open
 * addressing, so a lookup neither boxes nor follows a chain of map nodes.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class VarIntMap {

  /** The value returned for a variable that is not in the map. */
  public static final int ABSENT = -1;

  private Var[] keys;

  private int[] values;

  private int size;

  /** Creates an empty map. */
  public VarIntMap() {
    this(8);
  }

  /**
   * Creates an empty map with room for the given number of variables before it grows.
   *
   * @param expected the expected number of variables.
   */
  public VarIntMap(int expected) {
    int capacity = Integer.highestOneBit(Math.max(4, expected) * 2 - 1) << 1;
    keys = new Var[capacity];
    values = new int[capacity];
  }

  // the store index, unlike the identity hash, costs no header access and leaves the identity
  // hashes
  // of other objects, and so the iteration order of identity-based collections, unchanged
  private static int slot(Var v, int mask) {
    int h = v.index() * 0x9E3779B9;
    return (h ^ (h >>> 16)) & mask;
  }

  /**
   * Returns the value of a variable.
   *
   * @param v the variable.
   * @return the value, or {@link #ABSENT} if the variable is not in the map.
   */
  public int get(Var v) {
    Var[] k = keys;
    int mask = k.length - 1;
    int i = slot(v, mask);
    Var key;
    while ((key = k[i]) != null) {
      if (key == v) {
        return values[i];
      }
      i = (i + 1) & mask;
    }
    return ABSENT;
  }

  /**
   * Checks whether a variable is in the map.
   *
   * @param v the variable.
   * @return true if the variable has a value.
   */
  public boolean containsKey(Var v) {
    return get(v) != ABSENT;
  }

  /**
   * Sets the value of a variable.
   *
   * @param v the variable.
   * @param value the value, not negative.
   */
  public void put(Var v, int value) {
    if (value < 0) {
      throw new IllegalArgumentException("Negative value " + value);
    }
    if (2 * (size + 1) > keys.length) {
      grow();
    }
    int mask = keys.length - 1;
    int i = slot(v, mask);
    while (keys[i] != null) {
      if (keys[i] == v) {
        values[i] = value;
        return;
      }
      i = (i + 1) & mask;
    }
    keys[i] = v;
    values[i] = value;
    size++;
  }

  /**
   * Returns the number of variables in the map.
   *
   * @return the number of variables.
   */
  public int size() {
    return size;
  }

  private void grow() {
    Var[] oldKeys = keys;
    int[] oldValues = values;
    keys = new Var[oldKeys.length * 2];
    values = new int[oldKeys.length * 2];
    size = 0;
    for (int i = 0; i < oldKeys.length; i++) {
      if (oldKeys[i] != null) {
        put(oldKeys[i], oldValues[i]);
      }
    }
  }
}
