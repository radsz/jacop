/*
 * LiteralMap.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import java.util.Arrays;

/**
 * The literals of one variable by value: sorted values with their DIMACS variables, in two int
 * arrays. Literals are created far less often than looked up, so an insertion moves the tail.
 */
final class LiteralMap {

  /** Returned when there is no such value. */
  static final int NONE = 0;

  private int[] values = new int[4];
  private int[] literals = new int[4];
  private int size;

  /** Returns the DIMACS variable of value v, or {@link #NONE}. */
  int get(int v) {
    int k = Arrays.binarySearch(values, 0, size, v);
    return k >= 0 ? literals[k] : NONE;
  }

  /** Returns the DIMACS variable of the largest value below v, or {@link #NONE}. */
  int lower(int v) {
    int k = Arrays.binarySearch(values, 0, size, v);
    int below = (k >= 0 ? k : -k - 1) - 1;
    return below >= 0 ? literals[below] : NONE;
  }

  /** Returns the DIMACS variable of the smallest value above v, or {@link #NONE}. */
  int higher(int v) {
    int k = Arrays.binarySearch(values, 0, size, v);
    int above = k >= 0 ? k + 1 : -k - 1;
    return above < size ? literals[above] : NONE;
  }

  /** Adds value v, which must be absent, with its DIMACS variable (positive). */
  void put(int v, int literal) {
    int k = -Arrays.binarySearch(values, 0, size, v) - 1;
    if (size == values.length) {
      values = Arrays.copyOf(values, 2 * size);
      literals = Arrays.copyOf(literals, 2 * size);
    }
    System.arraycopy(values, k, values, k + 1, size - k);
    System.arraycopy(literals, k, literals, k + 1, size - k);
    values[k] = v;
    literals[k] = literal;
    size++;
  }
}
