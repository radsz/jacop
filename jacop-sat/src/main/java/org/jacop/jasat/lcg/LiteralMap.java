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
 * arrays. Literals are created far less often than looked up, so an insertion moves the tail. Once
 * the values fill a sixteenth of a root domain of at most {@link #DENSE_SPAN} values, the map is
 * indexed by value instead, with a bit set of the values present for {@link #lower} and {@link
 * #higher}.
 */
final class LiteralMap {

  /** Returned when there is no such value. */
  static final int NONE = 0;

  /** The largest root domain indexed by value. */
  static final int DENSE_SPAN = 1 << 16;

  // values per entry of the root domain below which the map stays sorted
  private static final int DENSITY = 16;

  private static final int MIN_DENSE_SIZE = 8;

  private final int min;
  private final long span;

  // sorted form
  private int[] values = new int[4];
  private int[] literals = new int[4];
  private int size;

  // indexed form, null while sorted: the DIMACS variable of value min + k at k, and k in present
  private int[] byValue;
  private long[] present;

  /** A map for a variable whose root domain is within [min, max]. */
  LiteralMap(int min, int max) {
    this.min = min;
    this.span = (long) max - min + 1;
  }

  /** Returns the DIMACS variable of value v, or {@link #NONE}. */
  int get(int v) {
    if (byValue != null) {
      long k = (long) v - min;
      return k >= 0 && k < span ? byValue[(int) k] : NONE;
    }
    int k = Arrays.binarySearch(values, 0, size, v);
    return k >= 0 ? literals[k] : NONE;
  }

  /** Returns the DIMACS variable of the largest value below v, or {@link #NONE}. */
  int lower(int v) {
    if (byValue != null) {
      long k = Math.min((long) v - min, span) - 1;
      if (k < 0) {
        return NONE;
      }
      int w = (int) (k >>> 6);
      long word = present[w] & (-1L >>> (63 - (k & 63)));
      while (word == 0) {
        if (--w < 0) {
          return NONE;
        }
        word = present[w];
      }
      return byValue[(w << 6) + 63 - Long.numberOfLeadingZeros(word)];
    }
    int k = Arrays.binarySearch(values, 0, size, v);
    int below = (k >= 0 ? k : -k - 1) - 1;
    return below >= 0 ? literals[below] : NONE;
  }

  /** Returns the DIMACS variable of the smallest value above v, or {@link #NONE}. */
  int higher(int v) {
    if (byValue != null) {
      long k = Math.max((long) v - min + 1, 0);
      if (k >= span) {
        return NONE;
      }
      int w = (int) (k >>> 6);
      long word = present[w] & (-1L << (k & 63));
      while (word == 0) {
        if (++w == present.length) {
          return NONE;
        }
        word = present[w];
      }
      return byValue[(w << 6) + Long.numberOfTrailingZeros(word)];
    }
    int k = Arrays.binarySearch(values, 0, size, v);
    int above = k >= 0 ? k + 1 : -k - 1;
    return above < size ? literals[above] : NONE;
  }

  /** Adds value v of the root domain, which must be absent, with its DIMACS variable (positive). */
  void put(int v, int literal) {
    if (byValue != null) {
      int k = v - min;
      byValue[k] = literal;
      present[k >>> 6] |= 1L << k;
      return;
    }
    if (size == values.length) {
      if (size >= MIN_DENSE_SIZE && span <= DENSE_SPAN && span <= (long) DENSITY * size) {
        index();
        put(v, literal);
        return;
      }
      values = Arrays.copyOf(values, 2 * size);
      literals = Arrays.copyOf(literals, 2 * size);
    }
    int k = -Arrays.binarySearch(values, 0, size, v) - 1;
    System.arraycopy(values, k, values, k + 1, size - k);
    System.arraycopy(literals, k, literals, k + 1, size - k);
    values[k] = v;
    literals[k] = literal;
    size++;
  }

  /** Removes value v, which must be present. */
  void remove(int v) {
    if (byValue != null) {
      int k = v - min;
      byValue[k] = NONE;
      present[k >>> 6] &= ~(1L << k);
      return;
    }
    int k = Arrays.binarySearch(values, 0, size, v);
    size--;
    System.arraycopy(values, k + 1, values, k, size - k);
    System.arraycopy(literals, k + 1, literals, k, size - k);
  }

  /** Moves the entries to the indexed form. */
  private void index() {
    byValue = new int[(int) span];
    present = new long[(int) ((span + 63) >>> 6)];
    for (int i = 0; i < size; i++) {
      int k = values[i] - min;
      byValue[k] = literals[i];
      present[k >>> 6] |= 1L << k;
    }
    values = null;
    literals = null;
  }
}
