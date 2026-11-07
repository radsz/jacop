/*
 * LazyBitSetDomainValueEnumeration.java
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
 * Enumerates the values of a lazy bit set domain as they were when the enumeration was created.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class LazyBitSetDomainValueEnumeration extends ValueEnumeration {

  private final int max;

  private final long[] bits;

  private final int base;

  private int current;

  /**
   * It creates an enumeration of the values min..max present in bits.
   *
   * @param min the first value.
   * @param max the last value.
   * @param bits the bits of the values, null if all values min..max are present; not changed while
   *     the enumeration is used.
   * @param base the value of the first bit.
   */
  LazyBitSetDomainValueEnumeration(int min, int max, long[] bits, int base) {
    this.max = max;
    this.bits = bits;
    this.base = base;
    this.current = min;
  }

  @Override
  public boolean hasMoreElements() {
    return current <= max;
  }

  @Override
  public int nextElement() {
    if (current > max) {
      throw new IllegalStateException("No more elements");
    }
    int result = current;
    current = result == max ? max + 1 : next(result + 1);
    return result;
  }

  private int next(int value) {
    if (bits == null) {
      return value;
    }
    int index = value - base;
    int word = index >>> 6;
    int lastWord = (max - base) >>> 6;
    long w = bits[word] & (-1L << index);
    while (w == 0) {
      if (++word > lastWord) {
        return max + 1;
      }
      w = bits[word];
    }
    int result = base + (word << 6) + Long.numberOfTrailingZeros(w);
    return result > max ? max + 1 : result;
  }

  @Override
  public void domainHasChanged() {
    // the enumeration works on a snapshot of the domain
  }
}
