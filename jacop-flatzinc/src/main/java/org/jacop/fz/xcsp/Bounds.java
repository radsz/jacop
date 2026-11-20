/*
 * Bounds.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in material modified versions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.xcsp;

/** Saturating long arithmetic for the bounds of introduced variables. */
final class Bounds {

  private Bounds() {}

  static long add(long x, long y) {
    long r = x + y;
    if (((x ^ r) & (y ^ r)) < 0) {
      return x > 0 ? Long.MAX_VALUE : Long.MIN_VALUE;
    }
    return r;
  }

  static long mul(long x, long y) {
    long hi = Math.multiplyHigh(x, y);
    long lo = x * y;
    if ((hi == 0 && lo >= 0) || (hi == -1 && lo < 0)) {
      return lo;
    }
    return (x < 0) == (y < 0) ? Long.MAX_VALUE : Long.MIN_VALUE;
  }

  static long abs(long x) {
    return x == Long.MIN_VALUE ? Long.MAX_VALUE : Math.abs(x);
  }

  /** Returns x to the power y (y >= 0), saturated. */
  static long pow(long x, long y) {
    long r = 1;
    for (long i = 0; i < y; i++) {
      r = mul(r, x);
      if (r == Long.MAX_VALUE || r == Long.MIN_VALUE || r == 0 || r == 1 && x == 1) {
        if (r == 1 && x == 1) {
          return 1;
        }
        if (r == 0) {
          return 0;
        }
        if (x < 0 && (y - i - 1) % 2 != 0) {
          return -r;
        }
        return r;
      }
    }
    return r;
  }
}
