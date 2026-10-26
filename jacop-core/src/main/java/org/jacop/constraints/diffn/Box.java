/*
 * Box.java This file is part of JaCoP.
 *
 * <p>JaCoP is a Java Constraint Programming solver.
 *
 * <p>Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * <p>This program is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Affero General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * <p>This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * <p>Notwithstanding any other provision of this License, the copyright owners of this work
 * supplement the terms of this License with terms prohibiting misrepresentation of the origin of
 * this work and requiring that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license terms is in accordance with
 * Section 7 of GNU Affero General Public License version 3.
 *
 * <p>You should have received a copy of the GNU Affero General Public License along with this
 * program. If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints.diffn;

import org.jacop.core.IntVar;

/**
 * A k-dimensional box of the {@link DiffnK} constraint: an origin and a length in each dimension.
 * Ends are computed as longs so that origin + length never overflows.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Box {

  final IntVar[] origin;
  final IntVar[] length;
  final int index;

  Box(IntVar[] origin, IntVar[] length, int index) {
    this.origin = origin;
    this.length = length;
    this.index = index;
  }

  int dimensions() {
    return origin.length;
  }

  /** Earliest start in dimension d. */
  long est(int d) {
    return origin[d].min();
  }

  /** Latest start in dimension d. */
  long lst(int d) {
    return origin[d].max();
  }

  /** Earliest end in dimension d (with the smallest length). */
  long ect(int d) {
    return (long) origin[d].min() + length[d].min();
  }

  /** Latest end in dimension d (with the largest length). */
  long lct(int d) {
    return (long) origin[d].max() + length[d].max();
  }

  /**
   * True if every length is certainly positive, so the box takes part in non-strict non-overlap.
   */
  boolean present() {
    for (IntVar l : length) {
      if (l.min() <= 0) {
        return false;
      }
    }
    return true;
  }

  /** True if every length can still be positive. */
  boolean mayBePresent() {
    for (IntVar l : length) {
      if (l.max() <= 0) {
        return false;
      }
    }
    return true;
  }

  /** The smallest positive value of the length in dimension d; requires length[d].max() > 0. */
  long minPositiveLength(int d) {
    IntVar l = length[d];
    return l.min() > 0 ? l.min() : l.domain.nextValue(0);
  }

  boolean singleton() {
    for (int d = 0; d < origin.length; d++) {
      if (!origin[d].singleton() || !length[d].singleton()) {
        return false;
      }
    }
    return true;
  }

  /** True if all variables of the box were fixed before the given store level. */
  boolean fixedBefore(int level) {
    for (int d = 0; d < origin.length; d++) {
      if (!origin[d].singleton()
          || !length[d].singleton()
          || origin[d].domain.stamp >= level
          || length[d].domain.stamp >= level) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder("[").append(index).append(": ");
    for (int d = 0; d < origin.length; d++) {
      result.append(origin[d]).append(", ");
    }
    for (int d = 0; d < length.length; d++) {
      result.append(length[d]);
      if (d < length.length - 1) {
        result.append(", ");
      }
    }
    return result.append("]").toString();
  }
}
