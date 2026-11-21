/*
 * ElementVariableExplanation.java
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

import org.jacop.core.IntVar;

/**
 * Explanations of {@code list[index - offset - 1] = value} over a list of variables. An index value
 * goes when its list variable and the value are disjoint; a bound of the value holds because the
 * list variables at the remaining positions all respect it; with the index fixed, the value and the
 * chosen list variable are equal.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ElementVariableExplanation {

  // index values walked for one reason before giving up on it
  private static final int MAX_POSITIONS = 4096;

  private ElementVariableExplanation() {}

  /**
   * Adds to {@code out} the reason of an entry made by the constraint.
   *
   * @param trail the trail
   * @param entry the entry
   * @param index the index variable
   * @param list the list variables
   * @param value the value variable
   * @param offset the index offset: position j is index value j + 1 + offset
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  public static boolean explain(
      AtomicTrail trail,
      int entry,
      IntVar index,
      IntVar[] list,
      IntVar value,
      int offset,
      EntryList out) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    if (y == index) {
      return y != value && removedPositions(trail, entry, index, list, value, offset, out);
    }
    int lo = trail.minBefore(index, entry);
    if (lo == trail.maxBefore(index, entry)) {
      // the index was fixed: the value and the chosen list variable are equal
      int j = lo - 1 - offset;
      if (j < 0 || j >= list.length || y != value && y != list[j] || value == list[j]) {
        return false;
      }
      IntVar other = y == value ? list[j] : value;
      if (!ShiftExplanation.explain(trail, entry, y, other, 0, out)) {
        return false;
      }
      trail.addLowerBound(index, entry, out);
      trail.addUpperBound(index, entry, out);
      return true;
    }
    if (y == value && kind == AtomicTrail.NE) {
      return missingValue(trail, entry, index, list, value, offset, out);
    }
    if (y != value) {
      return false;
    }
    boolean ge = kind == AtomicTrail.GE;
    // the bound the remaining list variables give: the least of their minima, or largest maxima
    long bound = ge ? Long.MAX_VALUE : Long.MIN_VALUE;
    int hi = trail.maxBefore(index, entry);
    if ((long) hi - lo >= MAX_POSITIONS) {
      return false;
    }
    for (int v = lo; v <= hi; v++) {
      int j = v - 1 - offset;
      if (trail.excludedBefore(index, v, entry, out)) {
        continue;
      }
      if (j < 0 || j >= list.length || list[j] == value) {
        return false;
      }
      int mark = out.size();
      if (ShiftExplanation.disjointBefore(trail, entry, value, list[j], 0, out)) {
        continue;
      }
      out.truncate(mark);
      if (ge) {
        trail.addLowerBound(list[j], entry, out);
        bound = Math.min(bound, trail.minBefore(list[j], entry));
      } else {
        trail.addUpperBound(list[j], entry, out);
        bound = Math.max(bound, trail.maxBefore(list[j], entry));
      }
    }
    // the values between that bound and the entry's are holes of the value
    int a = trail.value(entry);
    if (ge ? bound < a && a - bound > MAX_POSITIONS : bound > a && bound - a > MAX_POSITIONS) {
      return false;
    }
    for (long u = bound; ge ? u < a : u > a; u += ge ? 1 : -1) {
      if (!trail.excludedBefore(value, (int) u, entry, out)) {
        return false;
      }
    }
    trail.addLowerBound(index, entry, out);
    trail.addUpperBound(index, entry, out);
    return true;
  }

  // a value removed from the value variable is missing from every list variable the index can
  // select
  private static boolean missingValue(
      AtomicTrail trail,
      int entry,
      IntVar index,
      IntVar[] list,
      IntVar value,
      int offset,
      EntryList out) {
    int a = trail.value(entry);
    int lo = trail.minBefore(index, entry);
    int hi = trail.maxBefore(index, entry);
    if (index == value || (long) hi - lo >= MAX_POSITIONS) {
      return false;
    }
    for (int v = lo; v <= hi; v++) {
      if (trail.excludedBefore(index, v, entry, out)) {
        continue;
      }
      int j = v - 1 - offset;
      if (j < 0 || j >= list.length || list[j] == value) {
        return false;
      }
      if (!trail.excludedBefore(list[j], a, entry, out)) {
        return false;
      }
    }
    trail.addLowerBound(index, entry, out);
    trail.addUpperBound(index, entry, out);
    return true;
  }

  /**
   * Adds to {@code out} the reason why the constraint has no solution now: every index value left
   * names a list variable disjoint from the value.
   *
   * @param trail the trail
   * @param index the index variable
   * @param list the list variables
   * @param value the value variable
   * @param offset the index offset
   * @param out where the reason entries are added
   * @return false when some index value is not excluded that way
   */
  public static boolean explainFailure(
      AtomicTrail trail, IntVar index, IntVar[] list, IntVar value, int offset, EntryList out) {
    int now = trail.size();
    int lo = trail.minBefore(index, now);
    int hi = trail.maxBefore(index, now);
    if (index == value || (long) hi - lo >= MAX_POSITIONS) {
      return false;
    }
    for (int v = lo; v <= hi; v++) {
      if (!trail.excludedBefore(index, v, now, out)
          && !disjoint(trail, now, v, list, value, offset, out)) {
        return false;
      }
    }
    trail.addLowerBound(index, now, out);
    trail.addUpperBound(index, now, out);
    return true;
  }

  // the index values an index entry removes are each excluded before it, or name a disjoint list
  // variable
  private static boolean removedPositions(
      AtomicTrail trail,
      int entry,
      IntVar index,
      IntVar[] list,
      IntVar value,
      int offset,
      EntryList out) {
    int a = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.NE -> disjoint(trail, entry, a, list, value, offset, out);
      case AtomicTrail.GE -> {
        int lo = trail.minBefore(index, entry);
        if ((long) a - lo > MAX_POSITIONS) {
          yield false;
        }
        for (int v = a - 1; v >= lo; v--) {
          if (!trail.excludedBefore(index, v, entry, out)
              && !disjoint(trail, entry, v, list, value, offset, out)) {
            yield false;
          }
        }
        trail.addLowerBound(index, entry, out);
        yield true;
      }
      default -> {
        int hi = trail.maxBefore(index, entry);
        if ((long) hi - a > MAX_POSITIONS) {
          yield false;
        }
        for (int v = a + 1; v <= hi; v++) {
          if (!trail.excludedBefore(index, v, entry, out)
              && !disjoint(trail, entry, v, list, value, offset, out)) {
            yield false;
          }
        }
        trail.addUpperBound(index, entry, out);
        yield true;
      }
    };
  }

  // index value v names no list variable, or one disjoint from the value
  private static boolean disjoint(
      AtomicTrail trail,
      int position,
      int v,
      IntVar[] list,
      IntVar value,
      int offset,
      EntryList out) {
    long j = (long) v - 1 - offset;
    if (j < 0 || j >= list.length) {
      return true;
    }
    if (list[(int) j] == value) {
      return false;
    }
    int mark = out.size();
    if (ShiftExplanation.disjointBefore(trail, position, value, list[(int) j], 0, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }
}
