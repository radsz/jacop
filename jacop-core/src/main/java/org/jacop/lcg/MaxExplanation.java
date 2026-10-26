/*
 * MaxExplanation.java
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
 * Explanations of {@code m = max(list)}, and of {@code m = min(list)} through the mirrored values.
 * A bound of m comes from the bounds of the list; a variable of the list is bounded by m; with one
 * variable left that can reach m, that variable and m are equal.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class MaxExplanation {

  // values walked for one reason before giving up on it
  private static final int MAX_VALUES = 4096;

  private final AtomicTrail trail;
  private final boolean isMax;
  private final EntryList out;

  private MaxExplanation(AtomicTrail trail, boolean isMax, EntryList out) {
    this.trail = trail;
    this.isMax = isMax;
    this.out = out;
  }

  /**
   * Adds to {@code out} the reason of an entry made by the constraint.
   *
   * @param trail the trail
   * @param entry the entry
   * @param list the list
   * @param m the maximum (or minimum)
   * @param isMax true for the maximum, false for the minimum
   * @param out where the reason entries are added
   * @return false when there is no such reason, or m is in the list
   */
  public static boolean explain(
      AtomicTrail trail, int entry, IntVar[] list, IntVar m, boolean isMax, EntryList out) {
    return !contains(list, m) && new MaxExplanation(trail, isMax, out).entry(entry, list, m);
  }

  /**
   * Adds to {@code out} the reason why the constraint has no solution now.
   *
   * @param trail the trail
   * @param list the list
   * @param m the maximum (or minimum)
   * @param isMax true for the maximum, false for the minimum
   * @param out where the reason entries are added
   * @return false when there is no such reason, or m is in the list
   */
  public static boolean explainFailure(
      AtomicTrail trail, IntVar[] list, IntVar m, boolean isMax, EntryList out) {
    return !contains(list, m) && new MaxExplanation(trail, isMax, out).failure(list, m);
  }

  private static boolean contains(IntVar[] list, IntVar m) {
    for (IntVar x : list) {
      if (x == m) {
        return true;
      }
    }
    return false;
  }

  private boolean entry(int entry, IntVar[] list, IntVar m) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE && y == m) {
      return false;
    }
    // the atom on mirrored values: an upper bound (m <= a) or a lower bound (m >= a)
    boolean upper = (kind == AtomicTrail.LE) == isMax;
    long a = isMax ? trail.value(entry) : -(long) trail.value(entry);
    if (y == m) {
      if (!upper) {
        int j = largestLow(list, entry);
        addLow(list[j], entry);
        return excludedFrom(m, low(list[j], entry), a - 1, entry);
      }
      long top = Long.MIN_VALUE;
      for (IntVar x : list) {
        addHigh(x, entry);
        top = Math.max(top, high(x, entry));
      }
      return excludedFrom(m, a + 1, top, entry);
    }
    int mark = out.size();
    if (kind != AtomicTrail.NE && upper) {
      addHigh(m, entry);
      if (excludedFrom(y, a + 1, high(m, entry), entry)) {
        return true;
      }
      out.truncate(mark);
    }
    // y is the only variable that can reach m
    if (!othersBelow(list, y, m, entry)) {
      return false;
    }
    return ShiftExplanation.explain(trail, entry, y, m, 0, out);
  }

  private boolean failure(IntVar[] list, IntVar m) {
    int now = trail.size();
    int mark = out.size();
    // nothing reaches m
    if (othersBelow(list, null, m, now)) {
      return true;
    }
    out.truncate(mark);
    // a variable above m
    for (IntVar x : list) {
      if (low(x, now) > high(m, now)) {
        addLow(x, now);
        addHigh(m, now);
        return true;
      }
    }
    // no value of m between the largest low and the largest high of the list
    int j = largestLow(list, now);
    long top = Long.MIN_VALUE;
    for (IntVar x : list) {
      addHigh(x, now);
      top = Math.max(top, high(x, now));
    }
    addLow(list[j], now);
    if (excludedFrom(m, low(list[j], now), top, now)) {
      return true;
    }
    out.truncate(mark);
    // the only variable that can reach m has no value of m
    for (IntVar x : list) {
      if (high(x, now) >= low(m, now)) {
        return othersBelow(list, x, m, now)
            && ShiftExplanation.disjointBefore(trail, now, x, m, 0, out);
      }
    }
    return false;
  }

  // every variable of the list but y is below m's low, before the position
  private boolean othersBelow(IntVar[] list, IntVar y, IntVar m, int position) {
    long bottom = low(m, position);
    for (IntVar x : list) {
      if (x == y) {
        continue;
      }
      if (high(x, position) >= bottom) {
        return false;
      }
      addHigh(x, position);
    }
    addLow(m, position);
    return true;
  }

  // the mirrored values from..to are out of x's domain before the position
  private boolean excludedFrom(IntVar x, long from, long to, int position) {
    if (to - from >= MAX_VALUES) {
      return false;
    }
    for (long u = from; u <= to; u++) {
      long v = isMax ? u : -u;
      if (v >= Integer.MIN_VALUE
          && v <= Integer.MAX_VALUE
          && !trail.excludedBefore(x, (int) v, position, out)) {
        return false;
      }
    }
    return true;
  }

  private int largestLow(IntVar[] list, int position) {
    int j = 0;
    for (int i = 1; i < list.length; i++) {
      if (low(list[i], position) > low(list[j], position)) {
        j = i;
      }
    }
    return j;
  }

  private long low(IntVar x, int position) {
    return isMax ? trail.minBefore(x, position) : -(long) trail.maxBefore(x, position);
  }

  private long high(IntVar x, int position) {
    return isMax ? trail.maxBefore(x, position) : -(long) trail.minBefore(x, position);
  }

  private void addLow(IntVar x, int position) {
    if (isMax) {
      trail.addLowerBound(x, position, out);
    } else {
      trail.addUpperBound(x, position, out);
    }
  }

  private void addHigh(IntVar x, int position) {
    if (isMax) {
      trail.addUpperBound(x, position, out);
    } else {
      trail.addLowerBound(x, position, out);
    }
  }
}
