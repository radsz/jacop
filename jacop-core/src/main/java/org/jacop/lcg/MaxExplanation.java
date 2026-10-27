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
 * variable left that can reach m, that variable and m are equal. When m is itself in the list the
 * constraint only says that m is at least every other variable, and is explained as such.
 *
 * <p>Each bound in a reason is given by the earliest atom on the trail that implies it, as CP-SAT
 * does when it relaxes a reason to the lowest trail index, and where several variables can give the
 * same bound, by the one whose atom is earliest. The learnt clause is then as general as the atoms
 * on the trail allow, and depends on the lowest decision levels they offer.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class MaxExplanation {

  // values walked for one reason before giving up on it
  private static final int MAX_VALUES = 4096;

  // the earliest-atom value of a bound that does not hold
  private static final int NONE = Integer.MAX_VALUE;

  private final AtomicTrail trail;
  private final IntVar[] list;
  private final IntVar m;
  private final boolean isMax;
  private final boolean inList;
  private final EntryList out;

  private MaxExplanation(AtomicTrail trail, IntVar[] list, IntVar m, boolean isMax, EntryList out) {
    this.trail = trail;
    this.list = list;
    this.m = m;
    this.isMax = isMax;
    this.out = out;
    boolean found = false;
    for (IntVar x : list) {
      found |= x == m;
    }
    this.inList = found;
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
   * @return false when there is no such reason
   */
  public static boolean explain(
      AtomicTrail trail, int entry, IntVar[] list, IntVar m, boolean isMax, EntryList out) {
    return new MaxExplanation(trail, list, m, isMax, out).entry(entry);
  }

  /**
   * Adds to {@code out} the reason why the constraint has no solution now.
   *
   * @param trail the trail
   * @param list the list
   * @param m the maximum (or minimum)
   * @param isMax true for the maximum, false for the minimum
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  public static boolean explainFailure(
      AtomicTrail trail, IntVar[] list, IntVar m, boolean isMax, EntryList out) {
    return new MaxExplanation(trail, list, m, isMax, out).failure();
  }

  private boolean entry(int entry) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE && y == m) {
      return false;
    }
    // the atom on mirrored values: an upper bound (m <= a) or a lower bound (m >= a)
    boolean upper = (kind == AtomicTrail.LE) == isMax;
    long a = isMax ? trail.value(entry) : -(long) trail.value(entry);
    if (y == m) {
      return upper ? maxAtMost(a, entry) : maxAtLeast(a, entry);
    }
    int mark = out.size();
    if (kind != AtomicTrail.NE && upper) {
      // y is at most m, and its values from a + 1 to m's high are out
      long top = high(m, entry);
      if (add(highAtMost(m, top, entry)) && excludedFrom(y, a + 1, top, entry)) {
        return true;
      }
      out.truncate(mark);
    }
    // y is the only variable that can reach m
    return !inList && othersBelow(y, entry) && ShiftExplanation.explain(trail, entry, y, m, 0, out);
  }

  // m >= a: a variable of the list at least a, or the largest low and m's values out up to a
  private boolean maxAtLeast(long a, int entry) {
    long largest = Long.MIN_VALUE;
    for (IntVar x : list) {
      if (x != m) {
        largest = Math.max(largest, low(x, entry));
      }
    }
    if (largest == Long.MIN_VALUE) {
      return false;
    }
    long b = Math.min(a, largest);
    return add(earliestLowAtLeast(b, entry)) && excludedFrom(m, b, a - 1, entry);
  }

  // m <= a: every variable of the list at most top, and m's values from a + 1 to top out
  private boolean maxAtMost(long a, int entry) {
    if (inList) {
      return false;
    }
    long top = Long.MIN_VALUE;
    for (IntVar x : list) {
      top = Math.max(top, high(x, entry));
    }
    return excludedFrom(m, a + 1, top, entry) && allAtMost(top, entry);
  }

  private boolean failure() {
    int now = trail.size();
    int mark = out.size();
    // nothing reaches m
    if (!inList && othersBelow(null, now)) {
      return true;
    }
    out.truncate(mark);
    // a variable above m
    if (variableAboveMax(now)) {
      return true;
    }
    out.truncate(mark);
    if (inList) {
      return false;
    }
    // no value of m between the largest low and the largest high of the list
    long largest = Long.MIN_VALUE;
    long top = Long.MIN_VALUE;
    for (IntVar x : list) {
      largest = Math.max(largest, low(x, now));
      top = Math.max(top, high(x, now));
    }
    if (excludedFrom(m, largest, top, now)
        && allAtMost(top, now)
        && add(earliestLowAtLeast(largest, now))) {
      return true;
    }
    out.truncate(mark);
    // the only variable that can reach m has no value of m
    for (IntVar x : list) {
      if (high(x, now) >= low(m, now)) {
        return othersBelow(x, now) && ShiftExplanation.disjointBefore(trail, now, x, m, 0, out);
      }
    }
    return false;
  }

  // a variable of the list is above m's high: x >= t and m <= t - 1 for t between the two, taking
  // the variable and t whose later atom is earliest
  private boolean variableAboveMax(int position) {
    long mHigh = high(m, position);
    int best = NONE;
    int bestX = NONE;
    int bestM = NONE;
    for (IntVar x : list) {
      long xLow = low(x, position);
      if (x == m || xLow <= mHigh) {
        continue;
      }
      for (long t : new long[] {xLow, mHigh + 1}) {
        int ex = lowAtLeast(x, t, position);
        int em = highAtMost(m, t - 1, position);
        if (Math.max(ex, em) < best) {
          best = Math.max(ex, em);
          bestX = ex;
          bestM = em;
        }
      }
    }
    return best != NONE && add(bestX) && add(bestM);
  }

  // every variable of the list but y is below m's low, before the position: the others at most
  // m's low - 1, which lifts their atoms, and m at its low
  private boolean othersBelow(IntVar y, int position) {
    long bottom = low(m, position);
    for (IntVar x : list) {
      if (x != y && !add(highAtMost(x, bottom - 1, position))) {
        return false;
      }
    }
    return add(lowAtLeast(m, bottom, position));
  }

  // every variable of the list at most top
  private boolean allAtMost(long top, int position) {
    for (IntVar x : list) {
      if (!add(highAtMost(x, top, position))) {
        return false;
      }
    }
    return true;
  }

  // the earliest atom by which a variable of the list other than m is at least b
  private int earliestLowAtLeast(long b, int position) {
    int best = NONE;
    for (IntVar x : list) {
      if (x != m) {
        best = Math.min(best, lowAtLeast(x, b, position));
      }
    }
    return best;
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

  // adds an earliest-atom entry; false when the bound does not hold
  private boolean add(int e) {
    if (e == NONE) {
      return false;
    }
    if (e >= 0) {
      out.add(e);
    }
    return true;
  }

  private long low(IntVar x, int position) {
    return isMax ? trail.minBefore(x, position) : -(long) trail.maxBefore(x, position);
  }

  private long high(IntVar x, int position) {
    return isMax ? trail.maxBefore(x, position) : -(long) trail.minBefore(x, position);
  }

  // the earliest atom giving the mirrored low of x at least v
  private int lowAtLeast(IntVar x, long v, int position) {
    return isMax
        ? trail.earliestLowerBound(x, v, position)
        : trail.earliestUpperBound(x, -v, position);
  }

  // the earliest atom giving the mirrored high of x at most v
  private int highAtMost(IntVar x, long v, int position) {
    return isMax
        ? trail.earliestUpperBound(x, v, position)
        : trail.earliestLowerBound(x, -v, position);
  }
}
