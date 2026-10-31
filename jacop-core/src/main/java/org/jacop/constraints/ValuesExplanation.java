/*
 * ValuesExplanation.java
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

package org.jacop.constraints;

import java.util.Arrays;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of {@link Values} (nvalue) under lazy clause generation, by variables whose
 * intervals are pairwise disjoint: k such variables take k different values. That explains a lower
 * bound of the count, a failure against its upper bound, and a value removed from a variable when
 * the count's upper bound is already reached by variables whose intervals miss that value. Bounds
 * the propagator derives from holes or from the matching have no explanation here.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
final class ValuesExplanation {

  // the most values of a removed range checked in the domain of a variable
  private static final int HOLES = 64;

  private final AtomicTrail trail;
  private final IntVar[] list;
  private final IntVar count;

  /**
   * Prepares explanations of a Values constraint.
   *
   * @param trail the trail
   * @param list the variables
   * @param count the number of different values
   */
  ValuesExplanation(AtomicTrail trail, IntVar[] list, IntVar count) {
    this.trail = trail;
    this.list = list;
    this.count = count;
  }

  /**
   * Adds to {@code out} the reason of an entry of the count or of a variable.
   *
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when there is no reason of this kind
   */
  boolean explain(int entry, EntryList out) {
    if (countInList()) {
      return false;
    }
    IntVar y = trail.variable(entry);
    if (y == count) {
      return trail.kind(entry) == AtomicTrail.GE
          && disjoint(trail.value(entry), entry, null, 1, 0, out);
    }
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    int mark = out.size();
    int min = trail.minBefore(y, entry);
    if (lo < min) {
      trail.addLowerBound(y, entry, out);
      lo = min;
    }
    int max = trail.maxBefore(y, entry);
    if (hi > max) {
      trail.addUpperBound(y, entry, out);
      hi = max;
    }
    // the values of lo..hi at its ends already removed were skipped by a bound
    while (lo < hi && trail.excludedBefore(y, lo, entry, out)) {
      lo++;
    }
    while (hi > lo && trail.excludedBefore(y, hi, entry, out)) {
      hi--;
    }
    // y takes a value in lo..hi only as a value of its own, one more than count's upper bound
    trail.addUpperBound(count, entry, out);
    if (lo > hi || !disjoint(trail.maxBefore(count, entry), entry, y, lo, hi, out)) {
      out.truncate(mark);
      return false;
    }
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure: more variables with disjoint intervals than the
   * count's upper bound.
   *
   * @param out where the reason entries are added
   * @return false when the failure has another cause
   */
  boolean explainFailure(EntryList out) {
    if (countInList()) {
      return false;
    }
    int position = trail.size();
    int max = trail.maxBefore(count, position);
    int mark = out.size();
    trail.addUpperBound(count, position, out);
    if (max < list.length && disjoint(max + 1, position, null, 1, 0, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  /**
   * Adds the reason why the variables other than skip take at least k different values outside
   * lo..hi (an empty range excludes nothing); false when that has no reason here. It is either k
   * variables whose intervals are pairwise disjoint and miss lo..hi, or, as the propagator counts,
   * the different values of the fixed variables plus variables whose domains miss those values and
   * whose intervals are pairwise disjoint.
   */
  private boolean disjoint(int k, int position, IntVar skip, int lo, int hi, EntryList out) {
    if (k <= 0) {
      return true;
    }
    int n = list.length;
    int[] mins = new int[n];
    int[] maxs = new int[n];
    for (int i = 0; i < n; i++) {
      mins[i] = trail.minBefore(list[i], position);
      maxs[i] = trail.maxBefore(list[i], position);
    }
    boolean[] candidate = new boolean[n];
    for (int i = 0; i < n; i++) {
      candidate[i] = list[i] != skip && (lo > hi || mins[i] > hi || maxs[i] < lo);
    }
    int[] chosen = greedy(candidate, mins, maxs, k);
    if (chosen.length >= k) {
      for (int i : chosen) {
        trail.addLowerBound(list[i], position, out);
        trail.addUpperBound(list[i], position, out);
      }
      return true;
    }
    // the different values of the fixed variables, outside lo..hi
    int[] fixedOwner = new int[n];
    int[] fixedValues = new int[n];
    int numberFixed = 0;
    for (int i = 0; i < n; i++) {
      int v = mins[i];
      if (list[i] != skip
          && v == maxs[i]
          && (v < lo || v > hi)
          && indexOf(fixedValues, numberFixed, v) < 0) {
        fixedOwner[numberFixed] = i;
        fixedValues[numberFixed++] = v;
      }
    }
    if (numberFixed == 0) {
      return false;
    }
    EntryList ignored = new EntryList();
    for (int i = 0; i < n; i++) {
      candidate[i] =
          list[i] != skip
              && mins[i] != maxs[i]
              && misses(i, mins[i], maxs[i], fixedValues, numberFixed, lo, hi, position, ignored);
    }
    int needed = Math.max(0, k - numberFixed);
    chosen = greedy(candidate, mins, maxs, needed);
    if (chosen.length < needed) {
      return false;
    }
    for (int f = 0; f < numberFixed && f < k; f++) {
      int i = fixedOwner[f];
      trail.addLowerBound(list[i], position, out);
      trail.addUpperBound(list[i], position, out);
    }
    for (int i : chosen) {
      trail.addLowerBound(list[i], position, out);
      trail.addUpperBound(list[i], position, out);
      misses(i, mins[i], maxs[i], fixedValues, numberFixed, lo, hi, position, out);
    }
    return true;
  }

  /**
   * Picks up to k candidates whose intervals are pairwise disjoint, greedily by their maximum,
   * which finds the most.
   */
  private static int[] greedy(boolean[] candidate, int[] mins, int[] maxs, int k) {
    int n = candidate.length;
    long[] intervals = new long[n];
    int size = 0;
    for (int i = 0; i < n; i++) {
      if (candidate[i]) {
        // sorted by the maximum, then by the index
        intervals[size++] = ((long) maxs[i] << 32) | i;
      }
    }
    Arrays.sort(intervals, 0, size);
    int[] chosen = new int[Math.min(k, size)];
    int found = 0;
    long last = Long.MIN_VALUE;
    for (int j = 0; j < size && found < chosen.length; j++) {
      int i = (int) intervals[j];
      if (mins[i] > last) {
        chosen[found++] = i;
        last = maxs[i];
      }
    }
    return Arrays.copyOf(chosen, found);
  }

  /**
   * Tells whether variable i had none of the fixed values and no value of lo..hi before the
   * position, adding the removals inside its interval to {@code out}. At most HOLES values of
   * lo..hi are checked.
   */
  private boolean misses(
      int i,
      int min,
      int max,
      int[] fixedValues,
      int numberFixed,
      int lo,
      int hi,
      int position,
      EntryList out) {
    IntVar x = list[i];
    for (int f = 0; f < numberFixed; f++) {
      int v = fixedValues[f];
      if (v >= min && v <= max && !trail.excludedBefore(x, v, position, out)) {
        return false;
      }
    }
    int from = Math.max(lo, min);
    int to = Math.min(hi, max);
    if (from <= to && (long) to - from >= HOLES) {
      return false;
    }
    for (int v = from; v <= to; v++) {
      if (indexOf(fixedValues, numberFixed, v) < 0 && !trail.excludedBefore(x, v, position, out)) {
        return false;
      }
    }
    return true;
  }

  private static int indexOf(int[] values, int size, int v) {
    for (int f = 0; f < size; f++) {
      if (values[f] == v) {
        return f;
      }
    }
    return -1;
  }

  private boolean countInList() {
    for (IntVar x : list) {
      if (x == count) {
        return true;
      }
    }
    return false;
  }
}
