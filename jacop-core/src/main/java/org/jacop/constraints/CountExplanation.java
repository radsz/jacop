/*
 * CountExplanation.java
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

import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of the number of variables of a list equal to a value, kept within a counter's
 * bounds (a variable, or two constants).
 *
 * <ul>
 *   <li>the counter is at least k when k variables are fixed to the value, and at most k when all
 *       but k cannot take it;
 *   <li>a variable takes the value when the counter is at least m and all but m - 1 of the other
 *       variables cannot take it, and loses it when the counter is at most m and m others are fixed
 *       to it;
 *   <li>a failure is more variables fixed to the value than the counter's maximum, or fewer that
 *       can take it than its minimum.
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CountExplanation {

  // the most holes cited next to a removed counted value
  private static final int HOLES = 64;

  private final AtomicTrail trail;
  private final IntVar[] list;
  private final int value;
  private final IntVar counter;
  private final int lb;
  private final int ub;
  private final int position;

  /**
   * Prepares explanations just before a trail position.
   *
   * @param trail the trail
   * @param list the counted variables
   * @param value the counted value
   * @param counter the counter, or null for the constant bounds
   * @param lb the least count when there is no counter
   * @param ub the largest count when there is no counter
   * @param position the trail position
   */
  CountExplanation(
      AtomicTrail trail, IntVar[] list, int value, IntVar counter, int lb, int ub, int position) {
    this.trail = trail;
    this.list = list;
    this.value = value;
    this.counter = counter;
    this.lb = lb;
    this.ub = ub;
    this.position = position;
  }

  /**
   * Adds to {@code out} the reason of an entry of the counter or of a counted variable.
   *
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when there is no reason of this kind
   */
  boolean explain(int entry, EntryList out) {
    if (counterInList()) {
      return false;
    }
    IntVar y = trail.variable(entry);
    int a = trail.value(entry);
    int kind = trail.kind(entry);
    if (y == counter) {
      return switch (kind) {
        case AtomicTrail.GE -> counterAtLeast(a, out);
        case AtomicTrail.LE -> counterAtMost(a, out);
        default -> false;
      };
    }
    int occurrences = 0;
    for (IntVar x : list) {
      if (x == y) {
        occurrences++;
      }
    }
    if (occurrences != 1) {
      return false;
    }
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    int mark = out.size();
    // values beyond the bounds y had were removed by those bounds' entries
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
    boolean removesValue = lo <= value && value <= hi;
    boolean removesOther = (lo < value || hi > value) && !onlyHolesBesides(y, lo, hi, entry, out);
    if (removesOther) {
      // y = value: the counter's minimum needs every other variable that can take the value
      addCounterMin(out);
      if (!excluded(list.length - counterMin(), y, out)) {
        out.truncate(mark);
        return false;
      }
    }
    if (removesValue) {
      // y != value: the counter's maximum is reached by others fixed to the value
      addCounterMax(out);
      if (!fixed(counterMax(), y, out)) {
        out.truncate(mark);
        return false;
      }
    }
    return true;
  }

  /**
   * Tells whether every value of lo..hi other than the counted one was removed from y before the
   * entry, adding the removals to {@code out}: a bound moved past the counted value skips the holes
   * next to it, and only the counted value is removed.
   */
  private boolean onlyHolesBesides(IntVar y, int lo, int hi, int entry, EntryList out) {
    if (lo > value || hi < value || (long) hi - lo > HOLES) {
      return false;
    }
    int mark = out.size();
    for (int v = lo; v <= hi; v++) {
      if (v != value && !trail.excludedBefore(y, v, entry, out)) {
        out.truncate(mark);
        return false;
      }
    }
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure.
   *
   * @param out where the reason entries are added
   * @return false when the counts and the counter's bounds do not conflict
   */
  boolean explainFailure(EntryList out) {
    if (counterInList()) {
      return false;
    }
    int mark = out.size();
    int max = counterMax();
    if (max < list.length) {
      addCounterMax(out);
      if (fixed(max + 1, null, out)) {
        return true;
      }
      out.truncate(mark);
    }
    int min = counterMin();
    if (min > 0) {
      addCounterMin(out);
      if (excluded(list.length - min + 1, null, out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // the counter is at least a: the variables fixed to the value, and the counter's holes up to a
  private boolean counterAtLeast(int a, EntryList out) {
    int count = 0;
    for (IntVar x : list) {
      if (trail.minBefore(x, position) == value && trail.maxBefore(x, position) == value) {
        count++;
      }
    }
    int k = Math.min(a, count);
    for (int v = k; v < a; v++) {
      if (!trail.excludedBefore(counter, v, position, out)) {
        return false;
      }
    }
    return fixed(k, null, out);
  }

  // the counter is at most a: the variables that cannot take the value, and the counter's holes
  private boolean counterAtMost(int a, EntryList out) {
    EntryList scratch = new EntryList();
    int count = 0;
    for (IntVar x : list) {
      if (trail.excludedBefore(x, value, position, scratch)) {
        count++;
      }
    }
    int k = Math.max(a, list.length - count);
    for (int v = a + 1; v <= k; v++) {
      if (!trail.excludedBefore(counter, v, position, out)) {
        return false;
      }
    }
    return excluded(list.length - k, null, out);
  }

  /** Adds the bounds of k variables other than skip fixed to the value; false when fewer are. */
  private boolean fixed(int k, IntVar skip, EntryList out) {
    int found = 0;
    for (int i = 0; i < list.length && found < k; i++) {
      IntVar x = list[i];
      if (x != skip
          && trail.minBefore(x, position) == value
          && trail.maxBefore(x, position) == value) {
        trail.addLowerBound(x, position, out);
        trail.addUpperBound(x, position, out);
        found++;
      }
    }
    return found >= k;
  }

  /** Adds why k variables other than skip cannot take the value; false when fewer cannot. */
  private boolean excluded(int k, IntVar skip, EntryList out) {
    int found = 0;
    for (int i = 0; i < list.length && found < k; i++) {
      IntVar x = list[i];
      if (x != skip && trail.excludedBefore(x, value, position, out)) {
        found++;
      }
    }
    return found >= k;
  }

  // a counter that is also counted changes the count with its own value; not explained here
  private boolean counterInList() {
    for (IntVar x : list) {
      if (x == counter) {
        return true;
      }
    }
    return false;
  }

  private int counterMin() {
    return counter != null ? trail.minBefore(counter, position) : lb;
  }

  private int counterMax() {
    return counter != null ? trail.maxBefore(counter, position) : ub;
  }

  private void addCounterMin(EntryList out) {
    if (counter != null) {
      trail.addLowerBound(counter, position, out);
    }
  }

  private void addCounterMax(EntryList out) {
    if (counter != null) {
      trail.addUpperBound(counter, position, out);
    }
  }
}
