/*
 * ArgExtremumExplanation.java
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of the index of the first maximum (or minimum) of a list. Values of the list are
 * read oriented, negated for the minimum, so that the extremum is always the largest. Position j is
 * the first maximum when every earlier variable is below x[j] and no later one above it, so
 *
 * <ul>
 *   <li>j is not the index when some i before j has {@code min x[i] >= max x[j]}, or some i after j
 *       has {@code min x[i] > max x[j]};
 *   <li>x[k] is not v when every index left either is k's own, already removed, or belongs to a
 *       variable whose maximum is too small to be above (after k) or at least (before k) v;
 *   <li>x[k] is below no v when k is the only index left and some other variable is too large for v
 *       to be above it (before k) or at least it (after k).
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ArgExtremumExplanation {

  /** The most removed values passed over one by one to reach one that was still in a domain. */
  private static final int VALUE_LIMIT = 256;

  private final AtomicTrail trail;
  private final IntVar[] list;
  private final IntVar index;
  private final int offset;
  private final boolean max;
  private final int position;

  ArgExtremumExplanation(
      AtomicTrail trail, IntVar[] list, IntVar index, int offset, boolean max, int position) {
    this.trail = trail;
    this.list = list;
    this.index = index;
    this.offset = offset;
    this.max = max;
    this.position = position;
  }

  /**
   * Adds to {@code out} the reason of an entry of the index or of a variable of the list.
   *
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when there is no reason of this kind
   */
  boolean explain(int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int a = trail.value(entry);
    int kind = trail.kind(entry);
    int mark = out.size();
    if (y == index) {
      if (explainIndex(kind, a, out)) {
        return true;
      }
      out.truncate(mark);
    }
    if (kind == AtomicTrail.NE) {
      return false;
    }
    // an upper bound in the oriented values
    boolean upper = (kind == AtomicTrail.LE) == max;
    int bound = max ? a : -a;
    for (int k = 0; k < list.length; k++) {
      if (list[k] != y) {
        continue;
      }
      boolean done =
          upper ? aboveImpossible(k, bound + 1, out) : belowImpossible(k, bound - 1, out);
      if (done) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  /**
   * Adds to {@code out} the reason of a failure: no index is left, or some variable has no value.
   *
   * @param out where the reason entries are added
   * @return false when there is no reason of this kind
   */
  boolean explainFailure(EntryList out) {
    int mark = out.size();
    if (indexesImpossible(Integer.MIN_VALUE, Integer.MAX_VALUE, out)) {
      return true;
    }
    out.truncate(mark);
    for (int k = 0; k < list.length; k++) {
      addLow(list[k], out);
      if (aboveImpossible(k, low(list[k]), out)) {
        return true;
      }
      out.truncate(mark);
      addHigh(list[k], out);
      if (belowImpossible(k, high(list[k]), out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  private boolean explainIndex(int kind, int a, EntryList out) {
    return switch (kind) {
      case AtomicTrail.GE -> indexesImpossible(Integer.MIN_VALUE, a - 1, out);
      case AtomicTrail.LE -> indexesImpossible(a + 1, Integer.MAX_VALUE, out);
      default -> indexesImpossible(a, a, out);
    };
  }

  // whether every index value in [lo, hi] was removed before, or names no position, or cannot be
  // the first extremum; the reasons go to out
  private boolean indexesImpossible(int lo, int hi, EntryList out) {
    int from = Math.max(lo, 1 + offset);
    int to = Math.min(hi, list.length + offset);
    int min = trail.minBefore(index, position);
    if (from < min) {
      trail.addLowerBound(index, position, out);
      from = min;
    }
    int maxIndex = trail.maxBefore(index, position);
    if (to > maxIndex) {
      trail.addUpperBound(index, position, out);
      to = maxIndex;
    }
    for (int v = from; v <= to; v++) {
      if (!trail.excludedBefore(index, v, position, out) && !notFirst(v - 1 - offset, out)) {
        return false;
      }
    }
    return true;
  }

  // whether position j cannot be the first extremum by one other variable
  private boolean notFirst(int j, EntryList out) {
    int best = high(list[j]);
    for (int i = 0; i < list.length; i++) {
      if (i != j && (i < j ? low(list[i]) >= best : low(list[i]) > best)) {
        addLow(list[i], out);
        addHigh(list[j], out);
        return true;
      }
    }
    return false;
  }

  // whether x[k] cannot take any oriented value from v up
  private boolean aboveImpossible(int k, int v, EntryList out) {
    v = firstKept(list[k], v, 1, out);
    if (v == Integer.MAX_VALUE) {
      return true;
    }
    if (v == Integer.MIN_VALUE) {
      return false;
    }
    for (int j = 0; j < list.length; j++) {
      int value = j + 1 + offset;
      if (j == k) {
        if (!trail.excludedBefore(index, value, position, out)) {
          return false;
        }
      } else if (j > k ? high(list[j]) <= v : high(list[j]) < v) {
        addHigh(list[j], out);
      } else if (!trail.excludedBefore(index, value, position, out)) {
        return false;
      }
    }
    return true;
  }

  // whether x[k] cannot take any oriented value from v down
  private boolean belowImpossible(int k, int v, EntryList out) {
    v = firstKept(list[k], v, -1, out);
    if (v == Integer.MIN_VALUE) {
      return true;
    }
    if (v == Integer.MAX_VALUE) {
      return false;
    }
    for (int j = 0; j < list.length; j++) {
      if (j != k && !trail.excludedBefore(index, j + 1 + offset, position, out)) {
        return false;
      }
    }
    if (trail.excludedBefore(index, k + 1 + offset, position, out)) {
      return true;
    }
    for (int i = 0; i < list.length; i++) {
      if (i != k && (i < k ? low(list[i]) >= v : low(list[i]) > v)) {
        addLow(list[i], out);
        return true;
      }
    }
    return false;
  }

  /**
   * Walks from oriented value v in direction step over values already out of x's domain (adding
   * their entries) and returns the first one in it; past the domain it returns MAX_VALUE going up
   * and MIN_VALUE going down, and the opposite when too many values are in the way.
   */
  private int firstKept(IntVar x, int v, int step, EntryList out) {
    int end = step > 0 ? high(x) : low(x);
    IntDomain root = trail.rootDomain(x);
    // values outside the initial domain need no atom, so they are skipped without counting
    boolean up = (step > 0) == max;
    for (int count = 0; step > 0 ? v <= end : v >= end; v += step) {
      int actual = max ? v : -v;
      if (!root.contains(actual)) {
        int nextRoot = up ? root.nextValue(actual) : root.previousValue(actual);
        if (nextRoot == actual) {
          break;
        }
        v = (max ? nextRoot : -nextRoot) - step;
        continue;
      }
      if (count++ == VALUE_LIMIT) {
        return step > 0 ? Integer.MIN_VALUE : Integer.MAX_VALUE;
      }
      if (!trail.excludedBefore(x, actual, position, out)) {
        return v;
      }
    }
    // beyond the bound the bound's entry removes the rest
    if (step > 0) {
      addHigh(x, out);
      return Integer.MAX_VALUE;
    }
    addLow(x, out);
    return Integer.MIN_VALUE;
  }

  private int high(IntVar x) {
    return max ? trail.maxBefore(x, position) : -trail.minBefore(x, position);
  }

  private int low(IntVar x) {
    return max ? trail.minBefore(x, position) : -trail.maxBefore(x, position);
  }

  private void addHigh(IntVar x, EntryList out) {
    if (max) {
      trail.addUpperBound(x, position, out);
    } else {
      trail.addLowerBound(x, position, out);
    }
  }

  private void addLow(IntVar x, EntryList out) {
    if (max) {
      trail.addLowerBound(x, position, out);
    } else {
      trail.addUpperBound(x, position, out);
    }
  }
}
