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
import java.util.HashMap;
import java.util.Map;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.DomainCover;
import org.jacop.lcg.EntryList;

/**
 * Explanations of {@link Values} (nvalue) under lazy clause generation, by variables whose
 * intervals are pairwise disjoint: k such variables take k different values. That explains a lower
 * bound of the count, a failure against its upper bound, and a value removed from a variable when
 * the count's upper bound is already reached by variables whose intervals miss that value. By the
 * union U of domains: the count is at most |U|, and when the other variables' domains have fewer
 * values together than the count's lower bound, a variable takes a value outside them. By a maximum
 * matching between the variables and their values, which bounds the count from above: the count's
 * upper bound, a failure against its lower bound, and a value whose taking would make the matching
 * smaller than the lower bound are explained by König's vertex cover of the matching (the domains
 * of the variables reachable from an unmatched one by alternating paths lie inside the values
 * reachable from them), as in the explanation of alldifferent by Hall sets (Downing, Feydy and
 * Stuckey, "Explaining alldifferent", ACSC 2012).
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
      if (trail.kind(entry) == AtomicTrail.LE) {
        // the variables have at most as many values as their domains together
        IntervalDomain union = union(entry, null);
        if (union != null
            && union.getSize() <= trail.value(entry)
            && within(union, entry, null, out)) {
          return true;
        }
        int mark = out.size();
        if (matchingCover(entry, null, null, trail.value(entry), out)) {
          return true;
        }
        out.truncate(mark);
        return false;
      }
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
    int bounded = out.size();
    // y takes a value in lo..hi only as a value of its own, one more than count's upper bound
    trail.addUpperBound(count, entry, out);
    if (lo <= hi && disjoint(trail.maxBefore(count, entry), entry, y, lo, hi, out)) {
      return true;
    }
    out.truncate(bounded);
    // the others' domains together have fewer values than count's lower bound, so y takes a value
    // outside them, and lo..hi is inside them
    IntervalDomain union = union(entry, y);
    if (lo <= hi
        && union != null
        && union.getSize() < trail.minBefore(count, entry)
        && removedInside(y, lo, hi, union, entry, out)
        && within(union, entry, y, out)) {
      trail.addLowerBound(count, entry, out);
      return true;
    }
    out.truncate(bounded);
    // with y in lo..hi a maximum matching between the variables and their values is smaller than
    // count's lower bound
    int[] removed =
        lo <= hi && (long) hi - lo < HOLES ? removedValues(y, lo, hi, entry, out) : null;
    if (removed != null
        && matchingCover(entry, y, removed, trail.minBefore(count, entry) - 1, out)) {
      trail.addLowerBound(count, entry, out);
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // the values of lo..hi that y had just before position, adding the reasons of the others to out
  private int[] removedValues(IntVar y, int lo, int hi, int position, EntryList out) {
    int[] values = new int[hi - lo + 1];
    int size = 0;
    for (int v = lo; v <= hi; v++) {
      if (!trail.excludedBefore(y, v, position, out)) {
        values[size++] = v;
      }
    }
    return size == 0 ? null : Arrays.copyOf(values, size);
  }

  /**
   * Adds the reason why the variables take at most bound different values: a maximum matching
   * between the variables and their values just before position (skip taking a value of skipValues
   * instead) has at most bound edges. By König's theorem the variables reachable from an unmatched
   * variable by alternating paths, Z, have their domains inside the values matched to them, V, and
   * |V| + (n - |Z|) is the size of the matching; the reason is that the domains of Z other than
   * skip lie inside V. False when the matching is larger or a domain is too wide.
   */
  private boolean matchingCover(
      int position, IntVar skip, int[] skipValues, int bound, EntryList out) {
    int n = list.length;
    if (bound >= n) {
      return false;
    }
    int[][] domains = new int[n][];
    int[] index = new int[0];
    int numberValues = 0;
    Map<Integer, Integer> valueIndex = new HashMap<>();
    EntryList ignored = new EntryList();
    for (int i = 0; i < n; i++) {
      int[] d;
      if (list[i] == skip) {
        d = skipValues;
      } else {
        int lo = trail.minBefore(list[i], position);
        int hi = trail.maxBefore(list[i], position);
        if ((long) hi - lo >= HOLES) {
          return false;
        }
        d = new int[hi - lo + 1];
        int size = 0;
        for (int v = lo; v <= hi; v++) {
          if (!trail.excludedBefore(list[i], v, position, ignored)) {
            d[size++] = v;
          }
        }
        d = Arrays.copyOf(d, size);
      }
      int[] ids = new int[d.length];
      for (int k = 0; k < d.length; k++) {
        Integer id = valueIndex.get(d[k]);
        if (id == null) {
          id = numberValues++;
          valueIndex.put(d[k], id);
        }
        ids[k] = id;
      }
      domains[i] = ids;
    }
    int[] mateOfValue = new int[numberValues];
    Arrays.fill(mateOfValue, -1);
    int[] mateOfVariable = new int[n];
    Arrays.fill(mateOfVariable, -1);
    int size = 0;
    int[] seen = new int[numberValues];
    int stamp = 0;
    for (int i = 0; i < n; i++) {
      stamp++;
      if (augment(i, domains, mateOfValue, mateOfVariable, seen, stamp)) {
        if (++size > bound) {
          return false;
        }
      }
    }
    // Z: the variables reachable from unmatched ones, and V: the values reachable from Z
    boolean[] inZ = new boolean[n];
    boolean[] inV = new boolean[numberValues];
    int[] queue = new int[n];
    int head = 0;
    int tail = 0;
    for (int i = 0; i < n; i++) {
      if (mateOfVariable[i] < 0) {
        inZ[i] = true;
        queue[tail++] = i;
      }
    }
    while (head < tail) {
      int i = queue[head++];
      for (int id : domains[i]) {
        if (!inV[id]) {
          inV[id] = true;
          int j = mateOfValue[id];
          if (j >= 0 && !inZ[j]) {
            inZ[j] = true;
            queue[tail++] = j;
          }
        }
      }
    }
    for (int i = 0; i < n; i++) {
      if (inZ[i] && list[i] != skip) {
        IntVar x = list[i];
        boolean covered =
            DomainCover.domain(
                trail,
                x,
                position,
                (v, o) -> {
                  Integer id = valueIndex.get(v);
                  return id != null && inV[id];
                },
                out);
        if (!covered) {
          return false;
        }
      }
    }
    return true;
  }

  // Kuhn's augmenting path from variable i
  private static boolean augment(
      int i, int[][] domains, int[] mateOfValue, int[] mateOfVariable, int[] seen, int stamp) {
    for (int id : domains[i]) {
      if (seen[id] != stamp) {
        seen[id] = stamp;
        if (mateOfValue[id] < 0
            || augment(mateOfValue[id], domains, mateOfValue, mateOfVariable, seen, stamp)) {
          mateOfValue[id] = i;
          mateOfVariable[i] = id;
          return true;
        }
      }
    }
    return false;
  }

  // the union of the domains of the variables other than skip just before position, or null when
  // it has more than HOLES values
  private IntervalDomain union(int position, IntVar skip) {
    IntervalDomain union = new IntervalDomain();
    for (IntVar x : list) {
      if (x == skip) {
        continue;
      }
      int lo = trail.minBefore(x, position);
      int hi = trail.maxBefore(x, position);
      if ((long) hi - lo >= HOLES) {
        return null;
      }
      for (int v = lo; v <= hi; v++) {
        if (!union.contains(v) && !trail.excludedBefore(x, v, position, new EntryList())) {
          union.unionAdapt(v, v);
        }
      }
      if (union.getSize() > HOLES) {
        return null;
      }
    }
    return union;
  }

  // the reason that the domains of the variables other than skip are inside union
  private boolean within(IntervalDomain union, int position, IntVar skip, EntryList out) {
    for (IntVar x : list) {
      if (x != skip && !DomainCover.domain(trail, x, position, (v, o) -> union.contains(v), out)) {
        return false;
      }
    }
    return true;
  }

  // whether every value of lo..hi that y had just before position is in union; y's own removals
  // of the others are already in out
  private boolean removedInside(
      IntVar y, int lo, int hi, IntervalDomain union, int position, EntryList out) {
    for (int v = lo; v <= hi; v++) {
      if (!union.contains(v) && !trail.excludedBefore(y, v, position, out)) {
        return false;
      }
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
    // fewer values in all the domains together than count's lower bound
    IntervalDomain union = union(position, null);
    if (union != null
        && union.getSize() < trail.minBefore(count, position)
        && within(union, position, null, out)) {
      trail.addLowerBound(count, position, out);
      return true;
    }
    out.truncate(mark);
    // a maximum matching smaller than count's lower bound
    if (matchingCover(position, null, null, trail.minBefore(count, position) - 1, out)) {
      trail.addLowerBound(count, position, out);
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
