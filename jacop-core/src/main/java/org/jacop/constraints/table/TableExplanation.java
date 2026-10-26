/*
 * TableExplanation.java
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

package org.jacop.constraints.table;

import java.util.Arrays;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of a table of hybrid tuples. An atom of a column's variable holds because every
 * tuple that would allow a value the atom removes was dead before it: some other column's
 * restriction accepted only values already out of that column's domain, or the values it allows
 * there were out of the variable's own domain. A failure is explained by every tuple being dead.
 *
 * <p>Restrictions between columns never kill a tuple here, so a tuple kept alive only by such a
 * restriction makes the explanation refuse, and the generic reason is used.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class TableExplanation {

  /** The most values of one restriction checked one by one when killing a tuple. */
  private static final int VALUE_LIMIT = 256;

  private TableExplanation() {}

  /**
   * Adds to {@code out} the reason of an entry of one of the table's variables.
   *
   * @param trail the trail
   * @param entry the entry
   * @param x the variables of the columns
   * @param cells the restrictions, tuple t in {@code cells[t * arity ..]}
   * @param tupleCount the number of tuples
   * @param out where the reason entries are added
   * @return false when some tuple allowing a removed value is not dead before the entry
   */
  static boolean explain(
      AtomicTrail trail,
      int entry,
      IntVar[] x,
      Restriction[] cells,
      int tupleCount,
      EntryList out) {
    IntVar y = trail.variable(entry);
    int i = column(x, y);
    if (i < 0) {
      return false;
    }
    IntDomain root = trail.rootDomain(y);
    int a = trail.value(entry);
    // the values the atom removes, as a range [lo, hi], with a hole at a for a != atom
    int lo;
    int hi;
    switch (trail.kind(entry)) {
      case AtomicTrail.GE -> {
        lo = root.min();
        hi = a - 1;
      }
      case AtomicTrail.LE -> {
        lo = a + 1;
        hi = root.max();
      }
      default -> {
        lo = a;
        hi = a;
      }
    }
    int arity = x.length;
    int mark = out.size();
    EntryList scratch = new EntryList();
    int last = -1;
    for (int t = 0; t < tupleCount; t++) {
      int base = t * arity;
      Restriction own = cells[base + i];
      if (!overlaps(own, lo, hi)) {
        continue;
      }
      int killer = kill(trail, entry, x, cells, base, i, last, scratch, out);
      if (killer >= 0) {
        last = killer;
        continue;
      }
      // alive by the other columns: the values it allows in this column were already removed
      if (own.isBinary() || !excludedWithin(trail, entry, y, own, lo, hi, scratch, out)) {
        out.truncate(mark);
        return false;
      }
    }
    unique(out, mark);
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure: every tuple is dead.
   *
   * @param trail the trail
   * @param x the variables of the columns
   * @param cells the restrictions
   * @param tupleCount the number of tuples
   * @param out where the reason entries are added
   * @return false when some tuple is not dead now
   */
  static boolean explainFailure(
      AtomicTrail trail, IntVar[] x, Restriction[] cells, int tupleCount, EntryList out) {
    int arity = x.length;
    int mark = out.size();
    int now = trail.size();
    EntryList scratch = new EntryList();
    int last = -1;
    for (int t = 0; t < tupleCount; t++) {
      int killer = kill(trail, now, x, cells, t * arity, -1, last, scratch, out);
      if (killer < 0) {
        out.truncate(mark);
        return false;
      }
      last = killer;
    }
    unique(out, mark);
    return true;
  }

  private static int column(IntVar[] x, IntVar y) {
    for (int i = 0; i < x.length; i++) {
      if (x[i] == y) {
        return i;
      }
    }
    return -1;
  }

  /**
   * Finds a column other than {@code skip} whose restriction allowed no value of its variable
   * before a trail position, trying {@code first} first, and adds the entries that removed those
   * values to {@code out}.
   *
   * @return the column, or -1 when there is none
   */
  private static int kill(
      AtomicTrail trail,
      int position,
      IntVar[] x,
      Restriction[] cells,
      int base,
      int skip,
      int first,
      EntryList scratch,
      EntryList out) {
    int arity = x.length;
    if (first >= 0
        && first != skip
        && dead(trail, position, x[first], cells[base + first], scratch, out)) {
      return first;
    }
    for (int j = 0; j < arity; j++) {
      if (j != skip && j != first && dead(trail, position, x[j], cells[base + j], scratch, out)) {
        return j;
      }
    }
    return -1;
  }

  /** Whether r allowed no value of y before the position; if so its removals go to out. */
  private static boolean dead(
      AtomicTrail trail, int position, IntVar y, Restriction r, EntryList scratch, EntryList out) {
    if (r.kind == Restriction.Kind.ANY || r.isBinary()) {
      return false;
    }
    IntDomain root = trail.rootDomain(y);
    return excludedAccepted(trail, position, y, r, root.min(), root.max(), scratch, out);
  }

  /**
   * Whether the values r allows in this column within [lo, hi] were out of y's domain before the
   * entry; if so their removals go to out.
   */
  private static boolean excludedWithin(
      AtomicTrail trail,
      int entry,
      IntVar y,
      Restriction r,
      int lo,
      int hi,
      EntryList scratch,
      EntryList out) {
    return excludedAccepted(trail, entry, y, r, lo, hi, scratch, out);
  }

  /**
   * Whether every value in [lo, hi] that r accepts was out of y's domain before the position; if so
   * the entries that removed them are added to out.
   */
  private static boolean excludedAccepted(
      AtomicTrail trail,
      int position,
      IntVar y,
      Restriction r,
      int lo,
      int hi,
      EntryList scratch,
      EntryList out) {
    scratch.clear();
    boolean all =
        switch (r.kind) {
          case EQ ->
              r.value < lo
                  || r.value > hi
                  || excludedRange(trail, position, y, r.value, r.value, scratch);
          case NE ->
              excludedRange(trail, position, y, lo, Math.min(hi, r.value - 1), scratch)
                  && excludedRange(trail, position, y, Math.max(lo, r.value + 1), hi, scratch);
          case LE -> excludedRange(trail, position, y, lo, Math.min(hi, r.value), scratch);
          case GE -> excludedRange(trail, position, y, Math.max(lo, r.value), hi, scratch);
          case IN -> {
            boolean ok = true;
            for (int k = 0; k < r.values.length && ok; k++) {
              int v = r.values[k];
              ok = v < lo || v > hi || excludedRange(trail, position, y, v, v, scratch);
            }
            yield ok;
          }
          case NOT_IN -> {
            boolean ok = true;
            int from = lo;
            for (int k = 0; k <= r.values.length && ok; k++) {
              int to = k < r.values.length ? Math.min(hi, r.values[k] - 1) : hi;
              ok = excludedRange(trail, position, y, from, to, scratch);
              if (k < r.values.length) {
                from = Math.max(from, r.values[k] + 1);
              }
            }
            yield ok;
          }
          default -> excludedRange(trail, position, y, lo, hi, scratch);
        };
    if (all) {
      for (int k = 0; k < scratch.size(); k++) {
        out.add(scratch.get(k));
      }
    }
    return all;
  }

  /**
   * Whether every value of y's root domain in [lo, hi] was out of its domain before the position,
   * adding the entries that removed them to out: one bound entry when a bound passed the range,
   * otherwise one entry per value, for ranges of a few values.
   */
  private static boolean excludedRange(
      AtomicTrail trail, int position, IntVar y, int lo, int hi, EntryList out) {
    IntDomain root = trail.rootDomain(y);
    lo = Math.max(lo, root.min());
    hi = Math.min(hi, root.max());
    if (lo > hi) {
      return true;
    }
    if (trail.minBefore(y, position) > hi) {
      trail.addLowerBound(y, position, out);
      return true;
    }
    if (trail.maxBefore(y, position) < lo) {
      trail.addUpperBound(y, position, out);
      return true;
    }
    if ((long) hi - lo >= VALUE_LIMIT) {
      return false;
    }
    for (int v = lo; v <= hi; v++) {
      if (root.contains(v) && !trail.excludedBefore(y, v, position, out)) {
        return false;
      }
    }
    return true;
  }

  // whether r accepts some value in [lo, hi], ignoring holes
  private static boolean overlaps(Restriction r, int lo, int hi) {
    return switch (r.kind) {
      case EQ -> r.value >= lo && r.value <= hi;
      case NE -> lo < hi || r.value != lo;
      case LE -> r.value >= lo;
      case GE -> r.value <= hi;
      case IN -> {
        int k = Arrays.binarySearch(r.values, lo);
        int p = k >= 0 ? k : -k - 1;
        yield p < r.values.length && r.values[p] <= hi;
      }
      case NOT_IN -> {
        // some value of [lo, hi] is not listed
        int k = Arrays.binarySearch(r.values, lo);
        int p = k >= 0 ? k : -k - 1;
        long run = 0;
        for (int v = lo; p < r.values.length && r.values[p] == v && v <= hi; p++, v++) {
          run++;
        }
        yield run <= (long) hi - lo;
      }
      default -> true;
    };
  }

  // sorts the entries from mark on and removes repeated ones
  private static void unique(EntryList out, int mark) {
    int n = out.size() - mark;
    if (n < 2) {
      return;
    }
    int[] e = new int[n];
    for (int k = 0; k < n; k++) {
      e[k] = out.get(mark + k);
    }
    Arrays.sort(e);
    out.truncate(mark);
    for (int k = 0; k < n; k++) {
      if (k == 0 || e[k] != e[k - 1]) {
        out.add(e[k]);
      }
    }
  }
}
