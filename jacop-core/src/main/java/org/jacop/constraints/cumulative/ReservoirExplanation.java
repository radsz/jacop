/*
 * ReservoirExplanation.java
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

package org.jacop.constraints.cumulative;

import java.util.Arrays;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explains the propagation of {@link Reservoir} for lazy clause generation by one argument, the
 * level just after an event x. Within a window [L, U] of x's time, the level after x is at most the
 * initial level plus x's change, the consumptions of the events surely at or before x and the
 * productions of the events not surely after x. When that is below the least level the window is
 * impossible (symmetrically with the largest level and the signs swapped). An event is surely at or
 * before x by a precedence of the constraint, by sharing x's time variable, or when its latest time
 * is at most L; surely after x by a precedence, or when its earliest time is above U.
 *
 * <p>Each pruning is the negation of such a window: {@code t >= v} rules out the window [L, v - 1]
 * of the event itself, or makes the event a consumption at or before another event x whose earliest
 * time is at least v - 1; {@code t <= v} rules out [v + 1, U], or makes the event a production
 * after an event x whose latest time is at most v. The bounds of the precedences between events are
 * explained by the bound they come from. Events whose change the window does not need are left out
 * of the reason, the smallest changes first, and the remaining bounds are lifted to the weakest
 * atoms on the trail that keep their event before or after x.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ReservoirExplanation {

  private final Reservoir reservoir;
  private final IntVar[] times;
  private final int[] changes;
  private final int n;

  // bounds of the times just before the explained position
  private final int[] lo;
  private final int[] hi;

  // the events the window needs a bound for: event, kind, change it accounts for, threshold
  private final int[] item;
  private final int[] itemKind;
  private final long[] itemValue;
  private final int[] itemThreshold;
  private final Integer[] order;
  private int items;

  // an event before x by its latest time at most L; after x by its earliest time above U; before
  // or after x through the anchor's bound
  private static final int BEFORE_BY_BOUND = 0;
  private static final int AFTER_BY_BOUND = 1;
  private static final int AFTER_THROUGH_ANCHOR = 2;

  ReservoirExplanation(Reservoir reservoir) {
    this.reservoir = reservoir;
    this.times = reservoir.times;
    this.changes = reservoir.changes;
    this.n = times.length;
    this.lo = new int[n];
    this.hi = new int[n];
    this.item = new int[n];
    this.itemKind = new int[n];
    this.itemValue = new long[n];
    this.itemThreshold = new int[n];
    this.order = new Integer[n];
  }

  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return false;
    }
    snapshot(trail, entry);
    IntVar y = trail.variable(entry);
    int v = trail.value(entry);
    boolean lower = kind == AtomicTrail.GE;
    int skipped = trail.skippedBound(entry);
    for (int e = 0; e < n; e++) {
      if (times[e] != y) {
        continue;
      }
      int mark = out.size();
      if (explainBound(trail, entry, e, lower, v, out)) {
        return true;
      }
      out.truncate(mark);
      if (skipped != v && explainBound(trail, entry, e, lower, skipped, out)) {
        trail.addSkippedHoles(entry, skipped, out);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!reservoir.feasible() || reservoir.initial < reservoir.min) {
      return true;
    }
    if (reservoir.initial > reservoir.max) {
      return true;
    }
    int position = trail.size();
    snapshot(trail, position);
    for (int[] p : reservoir.pairs()) {
      if ((long) lo[p[0]] + p[2] > hi[p[1]]) {
        int a =
            trail.addBoundReaching(times[p[0]], position, true, (long) hi[p[1]] - p[2] + 1, out);
        trail.addBoundReaching(times[p[1]], position, false, (long) a + p[2] - 1, out);
        return true;
      }
    }
    for (int x = 0; x < n; x++) {
      for (int sign = 1; sign >= -1; sign -= 2) {
        int mark = out.size();
        if (window(trail, position, x, sign, lo[x], true, hi[x], true, -1, -1, out)) {
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  // explains t_e >= v (lower) or t_e <= v
  private boolean explainBound(
      AtomicTrail trail, int entry, int e, boolean lower, int v, EntryList out) {
    int mark = out.size();
    // a precedence between events
    for (int[] p : reservoir.pairs()) {
      if (lower && p[1] == e && (long) lo[p[0]] + p[2] >= v) {
        trail.addBoundReaching(times[p[0]], entry, true, (long) v - p[2], out);
        return true;
      }
      if (!lower && p[0] == e && (long) hi[p[1]] - p[2] <= v) {
        trail.addBoundReaching(times[p[1]], entry, false, (long) v + p[2], out);
        return true;
      }
    }
    for (int sign = 1; sign >= -1; sign -= 2) {
      // the window of e's time that the bound rules out
      boolean done =
          lower
              ? window(trail, entry, e, sign, lo[e], true, v - 1L, false, -1, -1, out)
              : window(trail, entry, e, sign, v + 1L, false, hi[e], true, -1, -1, out);
      if (done) {
        return true;
      }
      out.truncate(mark);
    }
    // e at or before (after) another event x
    for (int x = 0; x < n; x++) {
      if (x == e || times[x] == times[e]) {
        continue;
      }
      if (lower ? lo[x] < v - 1L : hi[x] > v) {
        continue;
      }
      for (int sign = 1; sign >= -1; sign -= 2) {
        boolean done =
            lower
                ? window(trail, entry, x, sign, lo[x], true, hi[x], true, -1, e, out)
                : window(trail, entry, x, sign, lo[x], true, hi[x], true, e, -1, out);
        if (done) {
          // t_e <= v - 1 <= t_x, or t_x <= v < t_e
          if (lower) {
            trail.addBoundReaching(times[x], entry, true, v - 1L, out);
          } else {
            trail.addBoundReaching(times[x], entry, false, v, out);
          }
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  private void snapshot(AtomicTrail trail, int position) {
    for (int i = 0; i < n; i++) {
      lo[i] = trail.minBefore(times[i], position);
      hi[i] = trail.maxBefore(times[i], position);
    }
  }

  /**
   * Tells whether x's time cannot lie in [l, u]: the level just after x then leaves [min, max] for
   * sure. sign 1 checks the level against min, -1 against max. The event after (before) is an event
   * assumed after (at or before) x. citeL and citeU tell whether l and u are bounds of x to cite,
   * or come from the negated atom. On success adds the reason.
   */
  private boolean window(
      AtomicTrail trail,
      int position,
      int x,
      int sign,
      long l,
      boolean citeL,
      long u,
      boolean citeU,
      int after,
      int before,
      EntryList out) {
    if (l > u) {
      return false;
    }
    long bound = sign > 0 ? reservoir.min : -(long) reservoir.max;
    long level = (long) sign * reservoir.initial + (long) sign * changes[x];
    items = 0;
    for (int y = 0; y < n; y++) {
      long c = (long) sign * changes[y];
      if (y == x || c == 0) {
        continue;
      }
      if (c < 0) {
        // a consumption counts when it is surely at or before x
        if (y == before
            || reservoir.staticBefore(y, x)
            || (before >= 0 && reservoir.staticBefore(y, before))) {
          level += c;
        } else if (hi[y] <= l) {
          addItem(y, BEFORE_BY_BOUND, -c, 0);
          level += c;
        }
      } else {
        // a production counts unless it is surely after x
        if (y == after
            || reservoir.staticAfter(y, x)
            || (after >= 0 && reservoir.staticBefore(after, y))) {
          continue;
        }
        if (lo[y] > u) {
          addItem(y, AFTER_BY_BOUND, c, 0);
        } else if (after >= 0 && hi[after] <= lo[y]) {
          addItem(y, AFTER_THROUGH_ANCHOR, c, lo[y]);
        } else {
          level += c;
        }
      }
    }
    if (level >= bound) {
      return false;
    }
    // leave out the events the excess does not need, the smallest changes first
    long slack = bound - 1 - level;
    for (int k = 0; k < items; k++) {
      order[k] = k;
    }
    Arrays.sort(order, 0, items, (a, b) -> Long.compare(itemValue[a], itemValue[b]));
    long reachL = Long.MIN_VALUE;
    long reachU = Long.MAX_VALUE;
    for (int q = 0; q < items; q++) {
      int k = order[q];
      if (itemValue[k] <= slack) {
        slack -= itemValue[k];
        continue;
      }
      int y = item[k];
      switch (itemKind[k]) {
        case BEFORE_BY_BOUND -> {
          // t_y <= l <= t_x
          int got = trail.addBoundReaching(times[y], position, false, l, out);
          reachL = Math.max(reachL, got);
        }
        case AFTER_BY_BOUND -> {
          // t_y >= u + 1 > t_x
          int got = trail.addBoundReaching(times[y], position, true, u + 1, out);
          reachU = Math.min(reachU, got - 1L);
        }
        default -> {
          // t_y >= threshold >= t_after > t_x
          int t = itemThreshold[k];
          trail.addBoundReaching(times[y], position, true, t, out);
          trail.addBoundReaching(times[after], position, false, t, out);
        }
      }
    }
    if (citeL && reachL != Long.MIN_VALUE) {
      trail.addBoundReaching(times[x], position, true, reachL, out);
    }
    if (citeU && reachU != Long.MAX_VALUE) {
      trail.addBoundReaching(times[x], position, false, reachU, out);
    }
    return true;
  }

  private void addItem(int y, int kind, long value, int threshold) {
    item[items] = y;
    itemKind[items] = kind;
    itemValue[items] = value;
    itemThreshold[items] = threshold;
    items++;
  }
}
