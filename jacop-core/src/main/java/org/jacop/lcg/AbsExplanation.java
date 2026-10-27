/*
 * AbsExplanation.java
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
 * Explanations of {@code y = |x|}. A removed value of y is explained by both of its square roots,
 * {@code u} and {@code -u}, being out of x, and a removed value w of x by {@code |w|} being out of
 * y; a value can also be explained by its own variable having lost it before. Values are covered a
 * range at a time where a bound does it: the lower bound of x covers every y value below it, both
 * bounds of x every y value above {@code max(-min x, max x)}, the lower bound of y every x value in
 * {@code (-min y, min y)}, and the upper bound of y every x value outside {@code [-max y, max y]}.
 * Holes cover one value each.
 *
 * <p>The reasons are those of Chuffed and Pumpkin for the bounds (for example {@code [x >= l] -> [y
 * >= l]} for {@code l > 0}), extended to holes, so that they also explain the domain consistent
 * propagator and the gap {@code (-min y, min y)} the bounds propagator removes from x. They use the
 * trail's own atoms: an atom such as {@code [x >= 0]} that is not on the trail is replaced by the
 * bound that implies it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class AbsExplanation {

  // steps walked for one reason before giving up on it
  private static final int MAX_STEPS = 4096;

  private static final long BELOW = Long.MIN_VALUE / 4;

  private static final long ABOVE = Long.MAX_VALUE / 4;

  private final AtomicTrail trail;
  private final int position;
  private final IntVar x;
  private final IntVar y;
  private final EntryList out;
  private final long xMin;
  private final long xMax;
  private final long yMin;
  private final long yMax;

  // which bound entries are already in out: x low, x high, y low, y high
  private final boolean[] added = new boolean[4];

  // the range covered by the last successful cover
  private long coveredLow;
  private long coveredHigh;

  // the best range of a cover so far, and its bound entries as bits: 1 x low, 2 x high, 4 y low,
  // 8 y high
  private long bestLow;
  private long bestHigh;
  private int bestBounds;

  private AbsExplanation(AtomicTrail trail, int position, IntVar x, IntVar y, EntryList out) {
    this.trail = trail;
    this.position = position;
    this.x = x;
    this.y = y;
    this.out = out;
    this.xMin = trail.minBefore(x, position);
    this.xMax = trail.maxBefore(x, position);
    this.yMin = trail.minBefore(y, position);
    this.yMax = trail.maxBefore(y, position);
  }

  /**
   * Adds to {@code out} the reason of an entry of {@code y = |x|}.
   *
   * @param trail the trail
   * @param entry an entry of x or y
   * @param x the signed variable
   * @param y the absolute value
   * @param out where the reason entries are added
   * @return false when x and y are the same variable, or a removed value is not explained
   */
  public static boolean explain(AtomicTrail trail, int entry, IntVar x, IntVar y, EntryList out) {
    if (x == y) {
      return false;
    }
    boolean onY = trail.variable(entry) == y;
    long lo = trail.removedMin(entry);
    long hi = trail.removedMax(entry);
    AbsExplanation e = new AbsExplanation(trail, entry, x, y, out);
    return trail.kind(entry) == AtomicTrail.GE ? e.down(onY, hi, lo) : e.up(onY, lo, hi);
  }

  /**
   * Adds to {@code out} the reason why {@code y = |x|} has no solution now.
   *
   * @param trail the trail
   * @param x the signed variable
   * @param y the absolute value
   * @param out where the reason entries are added
   * @return false when x and y are the same variable, or some value of x has its absolute value in
   *     y
   */
  public static boolean explainFailure(AtomicTrail trail, IntVar x, IntVar y, EntryList out) {
    return disjointBefore(trail, trail.size(), x, y, out);
  }

  /**
   * Adds to {@code out} the reason why no value of x had its absolute value in y just before a
   * trail position: every value of x, or every value of y, out of the domain or without a
   * counterpart. The shorter of the two is kept.
   *
   * @param trail the trail
   * @param position the trail position (an entry index, or {@link AtomicTrail#size()} for now)
   * @param x the signed variable
   * @param y the absolute value
   * @param out where the reason entries are added
   * @return false when x and y are the same variable, or the domains had a supported pair
   */
  public static boolean disjointBefore(
      AtomicTrail trail, int position, IntVar x, IntVar y, EntryList out) {
    if (x == y) {
      return false;
    }
    int mark = out.size();
    EntryList viaY = new EntryList();
    boolean byY = allOut(trail, position, x, y, true, viaY);
    boolean byX = allOut(trail, position, x, y, false, out);
    if (byY && (!byX || viaY.size() < out.size() - mark)) {
      out.truncate(mark);
      for (int k = 0; k < viaY.size(); k++) {
        out.add(viaY.get(k));
      }
      return true;
    }
    return byX;
  }

  /**
   * Adds to {@code out} the reason why x and y were both fixed, to values that satisfy {@code y =
   * |x|}, just before a trail position.
   *
   * @param trail the trail
   * @param position the trail position (an entry index, or {@link AtomicTrail#size()} for now)
   * @param x the signed variable
   * @param y the absolute value
   * @param out where the reason entries are added
   * @return false when x and y are the same variable, or were not so fixed
   */
  public static boolean entailedBefore(
      AtomicTrail trail, int position, IntVar x, IntVar y, EntryList out) {
    int v = trail.minBefore(x, position);
    int u = trail.minBefore(y, position);
    if (x == y
        || v != trail.maxBefore(x, position)
        || u != trail.maxBefore(y, position)
        || u != Math.abs((long) v)) {
      return false;
    }
    trail.addLowerBound(x, position, out);
    trail.addUpperBound(x, position, out);
    trail.addLowerBound(y, position, out);
    trail.addUpperBound(y, position, out);
    return true;
  }

  // every value of one variable, from its root minimum to its root maximum, out before the position
  private static boolean allOut(
      AtomicTrail trail, int position, IntVar x, IntVar y, boolean onY, EntryList out) {
    AbsExplanation e = new AbsExplanation(trail, position, x, y, out);
    IntVar v = onY ? y : x;
    return e.up(onY, trail.rootDomain(v).min(), trail.rootDomain(v).max());
  }

  // every value of the variable in [lo, hi] out before the position, walked from lo upward
  private boolean up(boolean onY, long lo, long hi) {
    long u = lo;
    for (int steps = 0; u <= hi; steps++) {
      if (steps >= MAX_STEPS || !cover(onY, u, true)) {
        return false;
      }
      u = coveredHigh + 1;
    }
    return true;
  }

  // every value of the variable in [lo, hi] out before the position, walked from hi downward
  private boolean down(boolean onY, long hi, long lo) {
    long u = hi;
    for (int steps = 0; u >= lo; steps++) {
      if (steps >= MAX_STEPS || !cover(onY, u, false)) {
        return false;
      }
      u = coveredLow - 1;
    }
    return true;
  }

  // value u of y (or x) out before the position: sets the covered range and adds its entries; of
  // the ranges that bounds cover, the one reaching furthest in the walk's direction is taken
  private boolean cover(boolean onY, long u, boolean upward) {
    bestBounds = -1;
    if (onY) {
      if (u < 0) {
        candidate(BELOW, -1, 0, upward);
      }
      if (u >= 0 && u < xMin) {
        candidate(BELOW, xMin - 1, 1, upward);
      }
      if (u >= 0 && -u > xMax) {
        candidate(BELOW, -xMax - 1, 2, upward);
      }
      if (u > xMax && -u < xMin) {
        candidate(Math.max(xMax, -xMin) + 1, ABOVE, 1 | 2, upward);
      }
      ownBounds(u, yMin, yMax, 4, 8, upward);
    } else {
      long a = Math.abs(u);
      if (a < yMin) {
        candidate(1 - yMin, yMin - 1, 4, upward);
      }
      if (yMax < 0) {
        candidate(BELOW, ABOVE, 8, upward);
      } else if (u > yMax) {
        candidate(yMax + 1, ABOVE, 8, upward);
      } else if (-u > yMax) {
        candidate(BELOW, -yMax - 1, 8, upward);
      }
      ownBounds(u, xMin, xMax, 1, 2, upward);
    }
    if (bestBounds >= 0) {
      for (int k = 0; k < 4; k++) {
        if ((bestBounds & 1 << k) != 0) {
          bound(k);
        }
      }
      coveredLow = bestLow;
      coveredHigh = bestHigh;
      return true;
    }
    coveredLow = u;
    coveredHigh = u;
    if (trail.excludedBefore(onY ? y : x, (int) u, position, out)) {
      return true;
    }
    return onY ? bothRootsOut(u) : trail.excludedBefore(y, (int) Math.abs(u), position, out);
  }

  private void ownBounds(long u, long min, long max, int low, int high, boolean upward) {
    if (u < min) {
      candidate(BELOW, min - 1, low, upward);
    }
    if (u > max) {
      candidate(max + 1, ABOVE, high, upward);
    }
  }

  private void candidate(long low, long high, int bounds, boolean upward) {
    if (bestBounds >= 0) {
      long reach = upward ? high - bestHigh : bestLow - low;
      if (reach < 0 || reach == 0 && cost(bounds) >= cost(bestBounds)) {
        return;
      }
    }
    bestLow = low;
    bestHigh = high;
    bestBounds = bounds;
  }

  // bound entries not yet added
  private int cost(int bounds) {
    int c = 0;
    for (int k = 0; k < 4; k++) {
      if ((bounds & 1 << k) != 0 && !added[k]) {
        c++;
      }
    }
    return c;
  }

  // y value u, inside the bounds of x on one side at least, with u and -u each out of x
  private boolean bothRootsOut(long u) {
    int mark = out.size();
    boolean[] before = added.clone();
    if (rootOut(u) && rootOut(-u)) {
      return true;
    }
    out.truncate(mark);
    System.arraycopy(before, 0, added, 0, added.length);
    return false;
  }

  private boolean rootOut(long v) {
    if (v < xMin) {
      bound(0);
      return true;
    }
    if (v > xMax) {
      bound(1);
      return true;
    }
    return trail.excludedBefore(x, (int) v, position, out);
  }

  // adds a bound entry once: 0 x low, 1 x high, 2 y low, 3 y high
  private void bound(int which) {
    if (added[which]) {
      return;
    }
    added[which] = true;
    switch (which) {
      case 0 -> trail.addLowerBound(x, position, out);
      case 1 -> trail.addUpperBound(x, position, out);
      case 2 -> trail.addLowerBound(y, position, out);
      default -> trail.addUpperBound(y, position, out);
    }
  }
}
