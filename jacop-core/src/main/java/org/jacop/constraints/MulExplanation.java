/*
 * MulExplanation.java
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

import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of {@code x * y = z} by supports. A value w removed from one variable has no
 * support: for each value of one of the other two variables within its bounds just before the
 * entry, the value the third variable would need is not an integer or was out of its domain, or the
 * enumerated value itself was. The reason is the bounds of the enumerated variable and the entries
 * that removed the needed values. When z's interval of products already excludes the removed
 * values, the bounds of x and y are the reason.
 *
 * <p>Variables that occur twice are read as independent occurrences, which only weakens what the
 * check proves, so the reasons stay sound.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class MulExplanation {

  /** The most removed values explained one by one. */
  private static final int REMOVED_LIMIT = 64;

  /** The widest range of a variable enumerated for supports. */
  private static final int RANGE_LIMIT = 1024;

  /**
   * The most support checks of one explanation when more than {@link #REMOVED_LIMIT} values are
   * removed: removed values times the range enumerated for each.
   */
  private static final long WORK_LIMIT = 1 << 16;

  private final AtomicTrail trail;
  private final IntVar x;
  private final IntVar y;
  private final IntVar z;
  private final int position;

  MulExplanation(AtomicTrail trail, IntVar x, IntVar y, IntVar z, int position) {
    this.trail = trail;
    this.x = x;
    this.y = y;
    this.z = z;
    this.position = position;
  }

  /**
   * Adds to {@code out} the reason of an entry of x, y or z.
   *
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when some removed value has a support, or the ranges are too wide
   */
  boolean explain(int entry, EntryList out) {
    IntVar v = trail.variable(entry);
    IntDomain root = trail.rootDomain(v);
    long lo = trail.removedMin(entry);
    long hi = trail.removedMax(entry);
    int mark = out.size();
    int min = trail.minBefore(v, position);
    if (lo < min) {
      trail.addLowerBound(v, position, out);
      lo = min;
    }
    int max = trail.maxBefore(v, position);
    if (hi > max) {
      trail.addUpperBound(v, position, out);
      hi = max;
    }
    if (lo > hi) {
      return true;
    }
    int roles = (v == z ? 1 : 0) | (v == x ? 2 : 0) | (v == y ? 4 : 0);
    // the cheap case: the bounds of the other variables already exclude the removed values
    if (boundsExclude(roles, lo, hi, out)) {
      return true;
    }
    if (hi - lo >= REMOVED_LIMIT && (hi - lo + 1) * width(roles) > WORK_LIMIT) {
      out.truncate(mark);
      return false;
    }
    for (long w = lo; w <= hi; w++) {
      int value = (int) w;
      if (!root.contains(value) || trail.excludedBefore(v, value, position, out)) {
        continue;
      }
      if (!unsupported(roles, value, out)) {
        out.truncate(mark);
        return false;
      }
    }
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure: one of the variables has no supported value.
   *
   * @param out where the reason entries are added
   * @return false when every variable has a supported value, or the ranges are too wide
   */
  boolean explainFailure(EntryList out) {
    int mark = out.size();
    IntVar[] vars = {z, x, y};
    // the cheap case: the bounds of two variables exclude every value of the third's bounds
    for (IntVar v : vars) {
      int roles = (v == z ? 1 : 0) | (v == x ? 2 : 0) | (v == y ? 4 : 0);
      if (boundsExclude(roles, trail.minBefore(v, position), trail.maxBefore(v, position), out)) {
        addBounds(v, out);
        return true;
      }
      out.truncate(mark);
    }
    // otherwise the shortest of the variables' reasons that no value is supported: the first one
    // found could cite a != atom for every value of a wide product, thousands of atoms on Molnar
    EntryList best = null;
    EntryList candidate = new EntryList();
    for (IntVar v : vars) {
      int lo = trail.minBefore(v, position);
      int hi = trail.maxBefore(v, position);
      int roles = (v == z ? 1 : 0) | (v == x ? 2 : 0) | (v == y ? 4 : 0);
      if ((long) hi - lo >= REMOVED_LIMIT && ((long) hi - lo + 1) * width(roles) > WORK_LIMIT) {
        continue;
      }
      candidate.clear();
      addBounds(v, candidate);
      boolean all = true;
      for (int w = lo; w <= hi && all; w++) {
        all = trail.excludedBefore(v, w, position, candidate) || unsupported(roles, w, candidate);
      }
      if (all) {
        candidate.sortUnique(0);
        if (best == null || candidate.size() < best.size()) {
          EntryList swap = best == null ? new EntryList() : best;
          best = candidate;
          candidate = swap;
        }
      }
    }
    if (best == null) {
      return false;
    }
    for (int k = 0; k < best.size(); k++) {
      out.add(best.get(k));
    }
    return true;
  }

  /**
   * Whether the bounds of the other variables exclude the removed values [lo, hi] of the variable
   * in the given roles, as the bounds propagation of {@link XmulYeqZ} finds; the reason, those
   * bounds, goes to out. Wide domains, where supports are not enumerated, are explained this way.
   * Bounds that are not needed are left out: each is put back to its initial value while the
   * removed values stay excluded.
   */
  private boolean boundsExclude(int roles, long lo, long hi, EntryList out) {
    IntVar[] vars;
    switch (roles) {
      case 1 -> vars = x == y ? new IntVar[] {x} : new IntVar[] {x, y};
      case 2 -> vars = new IntVar[] {z, y, x};
      case 4 -> vars = new IntVar[] {z, x, y};
      case 6 -> vars = new IntVar[] {z};
      default -> {
        return false;
      }
    }
    int[] b = new int[2 * vars.length];
    for (int i = 0; i < vars.length; i++) {
      b[2 * i] = trail.minBefore(vars[i], position);
      b[2 * i + 1] = trail.maxBefore(vars[i], position);
    }
    if (!excludes(roles, b, lo, hi)) {
      return false;
    }
    for (int k = 0; k < b.length; k++) {
      IntDomain root = trail.rootDomain(vars[k / 2]);
      int initial = k % 2 == 0 ? root.min() : root.max();
      int current = b[k];
      if (current != initial) {
        b[k] = initial;
        if (!excludes(roles, b, lo, hi)) {
          b[k] = current;
        }
      }
    }
    for (int k = 0; k < b.length; k++) {
      if (k % 2 == 0 && b[k] == trail.minBefore(vars[k / 2], position)) {
        trail.addLowerBound(vars[k / 2], position, out);
      } else if (k % 2 == 1 && b[k] == trail.maxBefore(vars[k / 2], position)) {
        trail.addUpperBound(vars[k / 2], position, out);
      }
    }
    return true;
  }

  /**
   * Whether bounds b exclude [lo, hi]: b holds the min and max of x and y (role 1; of x alone for a
   * square), of z, the other factor and the factor (roles 2 and 4), or of z (role 6, a square).
   */
  private static boolean excludes(int roles, int[] b, long lo, long hi) {
    switch (roles) {
      case 1 -> {
        long[] p = b.length == 2 ? squares(b[0], b[1]) : products(b[0], b[1], b[2], b[3]);
        return hi < p[0] || lo > p[1];
      }
      case 6 -> {
        long[] p = squares(lo, hi);
        return p[0] > b[1] || p[1] < b[0];
      }
      default -> {
        long[] range = factorRange(b[0], b[1], b[2], b[3], b[4], b[5]);
        return range == null || hi < range[0] || lo > range[1];
      }
    }
  }

  private static long[] products(long xl, long xh, long yl, long yh) {
    long p1 = xl * yl;
    long p2 = xl * yh;
    long p3 = xh * yl;
    long p4 = xh * yh;
    return new long[] {
      Math.min(Math.min(p1, p2), Math.min(p3, p4)), Math.max(Math.max(p1, p2), Math.max(p3, p4))
    };
  }

  private static long[] squares(long lo, long hi) {
    long min = lo <= 0 && hi >= 0 ? 0 : Math.min(lo * lo, hi * hi);
    return new long[] {min, Math.max(lo * lo, hi * hi)};
  }

  /**
   * The bounds of factor v in v * other = z that the bounds of z and other allow, computed as
   * {@link XmulYeqZ} does: when other spans 0 and z does not, the quotient is taken over the
   * negative and the positive part of other, each cut to v's bounds.
   *
   * @return {min, max}, or null when no value is allowed
   */
  private static long[] factorRange(int zl, int zh, int ol, int oh, int vl, int vh) {
    if (ol >= 0 || oh <= 0 || (zl <= 0 && zh >= 0)) {
      try {
        Interval q = IntDomain.divIntBounds(zl, zh, ol, oh);
        return new long[] {q.min(), q.max()};
      } catch (FailException _) {
        return null;
      }
    }
    long[] negative = quotientWithin(zl, zh, ol, -1, vl, vh);
    long[] positive = quotientWithin(zl, zh, 1, oh, vl, vh);
    if (negative == null || positive == null) {
      return negative == null ? positive : negative;
    }
    return new long[] {Math.min(negative[0], positive[0]), Math.max(negative[1], positive[1])};
  }

  // the values of [zl, zh] / [c, d] within [vl, vh], or null if there are none
  private static long[] quotientWithin(int zl, int zh, int c, int d, int vl, int vh) {
    try {
      Interval q = IntDomain.divIntBounds(zl, zh, c, d);
      long min = Math.max(q.min(), vl);
      long max = Math.min(q.max(), vh);
      return min <= max ? new long[] {min, max} : null;
    } catch (FailException _) {
      return null;
    }
  }

  /** Whether value w of the variable in the given roles has no support; reasons go to out. */
  private boolean unsupported(int roles, int w, EntryList out) {
    // the first role the variable has; its other occurrences are read independently
    if ((roles & 1) != 0) {
      return unsupportedProduct(w, out);
    }
    return unsupportedFactor(w, (roles & 2) == 0 ? x : y, out);
  }

  // z = w: for each value a of the narrower factor, the other factor's w / a is gone
  private boolean unsupportedProduct(int w, EntryList out) {
    IntVar f = range(y) < range(x) ? y : x;
    IntVar g = f == x ? y : x;
    int fl = trail.minBefore(f, position);
    int fh = trail.maxBefore(f, position);
    if ((long) fh - fl >= RANGE_LIMIT) {
      return false;
    }
    addBounds(f, out);
    for (int a = fl; a <= fh; a++) {
      if (a == 0 ? w == 0 : w % a == 0) {
        if (trail.excludedBefore(f, a, position, out)) {
          continue;
        }
        if (a == 0 || !trail.excludedBefore(g, w / a, position, out)) {
          return false;
        }
      }
    }
    return true;
  }

  // the factor is w, other is the other factor: for each value b of other, z = w * b is gone; or,
  // when z is narrower, for each value c of z that w divides, other's c / w is gone
  private boolean unsupportedFactor(int w, IntVar other, EntryList out) {
    int ol = trail.minBefore(other, position);
    int oh = trail.maxBefore(other, position);
    if (w != 0 && range(z) < (long) oh - ol) {
      return unsupportedQuotient(w, other, out);
    }
    if ((long) oh - ol >= RANGE_LIMIT) {
      return false;
    }
    addBounds(other, out);
    for (int b = ol; b <= oh; b++) {
      long c = (long) w * b;
      if (c < Integer.MIN_VALUE || c > Integer.MAX_VALUE) {
        continue;
      }
      if (trail.excludedBefore(other, b, position, out)) {
        continue;
      }
      if (!trail.excludedBefore(z, (int) c, position, out)) {
        return false;
      }
    }
    return true;
  }

  // the factor is w != 0: for each value c of z that w divides, other = c / w is gone
  private boolean unsupportedQuotient(int w, IntVar other, EntryList out) {
    int zl = trail.minBefore(z, position);
    int zh = trail.maxBefore(z, position);
    if ((long) zh - zl >= RANGE_LIMIT) {
      return false;
    }
    addBounds(z, out);
    for (int c = zl; c <= zh; c++) {
      if (c % w != 0 || trail.excludedBefore(z, c, position, out)) {
        continue;
      }
      if (!trail.excludedBefore(other, c / w, position, out)) {
        return false;
      }
    }
    return true;
  }

  // the width of the range enumerated to check one value of the variable in the given roles
  private long width(int roles) {
    if ((roles & 1) != 0) {
      return Math.min(range(x), range(y)) + 1;
    }
    IntVar other = (roles & 2) == 0 ? x : y;
    return Math.min(range(other), range(z)) + 1;
  }

  private long range(IntVar v) {
    return (long) trail.maxBefore(v, position) - trail.minBefore(v, position);
  }

  private void addBounds(IntVar v, EntryList out) {
    trail.addLowerBound(v, position, out);
    trail.addUpperBound(v, position, out);
  }
}
