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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
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
    // the cheap case: products of the bounds of x and y miss the removed values of z
    if (roles == 1 && productsMiss(lo, hi)) {
      addBounds(x, out);
      addBounds(y, out);
      return true;
    }
    if (hi - lo >= REMOVED_LIMIT) {
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
    for (IntVar v : vars) {
      int lo = trail.minBefore(v, position);
      int hi = trail.maxBefore(v, position);
      if ((long) hi - lo >= REMOVED_LIMIT) {
        continue;
      }
      int roles = (v == z ? 1 : 0) | (v == x ? 2 : 0) | (v == y ? 4 : 0);
      addBounds(v, out);
      boolean all = true;
      for (int w = lo; w <= hi && all; w++) {
        all = trail.excludedBefore(v, w, position, out) || unsupported(roles, w, out);
      }
      if (all) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // whether the products of x's and y's bounds miss [lo, hi]
  private boolean productsMiss(long lo, long hi) {
    long xl = trail.minBefore(x, position);
    long xh = trail.maxBefore(x, position);
    long yl = trail.minBefore(y, position);
    long yh = trail.maxBefore(y, position);
    long p1 = xl * yl;
    long p2 = xl * yh;
    long p3 = xh * yl;
    long p4 = xh * yh;
    long pmin = Math.min(Math.min(p1, p2), Math.min(p3, p4));
    long pmax = Math.max(Math.max(p1, p2), Math.max(p3, p4));
    return hi < pmin || lo > pmax;
  }

  /** Whether value w of the variable in the given roles has no support; reasons go to out. */
  private boolean unsupported(int roles, int w, EntryList out) {
    // the first role the variable has; its other occurrences are read independently
    if ((roles & 1) != 0) {
      return unsupportedProduct(w, out);
    }
    return (roles & 2) != 0 ? unsupportedFactor(w, y, out) : unsupportedFactor(w, x, out);
  }

  // z = w: for each value a of x, y = w / a is gone
  private boolean unsupportedProduct(int w, EntryList out) {
    int xl = trail.minBefore(x, position);
    int xh = trail.maxBefore(x, position);
    if ((long) xh - xl >= RANGE_LIMIT) {
      return false;
    }
    addBounds(x, out);
    for (int a = xl; a <= xh; a++) {
      if (a == 0 ? w == 0 : w % a == 0) {
        if (trail.excludedBefore(x, a, position, out)) {
          continue;
        }
        if (a == 0 || !trail.excludedBefore(y, w / a, position, out)) {
          return false;
        }
      }
    }
    return true;
  }

  // the factor is w, other is the other factor: for each value b of other, z = w * b is gone
  private boolean unsupportedFactor(int w, IntVar other, EntryList out) {
    int ol = trail.minBefore(other, position);
    int oh = trail.maxBefore(other, position);
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

  private void addBounds(IntVar v, EntryList out) {
    trail.addLowerBound(v, position, out);
    trail.addUpperBound(v, position, out);
  }
}
