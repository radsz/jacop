/*
 * BoxExplanation.java
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
 * Explanations of a constraint on x, y and z by bounds, for a relation whose {@link
 * DivModPowBounds.Narrowing} narrows a box to the solutions in it. A removed range of one variable
 * is explained when, with that variable in the range and the other two in their bounds just before
 * the entry, the narrowing leaves no value, or only values that were already removed. The reason is
 * those bounds, each relaxed to its initial value when the range stays explained without it, and
 * the entries that removed the remaining values. A failure is explained when the narrowing of the
 * bounds just before it is empty.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class BoxExplanation {

  /** The most values inside the narrowed box that may be explained by earlier removals. */
  private static final int HOLE_LIMIT = 64;

  private BoxExplanation() {}

  /**
   * Adds to {@code out} the reason of an entry of x, y or z.
   *
   * @param trail the trail
   * @param entry the entry
   * @param vars x, y and z
   * @param f the narrowing of the relation
   * @param out where the reason entries are added
   * @return false when the variables are not distinct, or the bounds do not explain the entry
   */
  static boolean explain(
      AtomicTrail trail, int entry, IntVar[] vars, DivModPowBounds.Narrowing f, EntryList out) {
    if (vars[0] == vars[1] || vars[0] == vars[2] || vars[1] == vars[2]) {
      return false;
    }
    IntVar v = trail.variable(entry);
    int k = v == vars[0] ? 0 : v == vars[1] ? 1 : 2;
    long[] b = bounds(trail, entry, vars);
    long lo = trail.removedMin(entry);
    long hi = trail.removedMax(entry);
    int mark = out.size();
    if (lo < b[2 * k]) {
      trail.addLowerBound(v, entry, out);
      lo = b[2 * k];
    }
    if (hi > b[2 * k + 1]) {
      trail.addUpperBound(v, entry, out);
      hi = b[2 * k + 1];
    }
    if (lo > hi) {
      return true;
    }
    b[2 * k] = lo;
    b[2 * k + 1] = hi;
    long[] left = narrowed(f, b, k);
    if (left != null) {
      // the values left must have been removed before
      if (left[1] - left[0] >= HOLE_LIMIT) {
        out.truncate(mark);
        return false;
      }
      for (long w = left[0]; w <= left[1]; w++) {
        if (!trail.excludedBefore(v, (int) w, entry, out)) {
          out.truncate(mark);
          return false;
        }
      }
    }
    // the bounds of the other two variables, relaxed where they are not needed
    for (int i = 0; i < 6; i++) {
      if (i / 2 == k) {
        continue;
      }
      long current = b[i];
      IntDomain root = trail.rootDomain(vars[i / 2]);
      b[i] = i % 2 == 0 ? root.min() : root.max();
      if (b[i] != current && !within(narrowed(f, b, k), left)) {
        b[i] = current;
      }
    }
    addBounds(trail, entry, vars, b, k, out);
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure: bounds that leave no solution.
   *
   * @param trail the trail
   * @param vars x, y and z
   * @param f the narrowing of the relation
   * @param out where the reason entries are added
   * @return false when the bounds now hold a solution of the box
   */
  static boolean explainFailure(
      AtomicTrail trail, IntVar[] vars, DivModPowBounds.Narrowing f, EntryList out) {
    if (vars[0] == vars[1] || vars[0] == vars[2] || vars[1] == vars[2]) {
      return false;
    }
    int position = trail.size();
    long[] b = bounds(trail, position, vars);
    if (f.narrow(b.clone())) {
      return false;
    }
    for (int i = 0; i < 6; i++) {
      long current = b[i];
      IntDomain root = trail.rootDomain(vars[i / 2]);
      b[i] = i % 2 == 0 ? root.min() : root.max();
      if (b[i] != current && f.narrow(b.clone())) {
        b[i] = current;
      }
    }
    addBounds(trail, position, vars, b, -1, out);
    return true;
  }

  private static long[] bounds(AtomicTrail trail, int position, IntVar[] vars) {
    long[] b = new long[6];
    for (int i = 0; i < 3; i++) {
      b[2 * i] = trail.minBefore(vars[i], position);
      b[2 * i + 1] = trail.maxBefore(vars[i], position);
    }
    return b;
  }

  // the range of variable k the narrowing of b leaves, or null when it is empty
  private static long[] narrowed(DivModPowBounds.Narrowing f, long[] b, int k) {
    long[] c = b.clone();
    return f.narrow(c) ? new long[] {c[2 * k], c[2 * k + 1]} : null;
  }

  private static boolean within(long[] range, long[] allowed) {
    return range == null || (allowed != null && range[0] >= allowed[0] && range[1] <= allowed[1]);
  }

  // the bound entries of the variables other than k whose bound in b is the one before position
  private static void addBounds(
      AtomicTrail trail, int position, IntVar[] vars, long[] b, int k, EntryList out) {
    for (int i = 0; i < 3; i++) {
      if (i == k) {
        continue;
      }
      if (b[2 * i] == trail.minBefore(vars[i], position)) {
        trail.addLowerBound(vars[i], position, out);
      }
      if (b[2 * i + 1] == trail.maxBefore(vars[i], position)) {
        trail.addUpperBound(vars[i], position, out);
      }
    }
  }
}
