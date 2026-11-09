/*
 * ShiftExplanation.java
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
 * Explanations of {@code target = source + k} propagated on domains: an atom of the target holds
 * because each value it removes is out of the target's domain, or its counterpart out of the
 * source's domain, before the atom's entry. Equalities, shifts and sums with a fixed term share it.
 * Mirrors {@code target = k - source} (x + y = c) walk the same way with the counterpart {@code k -
 * u} of a target value {@code u}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ShiftExplanation {

  // values walked for one reason before giving up on it
  private static final int MAX_VALUES = 4096;

  private ShiftExplanation() {}

  /**
   * Adds to {@code out} the reason of an entry of {@code target}, given {@code target = source +
   * k}.
   *
   * @param trail the trail
   * @param entry an entry of the target
   * @param target the variable of the entry
   * @param source the other variable
   * @param k the shift
   * @param out where the reason entries are added
   * @return false when a removed value is out of neither domain before the entry
   */
  public static boolean explain(
      AtomicTrail trail, int entry, IntVar target, IntVar source, long k, EntryList out) {
    return explain(trail, entry, target, source, k, 1, out);
  }

  /**
   * Adds to {@code out} the reason of an entry of {@code target}, given {@code target = k -
   * source}.
   *
   * @param trail the trail
   * @param entry an entry of the target
   * @param target the variable of the entry
   * @param source the other variable
   * @param k the sum of the two variables
   * @param out where the reason entries are added
   * @return false when a removed value is out of neither domain before the entry
   */
  public static boolean explainMirror(
      AtomicTrail trail, int entry, IntVar target, IntVar source, long k, EntryList out) {
    return explain(trail, entry, target, source, k, -1, out);
  }

  private static boolean explain(
      AtomicTrail trail, int entry, IntVar target, IntVar source, long k, int sign, EntryList out) {
    int a = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.NE -> excluded(trail, entry, target, source, k, sign, a, out);
      case AtomicTrail.GE -> below(trail, entry, target, source, k, sign, a - 1L, out);
      default -> above(trail, entry, target, source, k, sign, a + 1L, out);
    };
  }

  /**
   * Adds to {@code out} the reason why {@code target = source + k} has no solution now: the bounds
   * of both variables, and the exclusion of each value in their common range.
   *
   * @param trail the trail
   * @param target one variable
   * @param source the other variable
   * @param k the shift
   * @param out where the reason entries are added
   * @return false when some value is in both domains
   */
  public static boolean explainFailure(
      AtomicTrail trail, IntVar target, IntVar source, long k, EntryList out) {
    return disjointBefore(trail, trail.size(), target, source, k, out);
  }

  /**
   * Adds to {@code out} the reason why no value of {@code target} equals a value of {@code source}
   * plus {@code k} just before a trail position.
   *
   * @param trail the trail
   * @param position the trail position (an entry index, or {@link AtomicTrail#size()} for now)
   * @param target one variable
   * @param source the other variable
   * @param k the shift
   * @param out where the reason entries are added
   * @return false when some value is in both domains then
   */
  public static boolean disjointBefore(
      AtomicTrail trail, int position, IntVar target, IntVar source, long k, EntryList out) {
    return disjointBefore(trail, position, target, source, k, 1, out);
  }

  /**
   * Adds to {@code out} the reason why {@code target = k - source} has no solution now: the bounds
   * of both variables, and the exclusion of each value in their common range.
   *
   * @param trail the trail
   * @param target one variable
   * @param source the other variable
   * @param k the sum of the two variables
   * @param out where the reason entries are added
   * @return false when some value of the target has its counterpart in the source
   */
  public static boolean explainMirrorFailure(
      AtomicTrail trail, IntVar target, IntVar source, long k, EntryList out) {
    return disjointBefore(trail, trail.size(), target, source, k, -1, out);
  }

  private static boolean disjointBefore(
      AtomicTrail trail,
      int position,
      IntVar target,
      IntVar source,
      long k,
      int sign,
      EntryList out) {
    long sourceMin = trail.minBefore(source, position);
    long sourceMax = trail.maxBefore(source, position);
    long lo = Math.max(trail.minBefore(target, position), sign > 0 ? sourceMin + k : k - sourceMax);
    long hi = Math.min(trail.maxBefore(target, position), sign > 0 ? sourceMax + k : k - sourceMin);
    if (hi - lo >= MAX_VALUES) {
      return false;
    }
    for (long u = lo; u <= hi; u++) {
      if (!excluded(trail, position, target, source, k, sign, u, out)) {
        return false;
      }
    }
    trail.addLowerBound(target, position, out);
    trail.addUpperBound(target, position, out);
    trail.addLowerBound(source, position, out);
    trail.addUpperBound(source, position, out);
    return true;
  }

  /**
   * Adds to {@code out} the reason of an entry of {@code x + y = z} over distinct variables when
   * {@code x} or {@code y} was fixed before it: that term's bounds, and the shift between the other
   * two variables.
   *
   * @param trail the trail
   * @param entry the entry
   * @param x the first term
   * @param y the second term
   * @param z the sum
   * @param out where the reason entries are added
   * @return false when neither term was fixed, or the shift does not explain the entry
   */
  public static boolean explainSum(
      AtomicTrail trail, int entry, IntVar x, IntVar y, IntVar z, EntryList out) {
    IntVar v = trail.variable(entry);
    for (int t = 0; t < 2; t++) {
      IntVar fixed = t == 0 ? x : y;
      IntVar other = t == 0 ? y : x;
      if (v == fixed || trail.minBefore(fixed, entry) != trail.maxBefore(fixed, entry)) {
        continue;
      }
      long c = trail.minBefore(fixed, entry);
      int mark = out.size();
      if (v == z ? explain(trail, entry, z, other, c, out) : explain(trail, entry, v, z, -c, out)) {
        addFixed(trail, entry, fixed, z, mark, out);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  /** Whether a bound explained by one bound of the other variable cites one bound of the term. */
  static final boolean ONE_SIDE = !"false".equals(System.getProperty("jacop.lcg.shiftOneSide"));

  /*
   * Adds the bounds of the fixed term. When the shift gave a bound entry by one bound of the
   * other variable alone (no holes), one bound of the term suffices: z >= a from y >= a - c needs
   * only x >= c, and y >= a from z >= a + c only x <= c.
   */
  private static void addFixed(
      AtomicTrail trail, int entry, IntVar fixed, IntVar z, int mark, EntryList out) {
    int kind = trail.kind(entry);
    if (ONE_SIDE && kind != AtomicTrail.NE && out.size() == mark + 1) {
      int a = out.get(mark);
      IntVar w = trail.variable(a);
      int k = trail.kind(a);
      if (w != fixed && w != trail.variable(entry) && k != AtomicTrail.NE) {
        // a bound of the sum pairs with the opposite bound of the term, a bound of the other term
        // with the same bound
        boolean lower = w == z ? k == AtomicTrail.LE : k == AtomicTrail.GE;
        if (lower) {
          trail.addLowerBound(fixed, entry, out);
        } else {
          trail.addUpperBound(fixed, entry, out);
        }
        return;
      }
    }
    trail.addLowerBound(fixed, entry, out);
    trail.addUpperBound(fixed, entry, out);
  }

  /**
   * Adds to {@code out} the reason why {@code x + y = z} over distinct variables has no solution
   * now, when {@code x} or {@code y} is fixed.
   *
   * @param trail the trail
   * @param x the first term
   * @param y the second term
   * @param z the sum
   * @param out where the reason entries are added
   * @return false when neither term is fixed, or the shift does not explain the failure
   */
  public static boolean explainSumFailure(
      AtomicTrail trail, IntVar x, IntVar y, IntVar z, EntryList out) {
    int now = trail.size();
    for (int t = 0; t < 2; t++) {
      IntVar fixed = t == 0 ? x : y;
      if (trail.minBefore(fixed, now) != trail.maxBefore(fixed, now)) {
        continue;
      }
      int mark = out.size();
      if (explainFailure(trail, z, t == 0 ? y : x, trail.minBefore(fixed, now), out)) {
        trail.addLowerBound(fixed, now, out);
        trail.addUpperBound(fixed, now, out);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // every target value from top down is out before the position
  private static boolean below(
      AtomicTrail trail,
      int position,
      IntVar target,
      IntVar source,
      long k,
      int sign,
      long top,
      EntryList out) {
    long targetMin = trail.minBefore(target, position);
    // the least target value with a counterpart in the source's bounds
    long sourceMin =
        sign > 0 ? trail.minBefore(source, position) + k : k - trail.maxBefore(source, position);
    for (long u = top; ; u--) {
      if (u < targetMin) {
        trail.addLowerBound(target, position, out);
        return true;
      }
      if (u < sourceMin) {
        if (sign > 0) {
          trail.addLowerBound(source, position, out);
        } else {
          trail.addUpperBound(source, position, out);
        }
        return true;
      }
      if (top - u >= MAX_VALUES || !excluded(trail, position, target, source, k, sign, u, out)) {
        return false;
      }
    }
  }

  // every target value from bottom up is out before the position
  private static boolean above(
      AtomicTrail trail,
      int position,
      IntVar target,
      IntVar source,
      long k,
      int sign,
      long bottom,
      EntryList out) {
    long targetMax = trail.maxBefore(target, position);
    // the greatest target value with a counterpart in the source's bounds
    long sourceMax =
        sign > 0 ? trail.maxBefore(source, position) + k : k - trail.minBefore(source, position);
    for (long u = bottom; ; u++) {
      if (u > targetMax) {
        trail.addUpperBound(target, position, out);
        return true;
      }
      if (u > sourceMax) {
        if (sign > 0) {
          trail.addUpperBound(source, position, out);
        } else {
          trail.addLowerBound(source, position, out);
        }
        return true;
      }
      if (u - bottom >= MAX_VALUES || !excluded(trail, position, target, source, k, sign, u, out)) {
        return false;
      }
    }
  }

  // target value u, or its source counterpart (u - k, or k - u for a mirror), is out before the
  // position
  private static boolean excluded(
      AtomicTrail trail,
      int position,
      IntVar target,
      IntVar source,
      long k,
      int sign,
      long u,
      EntryList out) {
    if (u < Integer.MIN_VALUE || u > Integer.MAX_VALUE) {
      return true;
    }
    if (trail.excludedBefore(target, (int) u, position, out)) {
      return true;
    }
    long s = sign > 0 ? u - k : k - u;
    return s < Integer.MIN_VALUE
        || s > Integer.MAX_VALUE
        || trail.excludedBefore(source, (int) s, position, out);
  }
}
