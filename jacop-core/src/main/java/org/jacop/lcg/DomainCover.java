/*
 * DomainCover.java
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
 * Explanations of atoms that keep a variable away from values some other fact rules out: every
 * value in a range is either out of the variable's domain already or ruled out by a reason the
 * caller gives (a value outside a fixed set, an element out of a set variable, ...).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class DomainCover {

  /** The widest range of values covered one by one; wider ranges get no reason. */
  public static final int RANGE_LIMIT = 4096;

  /** The reason why a value is ruled out. */
  @FunctionalInterface
  public interface ValueReason {

    /**
     * Adds to {@code out} the reason why a value is ruled out, when it is.
     *
     * @param value the value
     * @param out where the reason entries are added
     * @return false when the value is not ruled out
     */
    boolean add(int value, EntryList out);
  }

  private DomainCover() {}

  /**
   * Adds to {@code out} the reason that every value from lo to hi was out of a variable's domain
   * just before a trail position or is ruled out.
   *
   * @param trail the trail
   * @param x the variable
   * @param position the trail position (an entry index, or {@link AtomicTrail#size()} for now)
   * @param lo the first value
   * @param hi the last value
   * @param ruledOut the reason why a value is ruled out
   * @param out where the reason entries are added
   * @return false when some value is neither, or the range is wider than {@link #RANGE_LIMIT}
   */
  public static boolean range(
      AtomicTrail trail,
      IntVar x,
      int position,
      long lo,
      long hi,
      ValueReason ruledOut,
      EntryList out) {
    if (hi - lo >= RANGE_LIMIT) {
      return false;
    }
    for (long u = lo; u <= hi; u++) {
      int v = (int) u;
      if (!ruledOut.add(v, out) && !trail.excludedBefore(x, v, position, out)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Adds to {@code out} the reason that every value of a variable's domain just before a trail
   * position is ruled out: its bounds and the values between them.
   *
   * @param trail the trail
   * @param x the variable
   * @param position the trail position (an entry index, or {@link AtomicTrail#size()} for now)
   * @param ruledOut the reason why a value is ruled out
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  public static boolean domain(
      AtomicTrail trail, IntVar x, int position, ValueReason ruledOut, EntryList out) {
    trail.addLowerBound(x, position, out);
    trail.addUpperBound(x, position, out);
    return range(
        trail,
        x,
        position,
        trail.minBefore(x, position),
        trail.maxBefore(x, position),
        ruledOut,
        out);
  }

  /**
   * Adds to {@code out} the reason of an atom that removes ruled out values from its variable: a
   * removed value is ruled out, a moved bound passed only values that are out or ruled out.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param ruledOut the reason why a value is ruled out
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  public static boolean entry(AtomicTrail trail, int entry, ValueReason ruledOut, EntryList out) {
    IntVar x = trail.variable(entry);
    int v = trail.value(entry);
    switch (trail.kind(entry)) {
      case AtomicTrail.NE:
        return ruledOut.add(v, out);
      case AtomicTrail.GE:
        trail.addLowerBound(x, entry, out);
        return range(trail, x, entry, trail.minBefore(x, entry), v - 1L, ruledOut, out);
      default:
        trail.addUpperBound(x, entry, out);
        return range(trail, x, entry, v + 1L, trail.maxBefore(x, entry), ruledOut, out);
    }
  }
}
