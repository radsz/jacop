/*
 * LinearExplanation.java
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

import java.util.Arrays;
import org.jacop.core.IntVar;

/**
 * Explanations of a linear relation {@code sum w[i] * x[i] <= c}, {@code >= c} or both, from the
 * bounds of the other variables: the reasoning of bounds propagation. Sums, weighted sums and
 * pseudo-Boolean constraints share it. A variable may occur more than once; each occurrence is
 * treated as a variable of its own, as the propagators do, which gives weaker but sound reasons.
 * The checked explanations merge the occurrences of the explained variable when they have weights
 * of both signs, as an aggregated row can have. Sums that overflow a {@code long} give no reason.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LinearExplanation {

  private LinearExplanation() {}

  /**
   * Adds to {@code out} the reason of a bound entry: the bounds of the other variables that, with
   * the side of the relation the bound comes from, imply it.
   *
   * @param trail the trail
   * @param entry a bound entry of one of the variables
   * @param vars the variables
   * @param weights their weights
   * @param lessOrEqual whether the relation contains {@code sum <= c}
   * @param greaterOrEqual whether the relation contains {@code sum >= c}
   * @param out where the reason entries are added
   * @return false when there is no such reason (a {@code !=} entry, a side the relation lacks, or a
   *     variable that occurs with weights of both signs)
   */
  public static boolean explain(
      AtomicTrail trail,
      int entry,
      IntVar[] vars,
      long[] weights,
      boolean lessOrEqual,
      boolean greaterOrEqual,
      EntryList out) {
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return false;
    }
    int own = ownOccurrence(vars, weights, trail.variable(entry));
    if (own < 0) {
      // y occurs with weights of both signs: unchecked, the merged weight need not imply the entry
      return false;
    }
    long weight = weights[own];
    // the side of the relation the bound comes from: sum <= c, or sum >= c
    boolean upperSide = (kind == AtomicTrail.LE) == (weight > 0);
    if (upperSide ? !lessOrEqual : !greaterOrEqual) {
      return false;
    }
    addOtherBounds(trail, entry, vars, weights, own, upperSide, out);
    trail.addSkippedHoles(
        entry, kind == AtomicTrail.LE ? Integer.MAX_VALUE : Integer.MIN_VALUE, out);
    return true;
  }

  /**
   * Adds to {@code out} the reason of a bound entry as {@link #explain} does, but only when that
   * reason implies it: the bound the other variables' bounds give, with the holes of the entry's
   * variable recorded before it, must reach the entry's bound. A propagator stronger than bounds
   * reasoning uses it.
   *
   * @param trail the trail
   * @param entry a bound entry of one of the variables
   * @param vars the variables
   * @param weights their weights
   * @param c the right-hand side
   * @param lessOrEqual whether the relation contains {@code sum <= c}
   * @param greaterOrEqual whether the relation contains {@code sum >= c}
   * @param out where the reason entries are added
   * @return false when there is no such reason, or it does not imply the entry
   */
  public static boolean explainChecked(
      AtomicTrail trail,
      int entry,
      IntVar[] vars,
      long[] weights,
      long c,
      boolean lessOrEqual,
      boolean greaterOrEqual,
      EntryList out) {
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return false;
    }
    IntVar y = trail.variable(entry);
    int own = ownOccurrence(vars, weights, y);
    // y with weights of both signs: its occurrences are merged into one of their summed weight
    IntVar merged = own == MIXED ? y : null;
    long weight;
    if (merged != null) {
      weight = mergedWeight(vars, weights, y);
      if (weight == 0) {
        return false;
      }
    } else if (own < 0) {
      return false;
    } else {
      weight = weights[own];
    }
    boolean upperSide = (kind == AtomicTrail.LE) == (weight > 0);
    if (upperSide ? !lessOrEqual : !greaterOrEqual) {
      return false;
    }
    long a = trail.value(entry);
    int mark = out.size();
    try {
      // weight * y <= rest on the upper side, >= rest on the lower side
      long rest = c;
      for (int i = 0; i < vars.length; i++) {
        if (i == own || weights[i] == 0 || vars[i] == merged) {
          continue;
        }
        boolean low = upperSide == weights[i] > 0;
        rest =
            Math.subtractExact(
                rest,
                Math.multiplyExact(
                    weights[i],
                    low ? trail.minBefore(vars[i], entry) : trail.maxBefore(vars[i], entry)));
      }
      // the implied bound of y: an upper bound when kind is LE, a lower bound when GE
      long bound =
          kind == AtomicTrail.LE ? Math.floorDiv(rest, weight) : -Math.floorDiv(-rest, weight);
      if (kind == AtomicTrail.LE ? bound > a : bound < a) {
        if (Math.abs(Math.subtractExact(bound, a)) > 4096) {
          return false;
        }
        for (long u = Math.min(a, bound); u <= Math.max(a, bound); u++) {
          if (u != a
              && (kind == AtomicTrail.LE ? u > a : u < a)
              && !trail.excludedBefore(y, (int) u, entry, out)) {
            out.truncate(mark);
            return false;
          }
        }
      }
      // the value next to the bound reached, which the other bounds must keep out
      long beyond =
          kind == AtomicTrail.LE
              ? Math.addExact(Math.max(bound, a), 1)
              : Math.subtractExact(Math.min(bound, a), 1);
      long product = Math.multiplyExact(weight, beyond);
      long slack =
          upperSide
              ? Math.subtractExact(Math.subtractExact(product, 1), rest)
              : Math.subtractExact(Math.subtractExact(rest, 1), product);
      addLiftedBounds(trail, entry, vars, weights, own, merged, upperSide, slack, out);
      return true;
    } catch (ArithmeticException overflow) {
      out.truncate(mark);
      return false;
    }
  }

  /**
   * Adds to {@code out} the reason of a failure: the bounds that make the smallest sum exceed c, or
   * the largest one fall below it, now.
   *
   * @param trail the trail
   * @param vars the variables
   * @param weights their weights
   * @param c the right-hand side
   * @param lessOrEqual whether the relation contains {@code sum <= c}
   * @param greaterOrEqual whether the relation contains {@code sum >= c}
   * @param out where the reason entries are added
   * @return false when the bounds violate neither side
   */
  public static boolean explainFailure(
      AtomicTrail trail,
      IntVar[] vars,
      long[] weights,
      long c,
      boolean lessOrEqual,
      boolean greaterOrEqual,
      EntryList out) {
    int now = trail.size();
    long smallest = 0;
    long largest = 0;
    long slack;
    try {
      for (int i = 0; i < vars.length; i++) {
        long lo = Math.multiplyExact(weights[i], trail.minBefore(vars[i], now));
        long hi = Math.multiplyExact(weights[i], trail.maxBefore(vars[i], now));
        smallest = Math.addExact(smallest, Math.min(lo, hi));
        largest = Math.addExact(largest, Math.max(lo, hi));
      }
      slack =
          lessOrEqual && smallest > c
              ? Math.subtractExact(Math.subtractExact(smallest, c), 1)
              : Math.subtractExact(Math.subtractExact(c, 1), largest);
    } catch (ArithmeticException overflow) {
      return false;
    }
    boolean upperSide;
    if (lessOrEqual && smallest > c) {
      upperSide = true;
    } else if (greaterOrEqual && largest < c) {
      upperSide = false;
    } else {
      return false;
    }
    addLiftedBounds(trail, now, vars, weights, -1, null, upperSide, slack, out);
    return true;
  }

  /**
   * Adds to {@code out} the reason of an entry made by {@code sum w[i] * x[i] != c}: the other
   * occurrences fixed, which forbid one value of the entry's variable, and for a bound entry the
   * bound before it and the values it skipped. The reason is checked: the forbidden value must be
   * the one the entry removes, or the values a bound entry skips must be it or out already.
   *
   * @param trail the trail
   * @param entry an entry of one of the variables
   * @param vars the variables
   * @param weights their weights
   * @param c the right-hand side
   * @param out where the reason entries are added
   * @return false when an other occurrence was not fixed before the entry, or the entry does not
   *     follow
   */
  public static boolean explainNotEqual(
      AtomicTrail trail, int entry, IntVar[] vars, long[] weights, long c, EntryList out) {
    IntVar y = trail.variable(entry);
    int own = -1;
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == y) {
        own = i;
        break;
      }
    }
    if (own < 0 || weights[own] == 0 || !fixedBefore(trail, vars, own, entry)) {
      return false;
    }
    long rest = c;
    try {
      for (int i = 0; i < vars.length; i++) {
        if (i != own) {
          rest =
              Math.subtractExact(
                  rest, Math.multiplyExact(weights[i], trail.minBefore(vars[i], entry)));
        }
      }
    } catch (ArithmeticException overflow) {
      return false;
    }
    if (rest % weights[own] != 0) {
      return false;
    }
    long forbidden = rest / weights[own];
    int kind = trail.kind(entry);
    long a = trail.value(entry);
    int mark = out.size();
    if (kind == AtomicTrail.NE) {
      if (a != forbidden) {
        return false;
      }
    } else {
      boolean ge = kind == AtomicTrail.GE;
      long from = ge ? trail.minBefore(y, entry) : a + 1;
      long to = ge ? a - 1 : trail.maxBefore(y, entry);
      if (to - from > 4096) {
        return false;
      }
      for (long u = from; u <= to; u++) {
        if (u != forbidden && !trail.excludedBefore(y, (int) u, entry, out)) {
          out.truncate(mark);
          return false;
        }
      }
      if (ge) {
        trail.addLowerBound(y, entry, out);
      } else {
        trail.addUpperBound(y, entry, out);
      }
    }
    addFixed(trail, vars, own, entry, out);
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure of {@code sum w[i] * x[i] != c}: every variable
   * fixed now, to values that sum to c.
   *
   * @param trail the trail
   * @param vars the variables
   * @param weights their weights
   * @param c the right-hand side
   * @param out where the reason entries are added
   * @return false when a variable is not fixed, or the sum is not c
   */
  public static boolean explainNotEqualFailure(
      AtomicTrail trail, IntVar[] vars, long[] weights, long c, EntryList out) {
    int now = trail.size();
    if (!fixedBefore(trail, vars, -1, now)) {
      return false;
    }
    long sum = 0;
    try {
      for (int i = 0; i < vars.length; i++) {
        sum = Math.addExact(sum, Math.multiplyExact(weights[i], trail.minBefore(vars[i], now)));
      }
    } catch (ArithmeticException overflow) {
      return false;
    }
    if (sum != c) {
      return false;
    }
    addFixed(trail, vars, -1, now, out);
    return true;
  }

  private static boolean fixedBefore(AtomicTrail trail, IntVar[] vars, int skip, int position) {
    for (int i = 0; i < vars.length; i++) {
      if (i != skip && trail.minBefore(vars[i], position) != trail.maxBefore(vars[i], position)) {
        return false;
      }
    }
    return true;
  }

  private static void addFixed(
      AtomicTrail trail, IntVar[] vars, int skip, int position, EntryList out) {
    for (int i = 0; i < vars.length; i++) {
      if (i != skip) {
        trail.addLowerBound(vars[i], position, out);
        trail.addUpperBound(vars[i], position, out);
      }
    }
  }

  // ownOccurrence: y occurs with weights of both signs
  private static final int MIXED = -2;

  /**
   * Returns the occurrence of y with a nonzero weight the bound of y comes from, -1 when y has
   * none, or {@link #MIXED} when it occurs with weights of both signs.
   */
  private static int ownOccurrence(IntVar[] vars, long[] weights, IntVar y) {
    int own = -1;
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == y && weights[i] != 0) {
        if (own >= 0 && weights[own] > 0 != weights[i] > 0) {
          return MIXED;
        }
        own = i;
      }
    }
    return own;
  }

  // the summed weight of y's occurrences; ArithmeticException on overflow
  private static long mergedWeight(IntVar[] vars, long[] weights, IntVar y) {
    long w = 0;
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == y) {
        w = Math.addExact(w, weights[i]);
      }
    }
    return w;
  }

  /**
   * Adds the bounds of the occurrences other than {@code skip} and the occurrences of {@code
   * merged} (when not null) that bound one side of the relation, lifted (as in Ohrimenko, Stuckey
   * and Codish 2009): {@code slack} is how far the sum of their contributions may move against the
   * side before the reason no longer implies the propagation. The slack first drops whole terms,
   * those whose move from the initial bound costs least first, which leaves out as many terms as
   * the slack allows. What remains of it weakens the other terms, largest weights first, to the
   * earliest trail entry that still serves.
   */
  static void addLiftedBounds(
      AtomicTrail trail,
      int position,
      IntVar[] vars,
      long[] weights,
      int skip,
      IntVar merged,
      boolean upperSide,
      long slack,
      EntryList out) {
    long[] keys = null;
    long[] costs = null;
    int n = 0;
    for (int i = 0; i < vars.length; i++) {
      if (i == skip || weights[i] == 0 || vars[i] == merged) {
        continue;
      }
      long w = Math.abs(weights[i]);
      boolean lower = upperSide == weights[i] > 0;
      if (w > slack) {
        addBound(trail, vars[i], position, lower, out);
        continue;
      }
      long move = moveFromRoot(trail, vars[i], position, lower);
      if (move == 0) {
        continue;
      }
      if (keys == null) {
        keys = new long[vars.length];
        costs = new long[vars.length];
      }
      // the slack dropping the term takes; above the slack it can only be weakened
      costs[i] = move > slack / w ? Long.MAX_VALUE : w * move;
      keys[n++] = Math.min(costs[i], Integer.MAX_VALUE) << 32 | i;
    }
    if (n == 0) {
      return;
    }
    int k = 0;
    if (AtomicTrail.lifting()) {
      Arrays.sort(keys, 0, n);
      for (; k < n && costs[(int) keys[k]] <= slack; k++) {
        slack -= costs[(int) keys[k]];
      }
    }
    // the terms left, largest weights first
    int m = 0;
    for (int j = k; j < n; j++) {
      int i = (int) keys[j];
      keys[m++] = Math.min(Math.abs(weights[i]), Integer.MAX_VALUE) << 32 | i;
    }
    Arrays.sort(keys, 0, m);
    for (int j = m - 1; j >= 0; j--) {
      int i = (int) keys[j];
      long w = Math.abs(weights[i]);
      boolean lower = upperSide == weights[i] > 0;
      if (w > slack) {
        addBound(trail, vars[i], position, lower, out);
      } else {
        slack -= w * trail.addBoundWithin(vars[i], position, lower, slack / w, out);
      }
    }
  }

  // how far a variable's lower (or upper) bound just before a position is from its initial one
  private static long moveFromRoot(AtomicTrail trail, IntVar x, int position, boolean lower) {
    return lower
        ? (long) trail.minBefore(x, position) - trail.rootDomain(x).min()
        : (long) trail.rootDomain(x).max() - trail.maxBefore(x, position);
  }

  private static void addBound(
      AtomicTrail trail, IntVar x, int position, boolean lower, EntryList out) {
    if (lower) {
      trail.addLowerBound(x, position, out);
    } else {
      trail.addUpperBound(x, position, out);
    }
  }

  // the bounds of the other occurrences that bound the side of the relation the entry comes from
  private static void addOtherBounds(
      AtomicTrail trail,
      int entry,
      IntVar[] vars,
      long[] weights,
      int own,
      boolean upperSide,
      EntryList out) {
    for (int i = 0; i < vars.length; i++) {
      if (i == own || weights[i] == 0) {
        continue;
      }
      if (upperSide == weights[i] > 0) {
        trail.addLowerBound(vars[i], entry, out);
      } else {
        trail.addUpperBound(vars[i], entry, out);
      }
    }
  }
}
