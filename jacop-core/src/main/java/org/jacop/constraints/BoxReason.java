/*
 * BoxReason.java
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

package org.jacop.constraints;

import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations for lazy clause generation of a propagator that reads only the bounds of its
 * variables and checks whether a box of bounds has a solution, as a bounds(Z) consistent propagator
 * does. The reason of an atom is the box of the bounds just before it with the atom negated, which
 * the check finds without solution; each bound that can go back to its initial value while the box
 * stays without solution is left out, one at a time (a deletion filter over the bounds, as in J. L.
 * de Siqueira N. and J.-F. Puget, "Explanation-based generalisation of failures", ECAI 1988, and
 * the deletion filter of J. W. Chinneck and E. W. Dravnieks, "Locating minimal infeasible
 * constraint sets in linear programs", ORSA J. on Computing 3(2), 1991). The holes of the domains
 * are never read, so a bound that skipped holes is explained as the bound before them together with
 * the holes.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class BoxReason {

  /** Whether a box of bounds has no solution. */
  @FunctionalInterface
  interface Check {

    /**
     * Tells whether the constraint has no solution with every variable k within lo[k]..hi[k].
     *
     * @param lo the lower bounds, by variable
     * @param hi the upper bounds, by variable
     * @return true when there is no solution in the box
     */
    boolean infeasible(long[] lo, long[] hi);
  }

  private final IntVar[] vars;
  private final Check check;
  private final int relaxLimit;
  private final long rootLimit;
  private final int n;
  private final long[] lo;
  private final long[] hi;
  private final boolean[] fixedLo;
  private final boolean[] fixedHi;

  /**
   * It creates explanations over the given variables, each at most once.
   *
   * @param vars the variables the check reads, in its order
   * @param check the check of a box
   * @param relaxLimit bounds are relaxed only for at most this many variables
   * @param rootLimit a bound is relaxed only to an initial bound of at most this magnitude
   */
  BoxReason(IntVar[] vars, Check check, int relaxLimit, long rootLimit) {
    this.vars = vars.clone();
    this.check = check;
    this.relaxLimit = relaxLimit;
    this.rootLimit = rootLimit;
    this.n = vars.length;
    lo = new long[n];
    hi = new long[n];
    fixedLo = new boolean[n];
    fixedHi = new boolean[n];
  }

  /**
   * Explains an atom on one of the variables.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param out where the reason is added
   * @return false when the box with the atom negated has a solution, or the variable occurs twice
   */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int i = -1;
    for (int k = 0; k < n; k++) {
      if (vars[k] == y) {
        if (i >= 0) {
          return false;
        }
        i = k;
      }
    }
    if (i < 0) {
      return false;
    }
    int kind = trail.kind(entry);
    int value = trail.value(entry);
    if (kind == AtomicTrail.NE) {
      load(trail, entry);
      lo[i] = value;
      hi[i] = value;
      fixedLo[i] = true;
      fixedHi[i] = true;
      return check.infeasible(lo, hi) && cite(trail, entry, out);
    }
    boolean lower = kind == AtomicTrail.GE;
    int skipped = trail.skippedBound(entry);
    for (int bound : skipped == value ? new int[] {value} : new int[] {value, skipped}) {
      load(trail, entry);
      if (lower) {
        hi[i] = Math.min(hi[i], (long) bound - 1);
        fixedHi[i] = true;
      } else {
        lo[i] = Math.max(lo[i], (long) bound + 1);
        fixedLo[i] = true;
      }
      if (check.infeasible(lo, hi)) {
        cite(trail, entry, out);
        if (bound != value) {
          trail.addSkippedHoles(entry, bound, out);
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Explains a failure by the box of the bounds now.
   *
   * @param trail the trail
   * @param out where the reason is added
   * @return false when the box has a solution
   */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    for (int k = 0; k < n; k++) {
      for (int q = k + 1; q < n; q++) {
        if (vars[k] == vars[q]) {
          return false;
        }
      }
    }
    int now = trail.size();
    load(trail, now);
    return check.infeasible(lo, hi) && cite(trail, now, out);
  }

  private void load(AtomicTrail trail, int position) {
    for (int k = 0; k < n; k++) {
      lo[k] = trail.minBefore(vars[k], position);
      hi[k] = trail.maxBefore(vars[k], position);
      fixedLo[k] = false;
      fixedHi[k] = false;
    }
  }

  // relaxes the bounds that may go back to their initial values, then cites the others
  private boolean cite(AtomicTrail trail, int position, EntryList out) {
    if (n <= relaxLimit) {
      for (int k = 0; k < n; k++) {
        if (!fixedLo[k]) {
          long keep = lo[k];
          long root = trail.rootDomain(vars[k]).min();
          if (root < keep && Math.abs(root) <= rootLimit) {
            lo[k] = root;
            if (!check.infeasible(lo, hi)) {
              lo[k] = keep;
            }
          }
        }
        if (!fixedHi[k]) {
          long keep = hi[k];
          long root = trail.rootDomain(vars[k]).max();
          if (root > keep && Math.abs(root) <= rootLimit) {
            hi[k] = root;
            if (!check.infeasible(lo, hi)) {
              hi[k] = keep;
            }
          }
        }
      }
    }
    for (int k = 0; k < n; k++) {
      if (!fixedLo[k]) {
        trail.addBoundReaching(vars[k], position, true, lo[k], out);
      }
      if (!fixedHi[k]) {
        trail.addBoundReaching(vars[k], position, false, hi[k], out);
      }
    }
    return true;
  }
}
