/*
 * Alternative.java
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

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Alternative constraint over optional intervals (MiniZinc {@code alternative}, CP Optimizer {@code
 * alternative}): the master interval (p0, s0, d0) is present if and only if exactly one of the
 * optional intervals (p[i], s[i], d[i]) is, and then it has the start and the duration of that
 * interval. No other interval is present, and an absent master has duration 0.
 *
 * <p>Pruning: the presences are an exact-one constraint with p0; an interval whose start or
 * duration has no common value with the master's is made absent; once one interval is present the
 * domains of its start and duration are made equal to the master's; while the master is present and
 * the chosen interval is not known, the bounds of s0 and d0 are the hull of the conditional bounds
 * of the candidates (Laborie and Rogerie, FLAIRS 2008).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Alternative extends AbstractOptionalIntervals
    implements Copyable<Alternative>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs an alternative constraint.
   *
   * @param p0 presence of the master interval (0/1).
   * @param s0 start of the master interval.
   * @param d0 duration of the master interval.
   * @param p presences of the optional intervals (0/1).
   * @param s starts of the optional intervals.
   * @param d durations of the optional intervals.
   */
  public Alternative(IntVar p0, IntVar s0, IntVar d0, IntVar[] p, IntVar[] s, IntVar[] d) {
    super(p0, s0, d0, p, s, d, "Alternative");
    this.numberId = idNumber.incrementAndGet();
  }

  @Override
  public void consistency(Store store) {
    do {
      store.propagationHasOccurred = false;

      int ones = 0;
      int one = -1;
      int candidates = 0;
      int candidate = -1;
      for (int i = 0; i < n; i++) {
        if (p[i].min() == 1) {
          ones++;
          one = i;
        }
        if (p[i].max() == 1) {
          candidates++;
          candidate = i;
        }
      }

      if (ones > 1) {
        throw Store.failException;
      }
      if (ones == 1) {
        fix(store, p0, 1);
        for (int i = 0; i < n; i++) {
          if (i != one) {
            fix(store, p[i], 0);
          }
        }
        unify(store, s0, s[one]);
        unify(store, d0, d[one]);
        continue;
      }
      if (candidates == 0) {
        fix(store, p0, 0);
      }
      if (p0.max() == 0) {
        for (int i = 0; i < n; i++) {
          fix(store, p[i], 0);
        }
        restrict(store, d0, 0, 0);
        continue;
      }
      if (p0.min() == 1 && candidates == 1) {
        fix(store, p[candidate], 1);
        continue;
      }

      // no interval is present yet: drop the candidates that cannot be the master
      long startLo = Long.MAX_VALUE;
      long startHi = Long.MIN_VALUE;
      long durationLo = Long.MAX_VALUE;
      long durationHi = Long.MIN_VALUE;
      for (int i = 0; i < n; i++) {
        if (p[i].max() == 0) {
          continue;
        }
        if (!intersect(s0, s[i]) || !intersect(d0, d[i])) {
          fix(store, p[i], 0);
          continue;
        }
        startLo = Math.min(startLo, Math.max(s0.min(), s[i].min()));
        startHi = Math.max(startHi, Math.min(s0.max(), s[i].max()));
        durationLo = Math.min(durationLo, Math.max(d0.min(), d[i].min()));
        durationHi = Math.max(durationHi, Math.min(d0.max(), d[i].max()));
      }
      if (store.propagationHasOccurred) {
        continue;
      }

      if (p0.min() == 1) {
        restrict(store, s0, startLo, startHi);
        restrict(store, d0, durationLo, durationHi);
      } else {
        // an absent master has duration 0, a present one the duration of a candidate
        restrict(store, d0, Math.min(0, durationLo), Math.max(0, durationHi));
        if (!d0.domain.contains(0)) {
          fix(store, p0, 1);
        }
      }
    } while (store.propagationHasOccurred);
  }

  /**
   * Explains an atom by the rule of alternative that gives it: the presences that fix the others,
   * the present interval that the master equals, the bounds of two intervals that cannot meet, or
   * the hull of the candidates' bounds. Anything else is left to the generic reason.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    if (explainPresences(trail, entry, y, out)) {
      return true;
    }
    int mark = out.size();
    if ((y == s0 || y == d0) && explainMaster(trail, entry, y == s0, out)) {
      return true;
    }
    out.truncate(mark);
    for (int i = 0; i < n; i++) {
      if ((y == s[i] || y == d[i]) && presentBefore(trail, p[i], entry)) {
        trail.addLowerBound(p[i], entry, out);
        if (explainEqual(trail, entry, y, y == s[i] ? s0 : d0, out)) {
          return true;
        }
      }
      out.truncate(mark);
    }
    return false;
  }

  /** Explains a failure by two present intervals, or a present master without candidates. */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int position = trail.size();
    int first = -1;
    for (int i = 0; i < n; i++) {
      if (presentBefore(trail, p[i], position)) {
        if (first >= 0) {
          trail.addLowerBound(p[first], position, out);
          trail.addLowerBound(p[i], position, out);
          return true;
        }
        first = i;
      }
    }
    return explainNoCandidate(trail, position, out);
  }

  @Override
  boolean explainMasterPresence(AtomicTrail trail, int entry, EntryList out) {
    if (super.explainMasterPresence(trail, entry, out)) {
      return true;
    }
    if (fixedTo(trail, entry) != 1) {
      return false;
    }
    // an absent master has duration 0
    if (trail.minBefore(d0, entry) > 0) {
      trail.addBoundReaching(d0, entry, true, 1, out);
      return true;
    }
    if (trail.maxBefore(d0, entry) < 0) {
      trail.addBoundReaching(d0, entry, false, -1, out);
      return true;
    }
    return trail.excludedBefore(d0, 0, entry, out);
  }

  @Override
  boolean explainAbsence(AtomicTrail trail, int entry, int i, EntryList out) {
    return somePresent(trail, entry, i, out)
        || explainApart(trail, entry, s0, s[i], out)
        || explainApart(trail, entry, d0, d[i], out);
  }

  private boolean explainMaster(AtomicTrail trail, int entry, boolean start, EntryList out) {
    IntVar y = start ? s0 : d0;
    IntVar[] other = start ? s : d;
    for (int i = 0; i < n; i++) {
      if (presentBefore(trail, p[i], entry)) {
        trail.addLowerBound(p[i], entry, out);
        return explainEqual(trail, entry, y, other[i], out);
      }
    }
    int kind = trail.kind(entry);
    int v = trail.value(entry);
    // the duration of an absent master is 0
    boolean zeroHolds = kind == AtomicTrail.GE ? v <= 0 : kind == AtomicTrail.LE ? v >= 0 : v != 0;
    if (!start && absentBefore(trail, p0, entry)) {
      if (!zeroHolds) {
        return false;
      }
      trail.addUpperBound(p0, entry, out);
      return true;
    }
    if (kind == AtomicTrail.NE) {
      return false;
    }
    // the hull of the candidates, for a present master; for a master that may be absent, the
    // duration's hull with 0
    boolean present = presentBefore(trail, p0, entry);
    if (!present && (start || !zeroHolds)) {
      return false;
    }
    boolean lower = kind == AtomicTrail.GE;
    for (int i = 0; i < n; i++) {
      if (absentBefore(trail, p[i], entry)) {
        trail.addUpperBound(p[i], entry, out);
      } else if (lower
          ? trail.minBefore(other[i], entry) >= v
          : trail.maxBefore(other[i], entry) <= v) {
        trail.addBoundReaching(other[i], entry, lower, v, out);
      } else {
        return false;
      }
    }
    if (present) {
      trail.addLowerBound(p0, entry, out);
    }
    return true;
  }

  @Override
  boolean holds() {
    int present = -1;
    for (int i = 0; i < n; i++) {
      if (p[i].value() == 1) {
        if (present >= 0) {
          return false;
        }
        present = i;
      }
    }
    if (present < 0) {
      return p0.value() == 0 && d0.value() == 0;
    }
    return p0.value() == 1 && s0.value() == s[present].value() && d0.value() == d[present].value();
  }

  @Override
  public String toString() {
    return describe("Alternative");
  }

  @Override
  public Alternative copy(VarMap map) {
    return new Alternative(
        map.get(p0), map.get(s0), map.get(d0), map.get(p), map.get(s), map.get(d));
  }
}
