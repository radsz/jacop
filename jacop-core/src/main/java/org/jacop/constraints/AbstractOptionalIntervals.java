/*
 * AbstractOptionalIntervals.java
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

import java.util.Arrays;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Common part of {@link Alternative} and {@link Span}: a master interval (presence p0, start s0,
 * duration d0) and n optional intervals (presence p[i], start s[i], duration d[i]), with the
 * semantics of the MiniZinc globals over optional starts. The start of an absent interval is free
 * and the duration of an absent master is 0.
 *
 * <p>Presence reasoning follows Laborie and Rogerie ("Reasoning with Conditional Time-Intervals",
 * FLAIRS 2008): the bounds of an interval are reasoned about as if it were present, and an interval
 * whose conditional bounds are empty is made absent. The start and duration of an interval are only
 * pruned once it is present, since FlatZinc may share the start of an optional interval with other
 * constraints (the free value of an absent interval is still a value of that variable).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractOptionalIntervals extends Constraint implements SatisfiedPresent {

  /** Presence of the master interval, a 0/1 variable. */
  final IntVar p0;

  /** Start of the master interval. */
  final IntVar s0;

  /** Duration of the master interval. */
  final IntVar d0;

  /** Presence of the optional intervals, 0/1 variables. */
  final IntVar[] p;

  /** Starts of the optional intervals. */
  final IntVar[] s;

  /** Durations of the optional intervals. */
  final IntVar[] d;

  final int n;

  AbstractOptionalIntervals(
      IntVar p0, IntVar s0, IntVar d0, IntVar[] p, IntVar[] s, IntVar[] d, String name) {
    checkInputForNullness(
        new String[] {"p0", "s0", "d0", "p", "s", "d"},
        new Object[] {p0},
        new Object[] {s0},
        new Object[] {d0},
        p,
        s,
        d);
    if (p.length != s.length || s.length != d.length) {
      throw new IllegalArgumentException(
          name + ": presences, starts and durations must have the same length.");
    }
    if (p0.min() < 0 || p0.max() > 1) {
      throw new IllegalArgumentException(name + ": presence " + p0 + " is not a 0/1 variable.");
    }
    for (IntVar b : p) {
      if (b.min() < 0 || b.max() > 1) {
        throw new IllegalArgumentException(name + ": presence " + b + " is not a 0/1 variable.");
      }
    }
    this.p0 = p0;
    this.s0 = s0;
    this.d0 = d0;
    this.p = Arrays.copyOf(p, p.length);
    this.s = Arrays.copyOf(s, s.length);
    this.d = Arrays.copyOf(d, d.length);
    this.n = p.length;
    this.queueIndex = 1;
    setScope(
        Stream.concat(
            Stream.of(p0, s0, d0),
            Stream.concat(Arrays.stream(p), Stream.concat(Arrays.stream(s), Arrays.stream(d)))));
  }

  /**
   * The relation on a complete assignment.
   *
   * @return true if the fixed values satisfy the constraint.
   */
  abstract boolean holds();

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    if (!p0.singleton() || !s0.singleton() || !d0.singleton()) {
      return false;
    }
    for (int i = 0; i < n; i++) {
      if (!p[i].singleton() || !s[i].singleton() || !d[i].singleton()) {
        return false;
      }
    }
    return holds();
  }

  /** It sets a 0/1 variable, failing if it has the other value. */
  static void fix(Store store, IntVar b, int value) {
    if (!b.domain.contains(value)) {
      throw Store.failException;
    }
    if (!b.singleton()) {
      b.domain.in(store.level, b, value, value);
    }
  }

  /** It restricts x to [lo, hi], failing if no value of x is left. */
  static void restrict(Store store, IntVar x, long lo, long hi) {
    if (lo <= x.min() && hi >= x.max()) {
      return;
    }
    if (lo > hi || lo > x.max() || hi < x.min()) {
      throw Store.failException;
    }
    x.domain.in(store.level, x, (int) Math.max(lo, x.min()), (int) Math.min(hi, x.max()));
  }

  /** It makes the domains of x and y equal. */
  static void unify(Store store, IntVar x, IntVar y) {
    if (x == y) {
      return;
    }
    if (!x.domain.isIntersecting(y.domain)) {
      throw Store.failException;
    }
    x.domain.in(store.level, x, y.domain);
    y.domain.in(store.level, y, x.domain);
  }

  /** Whether x and y have a common value. */
  static boolean intersect(IntVar x, IntVar y) {
    return x == y || x.domain.isIntersecting(y.domain);
  }

  // lazy clause generation: helpers of the explanations of the subclasses

  /** The most values an explanation of an equality walks over before it gives up. */
  private static final int EQUAL_SPAN = 256;

  /**
   * The value a trail entry gives a 0/1 variable.
   *
   * @return 1, 0, or -1 when the atom does not fix it
   */
  static int fixedTo(AtomicTrail trail, int entry) {
    int v = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> v >= 1 ? 1 : -1;
      case AtomicTrail.LE -> v <= 0 ? 0 : -1;
      default -> v == 0 ? 1 : v == 1 ? 0 : -1;
    };
  }

  static boolean presentBefore(AtomicTrail trail, IntVar b, int position) {
    return trail.minBefore(b, position) >= 1;
  }

  static boolean absentBefore(AtomicTrail trail, IntVar b, int position) {
    return trail.maxBefore(b, position) <= 0;
  }

  /**
   * Explains an atom on x that x = y implies, by the domain of y and the holes of x just before the
   * entry. Gives up (returns false) on long runs of holes.
   */
  static boolean explainEqual(AtomicTrail trail, int entry, IntVar x, IntVar y, EntryList out) {
    int v = trail.value(entry);
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return excludedEither(trail, entry, x, y, v, out);
    }
    boolean lower = kind == AtomicTrail.GE;
    int yb = lower ? trail.minBefore(y, entry) : trail.maxBefore(y, entry);
    if (lower ? yb >= v : yb <= v) {
      trail.addBoundReaching(y, entry, lower, v, out);
      return true;
    }
    // the values between y's bound and v are out of x or y
    if (Math.abs((long) v - yb) > EQUAL_SPAN) {
      return false;
    }
    trail.addBoundReaching(y, entry, lower, yb, out);
    for (int w = yb; w != v; w += lower ? 1 : -1) {
      if (!excludedEither(trail, entry, x, y, w, out)) {
        return false;
      }
    }
    return true;
  }

  private static boolean excludedEither(
      AtomicTrail trail, int entry, IntVar x, IntVar y, int w, EntryList out) {
    return trail.excludedBefore(y, w, entry, out) || trail.excludedBefore(x, w, entry, out);
  }

  /**
   * Explains that two intervals of values cannot meet, by their bounds just before a position.
   *
   * @return false when the bounds overlap
   */
  static boolean explainApart(AtomicTrail trail, int position, IntVar x, IntVar y, EntryList out) {
    int xMax = trail.maxBefore(x, position);
    int yMax = trail.maxBefore(y, position);
    if (xMax < trail.minBefore(y, position)) {
      trail.addUpperBound(x, position, out);
      trail.addBoundReaching(y, position, true, (long) xMax + 1, out);
      return true;
    }
    if (yMax < trail.minBefore(x, position)) {
      trail.addUpperBound(y, position, out);
      trail.addBoundReaching(x, position, true, (long) yMax + 1, out);
      return true;
    }
    return false;
  }

  /**
   * Explains an atom on a presence: the master's by the intervals' presences, an interval's by the
   * master and the other intervals, or by {@link #explainAbsence}.
   */
  final boolean explainPresences(AtomicTrail trail, int entry, IntVar y, EntryList out) {
    int mark = out.size();
    if (y == p0 && explainMasterPresence(trail, entry, out)) {
      return true;
    }
    out.truncate(mark);
    for (int i = 0; i < n; i++) {
      if (y == p[i] && explainPresence(trail, entry, i, out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  /** The master is absent as all intervals are, or present as one interval is. */
  boolean explainMasterPresence(AtomicTrail trail, int entry, EntryList out) {
    int value = fixedTo(trail, entry);
    if (value == 0) {
      return allAbsent(trail, entry, -1, out);
    }
    return value == 1 && somePresent(trail, entry, -1, out);
  }

  private boolean explainPresence(AtomicTrail trail, int entry, int i, EntryList out) {
    int value = fixedTo(trail, entry);
    if (value == 1) {
      // the last candidate of a present master
      if (presentBefore(trail, p0, entry) && allAbsent(trail, entry, i, out)) {
        trail.addLowerBound(p0, entry, out);
        return true;
      }
      return false;
    }
    if (value != 0) {
      return false;
    }
    if (absentBefore(trail, p0, entry)) {
      trail.addUpperBound(p0, entry, out);
      return true;
    }
    return explainAbsence(trail, entry, i, out);
  }

  /** Explains that interval i is absent while the master may be present. */
  abstract boolean explainAbsence(AtomicTrail trail, int entry, int i, EntryList out);

  /** Explains a failure of a present master whose intervals are all absent. */
  final boolean explainNoCandidate(AtomicTrail trail, int position, EntryList out) {
    if (presentBefore(trail, p0, position) && allAbsent(trail, position, -1, out)) {
      trail.addLowerBound(p0, position, out);
      return true;
    }
    return false;
  }

  /** Every interval but skip is absent: adds their absences, or nothing and false. */
  final boolean allAbsent(AtomicTrail trail, int position, int skip, EntryList out) {
    int mark = out.size();
    for (int i = 0; i < n; i++) {
      if (i != skip) {
        if (!absentBefore(trail, p[i], position)) {
          out.truncate(mark);
          return false;
        }
        trail.addUpperBound(p[i], position, out);
      }
    }
    return true;
  }

  /** Some interval but skip is present: adds its presence, or nothing and false. */
  final boolean somePresent(AtomicTrail trail, int position, int skip, EntryList out) {
    for (int i = 0; i < n; i++) {
      if (i != skip && presentBefore(trail, p[i], position)) {
        trail.addLowerBound(p[i], position, out);
        return true;
      }
    }
    return false;
  }

  String describe(String name) {
    StringBuilder result = new StringBuilder(id()).append(" : ").append(name).append("(");
    result.append(p0).append(", ").append(s0).append(", ").append(d0).append(", [");
    for (int i = 0; i < n; i++) {
      result.append(p[i]).append(", ").append(s[i]).append(", ").append(d[i]);
      if (i < n - 1) {
        result.append("; ");
      }
    }
    return result.append("])").toString();
  }
}
