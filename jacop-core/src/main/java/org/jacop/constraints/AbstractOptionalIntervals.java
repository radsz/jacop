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
        new String[] {"p0", "s0", "d0", "p", "s", "d"}, new Object[][] {{p0}, {s0}, {d0}, p, s, d});
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
  static void equal(Store store, IntVar x, IntVar y) {
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
