/*
 * Span.java
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

/**
 * Span constraint over optional intervals (MiniZinc {@code span}, CP Optimizer {@code span}): the
 * master interval (p0, s0, d0) is present if and only if at least one of the optional intervals
 * (p[i], s[i], d[i]) is, and then it starts at the earliest start and ends (s0 + d0) at the latest
 * end (s[i] + d[i]) of the present intervals. An absent master has duration 0.
 *
 * <p>Pruning, on bounds: presence of the master from the presences; while the master is present, s0
 * lies between the least start of the candidates and the least latest start of the present
 * intervals, and its end between the greatest earliest end of the present intervals and the
 * greatest end of the candidates; a present interval starts no earlier than s0 and ends no later
 * than the end of the master; a candidate that could not do so is made absent; when only one
 * candidate can give the master its start (or end), it is made present and its bounds follow. The
 * conditional reasoning is that of Laborie and Rogerie (FLAIRS 2008).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Span extends AbstractOptionalIntervals implements Copyable<Span> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs a span constraint.
   *
   * @param p0 presence of the master interval (0/1).
   * @param s0 start of the master interval.
   * @param d0 duration of the master interval.
   * @param p presences of the optional intervals (0/1).
   * @param s starts of the optional intervals.
   * @param d durations of the optional intervals.
   */
  public Span(IntVar p0, IntVar s0, IntVar d0, IntVar[] p, IntVar[] s, IntVar[] d) {
    super(p0, s0, d0, p, s, d, "Span");
    this.numberId = idNumber.incrementAndGet();
  }

  @Override
  public void consistency(Store store) {
    do {
      store.propagationHasOccurred = false;

      int ones = 0;
      int candidates = 0;
      int candidate = -1;
      for (int i = 0; i < n; i++) {
        if (p[i].min() == 1) {
          ones++;
        }
        if (p[i].max() == 1) {
          candidates++;
          candidate = i;
        }
      }
      if (ones > 0) {
        fix(store, p0, 1);
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
      if (p0.min() == 1 && candidates == 1 && ones == 0) {
        fix(store, p[candidate], 1);
        continue;
      }

      // a candidate is made absent if, present, it would start before the master or end after it
      long masterEndHi = (long) s0.max() + d0.max();
      for (int i = 0; i < n; i++) {
        if (p[i].min() == 0
            && p[i].max() == 1
            && (s[i].max() < s0.min() || (long) s[i].min() + d[i].min() > masterEndHi)) {
          fix(store, p[i], 0);
        }
      }
      if (store.propagationHasOccurred) {
        continue;
      }

      // bounds of the master's start and end as if it were present
      long startLo = Long.MAX_VALUE;
      long startHi = ones > 0 ? Long.MAX_VALUE : Long.MIN_VALUE;
      long endLo = ones > 0 ? Long.MIN_VALUE : Long.MAX_VALUE;
      long endHi = Long.MIN_VALUE;
      for (int i = 0; i < n; i++) {
        if (p[i].max() == 0) {
          continue;
        }
        long earliestEnd = (long) s[i].min() + d[i].min();
        long latestEnd = (long) s[i].max() + d[i].max();
        startLo = Math.min(startLo, s[i].min());
        endHi = Math.max(endHi, latestEnd);
        if (ones > 0) {
          if (p[i].min() == 1) {
            startHi = Math.min(startHi, s[i].max());
            endLo = Math.max(endLo, earliestEnd);
          }
        } else {
          startHi = Math.max(startHi, s[i].max());
          endLo = Math.min(endLo, earliestEnd);
        }
      }
      startLo = Math.max(startLo, s0.min());
      startHi = Math.min(startHi, s0.max());
      endLo = Math.max(endLo, (long) s0.min() + d0.min());
      endHi = Math.min(endHi, masterEndHi);

      if (p0.min() == 0) {
        // the master may still be absent: only its presence and its duration (0 when absent)
        if (startLo > startHi || endLo > endHi) {
          fix(store, p0, 0);
          continue;
        }
        restrict(store, d0, Math.min(0, endLo - startHi), Math.max(0, endHi - startLo));
        if (!d0.domain.contains(0)) {
          fix(store, p0, 1);
        }
        continue;
      }

      restrict(store, s0, startLo, startHi);
      // s0 + d0 within [endLo, endHi]
      restrict(store, d0, endLo - s0.max(), endHi - s0.min());
      restrict(store, s0, endLo - d0.max(), endHi - d0.min());
      long startMin = s0.min();
      long startMax = s0.max();
      long endMin = Math.max(endLo, startMin + d0.min());
      long endMax = Math.min(endHi, startMax + d0.max());

      // present intervals lie within the master; count who can give it its start and its end
      int starters = 0;
      int starter = -1;
      int enders = 0;
      int ender = -1;
      for (int i = 0; i < n; i++) {
        if (p[i].max() == 0) {
          continue;
        }
        if (p[i].min() == 1) {
          restrict(store, s[i], startMin, endMax - d[i].min());
          restrict(store, d[i], d[i].min(), endMax - s[i].min());
        }
        if (s[i].min() <= startMax) {
          starters++;
          starter = i;
        }
        if ((long) s[i].max() + d[i].max() >= endMin) {
          enders++;
          ender = i;
        }
      }
      if (starters == 0 || enders == 0) {
        throw Store.failException;
      }
      if (starters == 1) {
        fix(store, p[starter], 1);
        restrict(store, s[starter], startMin, startMax);
      }
      if (enders == 1) {
        fix(store, p[ender], 1);
        restrict(store, s[ender], endMin - d[ender].max(), endMax - d[ender].min());
        restrict(store, d[ender], endMin - s[ender].max(), endMax - s[ender].min());
      }
    } while (store.propagationHasOccurred);
  }

  @Override
  boolean holds() {
    long start = Long.MAX_VALUE;
    long end = Long.MIN_VALUE;
    boolean any = false;
    for (int i = 0; i < n; i++) {
      if (p[i].value() == 1) {
        any = true;
        start = Math.min(start, s[i].value());
        end = Math.max(end, (long) s[i].value() + d[i].value());
      }
    }
    if (!any) {
      return p0.value() == 0 && d0.value() == 0;
    }
    return p0.value() == 1 && s0.value() == start && (long) s0.value() + d0.value() == end;
  }

  @Override
  public String toString() {
    return describe("Span");
  }

  @Override
  public Span copy(VarMap map) {
    return new Span(map.get(p0), map.get(s0), map.get(d0), map.get(p), map.get(s), map.get(d));
  }
}
