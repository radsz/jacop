/*
 * IntervalVar.java
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

package org.jacop.constraints.cumulative;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.constraints.Alternative;
import org.jacop.constraints.And;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Span;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * An interval variable with optional presence, as in CP Optimizer and CP-SAT: a presence (a 0/1
 * variable), a start, a duration and an end, with end = start + duration. An absent interval takes
 * no part in the constraints over it; its start and duration then keep values, as a MiniZinc {@code
 * var opt int} keeps its {@code deopt}, but nothing uses them.
 *
 * <p>The constraints over intervals are built by the static methods and imposed as usual. They map
 * onto JaCoP's scheduling constraints, all of which explain their pruning under lazy clause
 * generation: {@link #noOverlap} is a {@link CumulativeUnary} whose resource uses are the
 * presences, {@link #cumulative} a {@link Cumulative} whose uses are the demands of the present
 * intervals, {@link #alternative} and {@link #span} are {@link Alternative} and {@link Span}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class IntervalVar {

  /** The presence, 1 when the interval is present. */
  public final IntVar presence;

  /** The start. */
  public final IntVar start;

  /** The duration. */
  public final IntVar duration;

  /** The end, start + duration. */
  public final IntVar end;

  /**
   * Creates an interval over existing variables. The relation end = start + duration is not
   * imposed; {@link #IntervalVar(Store, String, int, int, int, int, boolean)} imposes it.
   *
   * @param presence the presence, a 0/1 variable (a constant 1 for an interval always present)
   * @param start the start
   * @param duration the duration
   * @param end the end
   */
  public IntervalVar(IntVar presence, IntVar start, IntVar duration, IntVar end) {
    if (presence == null || start == null || duration == null || end == null) {
      throw new IllegalArgumentException(
          "IntervalVar: presence, start, duration and end are needed");
    }
    if (presence.min() < 0 || presence.max() > 1) {
      throw new IllegalArgumentException(
          "IntervalVar: presence " + presence + " is not a 0/1 variable");
    }
    this.presence = presence;
    this.start = start;
    this.duration = duration;
    this.end = end;
  }

  /**
   * Creates an interval with new variables and imposes end = start + duration.
   *
   * @param store the store
   * @param name the prefix of the variables' names
   * @param startMin the earliest start
   * @param endMax the latest end
   * @param durationMin the smallest duration, at least 0
   * @param durationMax the largest duration
   * @param optional whether the interval may be absent; otherwise its presence is the constant 1
   */
  public IntervalVar(
      Store store,
      String name,
      int startMin,
      int endMax,
      int durationMin,
      int durationMax,
      boolean optional) {
    this(
        presence(store, name, startMin, endMax, durationMin, durationMax, optional),
        new IntVar(store, name + ".start", startMin, endMax - durationMin),
        new IntVar(store, name + ".duration", durationMin, durationMax),
        new IntVar(store, name + ".end", startMin + durationMin, endMax));
    store.impose(new XplusYeqZ(start, duration, end));
  }

  // the presence of a new interval, once its bounds are checked
  private static IntVar presence(
      Store store,
      String name,
      int startMin,
      int endMax,
      int durationMin,
      int durationMax,
      boolean optional) {
    if (durationMin < 0 || durationMin > durationMax || (long) startMin + durationMin > endMax) {
      throw new IllegalArgumentException("IntervalVar " + name + ": no interval fits these bounds");
    }
    return optional ? new IntVar(store, name + ".presence", 0, 1) : new IntVar(store, 1, 1);
  }

  /**
   * Tells whether the interval may be absent.
   *
   * @return true when its presence is not fixed to 1
   */
  public boolean isOptional() {
    return presence.min() == 0;
  }

  private static IntVar[] starts(IntervalVar[] xs) {
    return Arrays.stream(xs).map(x -> x.start).toArray(IntVar[]::new);
  }

  private static IntVar[] durations(IntervalVar[] xs) {
    return Arrays.stream(xs).map(x -> x.duration).toArray(IntVar[]::new);
  }

  private static IntVar[] presences(IntervalVar[] xs) {
    return Arrays.stream(xs).map(x -> x.presence).toArray(IntVar[]::new);
  }

  /**
   * The present intervals do not overlap (a disjunctive resource).
   *
   * @param store the store
   * @param xs the intervals
   * @return a CumulativeUnary over the intervals whose resource uses are their presences
   */
  public static Constraint noOverlap(Store store, IntervalVar... xs) {
    return new CumulativeUnary(
        starts(xs), durations(xs), presences(xs), new IntVar(store, 1, 1), true);
  }

  /**
   * The present intervals use at most the capacity at any time, each its demand.
   *
   * @param store the store
   * @param xs the intervals
   * @param demands the demands, at least 0
   * @param capacity the capacity
   * @return the constraints to impose: the use of each optional interval (its demand when present,
   *     0 otherwise) and a Cumulative over the uses
   */
  public static List<Constraint> cumulative(
      Store store, IntervalVar[] xs, int[] demands, IntVar capacity) {
    if (xs.length != demands.length) {
      throw new IllegalArgumentException("cumulative: one demand per interval is needed");
    }
    List<Constraint> result = new ArrayList<>();
    IntVar[] uses = new IntVar[xs.length];
    for (int i = 0; i < xs.length; i++) {
      if (demands[i] < 0) {
        throw new IllegalArgumentException("cumulative: demand " + demands[i] + " is negative");
      }
      if (!xs[i].isOptional() || demands[i] == 0) {
        uses[i] = new IntVar(store, demands[i], demands[i]);
      } else {
        uses[i] = new IntVar(store, 0, 0);
        uses[i].addDom(demands[i], demands[i]);
        result.add(new XmulCeqZ(xs[i].presence, demands[i], uses[i]));
      }
    }
    result.add(new Cumulative(starts(xs), durations(xs), uses, capacity));
    return result;
  }

  /**
   * The master is present exactly when one of the options is, and then has its start and duration;
   * an absent master has duration 0.
   *
   * @param master the master interval
   * @param options the options
   * @return an Alternative
   */
  public static Constraint alternative(IntervalVar master, IntervalVar... options) {
    return new Alternative(
        master.presence,
        master.start,
        master.duration,
        presences(options),
        starts(options),
        durations(options));
  }

  /**
   * The master is present exactly when one of the intervals is, and then spans the present ones: it
   * starts with the first and ends with the last; an absent master has duration 0.
   *
   * @param master the master interval
   * @param xs the intervals
   * @return a Span
   */
  public static Constraint span(IntervalVar master, IntervalVar... xs) {
    return new Span(
        master.presence, master.start, master.duration, presences(xs), starts(xs), durations(xs));
  }

  /**
   * When both intervals are present, a ends at least delay before b starts.
   *
   * @param a the first interval
   * @param b the second interval
   * @param delay the least time from the end of a to the start of b
   * @return the precedence, conditional on the presences of optional intervals
   */
  public static Constraint endBeforeStart(IntervalVar a, IntervalVar b, int delay) {
    PrimitiveConstraint precedence = new XplusClteqZ(a.end, delay, b.start);
    List<PrimitiveConstraint> present = new ArrayList<>();
    for (IntervalVar x : new IntervalVar[] {a, b}) {
      if (x.isOptional()) {
        present.add(new XeqC(x.presence, 1));
      }
    }
    if (present.isEmpty()) {
      return precedence;
    }
    PrimitiveConstraint condition = present.size() == 1 ? present.get(0) : new And(present);
    return new IfThen(condition, precedence);
  }

  @Override
  public String toString() {
    return "interval(" + presence + ", " + start + ", " + duration + ", " + end + ")";
  }
}
