/*
 * ViolationTest.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.search.ls;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.BiFunction;
import java.util.stream.Stream;
import org.jacop.api.Violation;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.ChannelImply;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.constraints.Max;
import org.jacop.constraints.Min;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Checks the {@link Violation} of each constraint against propagation: for random assignments, the
 * violation is 0 exactly when the constraint, imposed over the assigned values, propagates without
 * failure.
 */
class ViolationTest {

  private static final int TRIALS = 300;

  /** A constraint over variables 0..n-1, each with domain min..max. */
  record Case(String name, int n, int min, int max, BiFunction<Store, IntVar[], Constraint> make) {
    @Override
    public String toString() {
      return name;
    }
  }

  static Stream<Case> cases() {
    List<Case> cs = new ArrayList<>();
    cs.add(new Case("AndBoolSimple", 3, 0, 1, (s, x) -> new AndBoolSimple(x[0], x[1], x[2])));
    cs.add(new Case("OrBoolSimple", 3, 0, 1, (s, x) -> new OrBoolSimple(x[0], x[1], x[2])));
    cs.add(new Case("AndBoolVector", 5, 0, 1, (s, x) -> new AndBoolVector(head(x, 4), x[4])));
    cs.add(new Case("OrBoolVector", 5, 0, 1, (s, x) -> new OrBoolVector(head(x, 4), x[4])));
    cs.add(new Case("XorBool", 4, 0, 1, (s, x) -> new XorBool(head(x, 3), x[3])));
    cs.add(
        new Case(
            "ElementInteger",
            2,
            0,
            5,
            (s, x) -> new ElementInteger(x[0], new int[] {3, 1, 4, 1, 5}, x[1], -1)));
    cs.add(
        new Case(
            "ElementVariableFast",
            5,
            0,
            3,
            (s, x) -> new ElementVariableFast(x[0], new IntVar[] {x[1], x[2], x[3]}, x[4], 0)));
    cs.add(new Case("Alldistinct", 4, 0, 4, (s, x) -> new Alldistinct(x)));
    cs.add(new Case("Alldifferent", 4, 0, 4, (s, x) -> new Alldifferent(x)));
    cs.add(
        new Case(
            "AlldifferentExcept",
            4,
            0,
            3,
            (s, x) -> new AlldifferentExcept(x, new IntervalDomain(0, 0))));
    cs.add(new Case("Max", 4, -2, 2, (s, x) -> new Max(head(x, 3), x[3])));
    cs.add(new Case("Min", 4, -2, 2, (s, x) -> new Min(head(x, 3), x[3])));
    cs.add(new Case("XmulYeqZ", 3, -3, 3, (s, x) -> new XmulYeqZ(x[0], x[1], x[2])));
    cs.add(
        new Case(
            "ChannelReif",
            4,
            0,
            3,
            (s, x) -> new ChannelReif(x[0], bools(s, x, 1, 3), new int[] {0, 1, 2})));
    cs.add(
        new Case(
            "ChannelImply",
            4,
            0,
            3,
            (s, x) -> new ChannelImply(x[0], bools(s, x, 1, 3), new int[] {0, 1, 2})));
    cs.add(new Case("Count", 5, 0, 3, (s, x) -> new Count(head(x, 4), x[4], 1)));
    cs.add(new Case("CountVar", 6, 0, 3, (s, x) -> new CountVar(head(x, 4), x[4], x[5])));
    cs.add(new Case("CountBounds", 4, 0, 2, (s, x) -> new CountBounds(x, 1, 1, 2)));
    cs.add(new Case("AtMost", 4, 0, 2, (s, x) -> new AtMost(x, 2, 1)));
    cs.add(new Case("AtLeast", 4, 0, 2, (s, x) -> new AtLeast(x, 2, 1)));
    cs.add(
        new Case(
            "CountValues",
            6,
            0,
            3,
            (s, x) ->
                new CountValues(
                    Arrays.asList(head(x, 4)), new IntVar[] {x[4], x[5]}, new int[] {1, 2})));
    cs.add(new Case("Regular", 5, 0, 2, (s, x) -> new Regular(noTwoOnes(), x)));
    cs.add(
        new Case(
            "Cumulative",
            7,
            0,
            3,
            (s, x) ->
                new Cumulative(
                    new IntVar[] {x[0], x[1], x[2]},
                    new IntVar[] {x[3], x[4], x[5]},
                    new IntVar[] {one(s), one(s), one(s)},
                    x[6])));
    cs.add(
        new Case(
            "CumulativeUnary",
            6,
            0,
            3,
            (s, x) ->
                new CumulativeUnary(
                    new IntVar[] {x[0], x[1], x[2]},
                    new IntVar[] {x[3], x[4], x[5]},
                    new IntVar[] {one(s), one(s), one(s)},
                    one(s))));
    cs.add(
        new Case(
            "CumulativeOptional",
            9,
            0,
            2,
            (s, x) ->
                new CumulativeOptional(
                    new IntVar[] {x[0], x[1], x[2]},
                    new IntVar[] {x[3], x[4], x[5]},
                    new IntVar[] {one(s), one(s), one(s)},
                    one(s),
                    bools(s, x, 6, 3))));
    return cs.stream();
  }

  private static IntVar[] head(IntVar[] x, int n) {
    return Arrays.copyOf(x, n);
  }

  private static IntVar one(Store s) {
    return new IntVar(s, 1, 1);
  }

  // the variables from..from+n-1 restricted to 0..1
  private static IntVar[] bools(Store s, IntVar[] x, int from, int n) {
    IntVar[] b = Arrays.copyOfRange(x, from, from + n);
    for (IntVar v : b) {
      if (v.max() > 1) {
        v.domain.in(s.level, v, 0, 1);
      }
    }
    return b;
  }

  // words over 0..2 without two 1s in a row
  private static Fsm noTwoOnes() {
    Fsm fsm = new Fsm();
    FsmState a = new FsmState();
    FsmState b = new FsmState();
    fsm.allStates.add(a);
    fsm.allStates.add(b);
    fsm.initState = a;
    fsm.finalStates.add(a);
    fsm.finalStates.add(b);
    a.addTransition(new FsmTransition(new IntervalDomain(0, 0), a));
    a.addTransition(new FsmTransition(new IntervalDomain(2, 2), a));
    a.addTransition(new FsmTransition(new IntervalDomain(1, 1), b));
    b.addTransition(new FsmTransition(new IntervalDomain(0, 0), a));
    b.addTransition(new FsmTransition(new IntervalDomain(2, 2), a));
    return fsm;
  }

  @ParameterizedTest
  @MethodSource("cases")
  void violationIsZeroExactlyWhenPropagationAccepts(Case c) {
    Random random = new Random(c.name().hashCode());
    Store store = new Store();
    IntVar[] x = new IntVar[c.n()];
    for (int i = 0; i < c.n(); i++) {
      x[i] = new IntVar(store, "x" + i, c.min(), c.max());
    }
    Violation v = (Violation) c.make().apply(store, x);
    int accepted = 0;
    for (int t = 0; t < TRIALS; t++) {
      int[] values = new int[c.n()];
      Map<IntVar, Integer> at = new IdentityHashMap<>();
      for (int i = 0; i < c.n(); i++) {
        values[i] = x[i].dom().getElementAt(random.nextInt(x[i].getSize()));
        at.put(x[i], values[i]);
      }
      // constants and variables made by the constraint keep their smallest value
      long violation = v.violation(y -> at.getOrDefault(y, y.min()));
      boolean holds = propagates(c, values);
      String instance = c.name() + " " + Arrays.toString(values) + " violation " + violation;
      assertTrue(violation >= 0, instance);
      assertEquals(holds, violation == 0, instance);
      if (holds) {
        accepted++;
      }
    }
    assertTrue(accepted > 0 && accepted < TRIALS, c.name() + " accepted " + accepted);
  }

  // imposes the constraint over variables fixed to the values and propagates
  private static boolean propagates(Case c, int[] values) {
    Store store = new Store();
    IntVar[] x = new IntVar[c.n()];
    for (int i = 0; i < c.n(); i++) {
      x[i] = new IntVar(store, "x" + i, values[i], values[i]);
    }
    try {
      store.impose(c.make().apply(store, x));
      return store.consistency();
    } catch (org.jacop.core.FailException e) {
      return false;
    }
  }

  /** The violation of Regular is the Hamming distance to the nearest accepted word. */
  @org.junit.jupiter.api.Test
  void regularViolationIsHammingDistance() {
    Store store = new Store();
    int n = 5;
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 2);
    }
    Regular r = new Regular(noTwoOnes(), x);
    int words = 243;
    for (int w = 0; w < words; w++) {
      int[] word = digits(w, n);
      Map<IntVar, Integer> at = new IdentityHashMap<>();
      for (int i = 0; i < n; i++) {
        at.put(x[i], word[i]);
      }
      int best = Integer.MAX_VALUE;
      for (int u = 0; u < words; u++) {
        int[] other = digits(u, n);
        if (!twoOnes(other)) {
          int d = 0;
          for (int i = 0; i < n; i++) {
            d += other[i] == word[i] ? 0 : 1;
          }
          best = Math.min(best, d);
        }
      }
      assertEquals(best, r.violation(at::get), Arrays.toString(word));
    }
  }

  private static int[] digits(int w, int n) {
    int[] d = new int[n];
    for (int i = 0; i < n; i++) {
      d[i] = w % 3;
      w /= 3;
    }
    return d;
  }

  private static boolean twoOnes(int[] word) {
    for (int i = 1; i < word.length; i++) {
      if (word[i] == 1 && word[i - 1] == 1) {
        return true;
      }
    }
    return false;
  }

  /** The violation of a cumulative is the area above the limit. */
  @org.junit.jupiter.api.Test
  void cumulativeViolationIsOverload() {
    Store store = new Store();
    IntVar[] s = {new IntVar(store, 0, 10), new IntVar(store, 0, 10), new IntVar(store, 0, 10)};
    IntVar[] d = {new IntVar(store, 4, 4), new IntVar(store, 3, 3), new IntVar(store, 2, 2)};
    IntVar[] r = {new IntVar(store, 2, 2), new IntVar(store, 1, 1), new IntVar(store, 2, 2)};
    IntVar limit = new IntVar(store, 2, 2);
    Cumulative c = new Cumulative(s, d, r, limit);
    // tasks [0,4) of 2, [1,4) of 1, [3,5) of 2: usage 2, 3, 3, 5, 2 at times 0..4
    int[] starts = {0, 1, 3};
    Map<IntVar, Integer> at = new IdentityHashMap<>();
    for (int i = 0; i < 3; i++) {
      at.put(s[i], starts[i]);
      at.put(d[i], d[i].value());
      at.put(r[i], r[i].value());
    }
    at.put(limit, 2);
    assertEquals(1 + 1 + 3, c.violation(at::get));
  }
}
