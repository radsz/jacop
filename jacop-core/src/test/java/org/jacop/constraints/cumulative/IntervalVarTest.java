/*
 * IntervalVarTest.java
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

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.Random;
import java.util.function.Predicate;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * The constraints of {@link IntervalVar} against their meaning: on random small models, the number
 * of solutions over all variables equals the number of assignments of the variables' domains that
 * satisfy the relation written out by hand.
 */
class IntervalVarTest {

  private static final int TRIALS = Integer.getInteger("intervals.trials", 60);

  // four intervals, the first a master; 0: presence, 1: start, 2: duration, 3: end of each
  private static IntervalVar[] intervals(Store store, Random rnd) {
    IntervalVar[] x = new IntervalVar[4];
    for (int i = 0; i < 4; i++) {
      int d = 1 + rnd.nextInt(2);
      x[i] =
          new IntervalVar(
              store, "i" + i, 0, 5, i == 0 ? 0 : d, i == 0 ? 3 : d + rnd.nextInt(2), true);
    }
    if (rnd.nextBoolean()) {
      x[3].presence.domain.in(store.level, x[3].presence, 1, 1);
    }
    return x;
  }

  private static IntVar[] vars(IntervalVar[] x) {
    IntVar[] v = new IntVar[16];
    for (int i = 0; i < 4; i++) {
      v[4 * i] = x[i].presence;
      v[4 * i + 1] = x[i].start;
      v[4 * i + 2] = x[i].duration;
      v[4 * i + 3] = x[i].end;
    }
    return v;
  }

  private static boolean intervalsHold(int[] t) {
    for (int i = 0; i < 4; i++) {
      if (t[4 * i + 1] + t[4 * i + 2] != t[4 * i + 3]) {
        return false;
      }
    }
    return true;
  }

  private static boolean present(int[] t, int i) {
    return t[4 * i] == 1;
  }

  private static boolean overlap(int[] t, int i, int j) {
    return t[4 * i + 1] < t[4 * j + 3] && t[4 * j + 1] < t[4 * i + 3];
  }

  private static boolean noOverlapHolds(int[] t) {
    for (int i = 1; i < 4; i++) {
      for (int j = i + 1; j < 4; j++) {
        if (present(t, i) && present(t, j) && overlap(t, i, j)) {
          return false;
        }
      }
    }
    return true;
  }

  private static boolean alternativeHolds(int[] t) {
    int chosen = -1;
    for (int i = 1; i < 4; i++) {
      if (present(t, i)) {
        if (chosen >= 0) {
          return false;
        }
        chosen = i;
      }
    }
    if (chosen < 0) {
      return !present(t, 0) && t[2] == 0;
    }
    return present(t, 0) && t[1] == t[4 * chosen + 1] && t[2] == t[4 * chosen + 2];
  }

  private static boolean spanHolds(int[] t) {
    int start = Integer.MAX_VALUE;
    int end = Integer.MIN_VALUE;
    for (int i = 1; i < 4; i++) {
      if (present(t, i)) {
        start = Math.min(start, t[4 * i + 1]);
        end = Math.max(end, t[4 * i + 3]);
      }
    }
    if (start == Integer.MAX_VALUE) {
      return !present(t, 0) && t[2] == 0;
    }
    return present(t, 0) && t[1] == start && t[3] == end;
  }

  private static long count(Store store, IntVar[] v) {
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    boolean found = search.labeling(store, new SimpleSelect<>(v, null, new IndomainMin<>()));
    return found ? search.getSolutionListener().solutionsNo() : 0;
  }

  // assignments of the intervals' presences, starts and durations, with the end their sum when the
  // end's domain has it
  private static long enumerate(IntVar[] v, int[] t, int k, Predicate<int[]> relation) {
    if (k == v.length) {
      return relation.test(t) ? 1 : 0;
    }
    if (k % 4 == 3) {
      t[k] = t[k - 2] + t[k - 1];
      return v[k].domain.contains(t[k]) ? enumerate(v, t, k + 1, relation) : 0;
    }
    long n = 0;
    for (var e = v[k].dom().valueEnumeration(); e.hasMoreElements(); ) {
      t[k] = e.nextElement();
      n += enumerate(v, t, k + 1, relation);
    }
    return n;
  }

  private interface Model {
    void post(Store store, IntervalVar[] x, Random rnd);
  }

  private static void check(String name, Model model, Predicate<int[]> relation) {
    Random rnd = new Random(name.hashCode());
    long solutions = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = rnd.nextLong();
      // the domains before the constraints, for the enumeration
      Store plain = new Store();
      IntVar[] before = vars(intervals(plain, new Random(seed)));
      long expected = enumerate(before, new int[16], 0, t -> intervalsHold(t) && relation.test(t));
      Store store = new Store();
      IntervalVar[] x = intervals(store, new Random(seed));
      model.post(store, x, new Random(seed));
      long found = store.consistency() ? count(store, vars(x)) : 0;
      assertThat(found).as("%s trial %d", name, trial).isEqualTo(expected);
      solutions += found;
    }
    assertThat(solutions).as(name).isPositive();
  }

  private static IntervalVar[] options(IntervalVar[] x) {
    return new IntervalVar[] {x[1], x[2], x[3]};
  }

  @Test
  void noOverlapKeepsThePresentIntervalsApart() {
    check(
        "noOverlap",
        (store, x, rnd) -> store.impose(IntervalVar.noOverlap(store, options(x))),
        IntervalVarTest::noOverlapHolds);
  }

  @Test
  void cumulativeCountsTheDemandsOfThePresentIntervals() {
    int[] demands = {1, 2, 1};
    check(
        "cumulative",
        (store, x, rnd) ->
            IntervalVar.cumulative(store, options(x), demands, new IntVar(store, 2, 2))
                .forEach(store::impose),
        t -> {
          for (int time = 0; time < 6; time++) {
            int load = 0;
            for (int i = 1; i < 4; i++) {
              if (present(t, i) && t[4 * i + 1] <= time && time < t[4 * i + 3]) {
                load += demands[i - 1];
              }
            }
            if (load > 2) {
              return false;
            }
          }
          return true;
        });
  }

  @Test
  void alternativePicksOneOption() {
    check(
        "alternative",
        (store, x, rnd) -> store.impose(IntervalVar.alternative(x[0], options(x))),
        IntervalVarTest::alternativeHolds);
  }

  @Test
  void spanCoversThePresentIntervals() {
    check(
        "span",
        (store, x, rnd) -> store.impose(IntervalVar.span(x[0], options(x))),
        IntervalVarTest::spanHolds);
  }

  @Test
  void endBeforeStartHoldsWhenBothArePresent() {
    check(
        "endBeforeStart",
        (store, x, rnd) -> {
          store.impose(IntervalVar.endBeforeStart(x[1], x[2], 1));
          store.impose(IntervalVar.endBeforeStart(x[2], x[3], 0));
        },
        t ->
            (!present(t, 1) || !present(t, 2) || t[7] + 1 <= t[9])
                && (!present(t, 2) || !present(t, 3) || t[11] <= t[13]));
  }

  @Test
  void rejectsBoundsThatFitNoInterval() {
    Store store = new Store();
    assertThatThrownBy(() -> new IntervalVar(store, "x", 0, 2, 3, 4, true))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new IntervalVar(store, "y", 0, 9, 2, 1, false))
        .isInstanceOf(IllegalArgumentException.class);
  }
}
