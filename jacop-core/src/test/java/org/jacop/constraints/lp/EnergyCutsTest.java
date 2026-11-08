/*
 * CapacityCutsTest.java
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
package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks the energy cuts of {@link EnergyCuts} against every schedule of small random resources,
 * found by enumeration: no cut may cut off a schedule, whatever the LP values the cuts were
 * separated from, also when the tasks run longer than their least durations.
 */
class EnergyCutsTest {

  private static final int INSTANCES = Integer.getInteger("energy.instances", 300);

  private record Resource(long[] est, long[] lst, long[] dur, long[] use, long cap) {

    // whether the tasks at the starts, each run for dur + extra, fit the capacity
    boolean fits(long[] start, long[] extra) {
      long end = 0;
      for (int j = 0; j < start.length; j++) {
        end = Math.max(end, start[j] + dur[j] + extra[j]);
      }
      for (long t = 0; t < end; t++) {
        long used = 0;
        for (int j = 0; j < start.length; j++) {
          if (start[j] <= t && t < start[j] + dur[j] + extra[j]) {
            used += use[j];
          }
        }
        if (used > cap) {
          return false;
        }
      }
      return true;
    }
  }

  private static Resource random(Random rnd) {
    int n = 2 + rnd.nextInt(4);
    long cap = 1 + rnd.nextInt(3);
    long[] est = new long[n];
    long[] lst = new long[n];
    long[] dur = new long[n];
    long[] use = new long[n];
    for (int j = 0; j < n; j++) {
      est[j] = rnd.nextInt(4);
      lst[j] = est[j] + rnd.nextInt(5);
      dur[j] = 1 + rnd.nextInt(3);
      use[j] = 1 + rnd.nextInt((int) cap);
    }
    return new Resource(est, lst, dur, use, cap);
  }

  // every feasible schedule, with each task run for its least duration or one longer
  private static List<long[]> schedules(Resource r) {
    int n = r.est.length;
    List<long[]> out = new ArrayList<>();
    long[] start = r.est.clone();
    while (true) {
      for (int mask = 0; mask < 1 << n; mask++) {
        long[] extra = new long[n];
        for (int j = 0; j < n; j++) {
          extra[j] = (mask >> j) & 1;
        }
        if (r.fits(start, extra)) {
          out.add(start.clone());
          break;
        }
      }
      int j = 0;
      while (j < n && start[j] == r.lst[j]) {
        start[j] = r.est[j];
        j++;
      }
      if (j == n) {
        return out;
      }
      start[j]++;
    }
  }

  @Test
  void energyCutsKeepEverySchedule() {
    Random rnd = new Random(7);
    Store store = new Store();
    int violated = 0;
    for (int instance = 0; instance < INSTANCES; instance++) {
      Resource r = random(rnd);
      int n = r.est.length;
      IntVar[] starts = new IntVar[n];
      int[] column = new int[n];
      long[] lo = new long[n];
      long[] hi = new long[n];
      for (int j = 0; j < n; j++) {
        starts[j] = new IntVar(store, (int) r.est[j], (int) r.lst[j]);
        column[j] = j;
        lo[j] = r.est[j];
        hi[j] = r.lst[j];
      }
      List<long[]> all = schedules(r);
      EnergyCuts cuts = new EnergyCuts(starts, r.dur, r.use, r.cap);
      for (int trial = 0; trial < 20; trial++) {
        double[] value = new double[n];
        for (int j = 0; j < n; j++) {
          value[j] =
              trial == 0
                  ? r.est[j]
                  : trial == 1 ? r.lst[j] : r.est[j] + rnd.nextDouble() * (r.lst[j] - r.est[j]);
        }
        for (MirCut c : cuts.separate(column, value, lo, hi, 10)) {
          double activity = 0;
          for (int k = 0; k < c.columns.length; k++) {
            activity += c.weights[k] * value[c.columns[k]];
          }
          assertThat(activity).as("violated at the values separated from").isGreaterThan(c.rhs);
          violated++;
          for (long[] s : all) {
            long sum = 0;
            for (int k = 0; k < c.columns.length; k++) {
              sum += c.weights[k] * s[c.columns[k]];
            }
            assertThat(sum).as("cut %s of %s at %s", c, r, s).isLessThanOrEqualTo(c.rhs);
          }
        }
      }
    }
    assertThat(violated).isGreaterThan(INSTANCES / 4);
  }

  @Test
  void oneMachineCutIsQueyranneInequality() {
    // three unit-usage tasks of durations 2, 3 and 4 on one machine, all released at 0: sum p S >=
    // 2*3 + 2*4 + 3*4 = 26; at S = 0 the cut over all three is violated
    Store store = new Store();
    IntVar[] starts = new IntVar[3];
    for (int j = 0; j < 3; j++) {
      starts[j] = new IntVar(store, 0, 20);
    }
    EnergyCuts cuts = new EnergyCuts(starts, new long[] {2, 3, 4}, new long[] {1, 1, 1}, 1);
    List<MirCut> found =
        cuts.separate(
            new int[] {0, 1, 2},
            new double[] {0, 0, 0},
            new long[] {0, 0, 0},
            new long[] {20, 20, 20},
            10);
    assertThat(found).isNotEmpty();
    MirCut best = found.get(0);
    assertThat(best.columns).containsExactly(0, 1, 2);
    assertThat(best.weights).containsExactly(-2, -3, -4);
    assertThat(best.rhs).isEqualTo(-26);
  }

  /**
   * Random resources with a weighted sum of starts to minimize keep their optimum when the energy
   * cuts do not fit the dense tableau (a cap of one entry) and the rows move to the sparse simplex
   * for them; the bound of the cuts is not above the optimum, and on some instances the rows stay
   * on the sparse simplex with the cuts.
   */
  @Test
  void energyCutsOnJalpAboveTheTableauCapKeepTheOptimum() {
    Random rnd = new Random(11);
    int kept = 0;
    for (int instance = 0; instance < INSTANCES / 3; instance++) {
      long seed = rnd.nextLong();
      long expected = optimum(new Random(seed), null);
      LinearRelaxation[] r = new LinearRelaxation[1];
      long actual = optimum(new Random(seed), r);
      assertThat(actual).as("instance %d", instance).isEqualTo(expected);
      if (r[0] == null || expected == Long.MIN_VALUE) {
        continue;
      }
      if (!Double.isNaN(r[0].capacityBound)) {
        assertThat(r[0].capacityBound)
            .as("instance %d", instance)
            .isLessThanOrEqualTo(expected + 1e-6);
      }
      if (r[0].sparseCuts && r[0].energyCuts > 0) {
        kept++;
      }
    }
    assertThat(kept).isPositive();
  }

  // the least weighted sum of starts of a random resource with a precedence, by search, with the
  // relaxation at a tableau cap of one entry when relaxation is given
  private static long optimum(Random rnd, LinearRelaxation[] relaxation) {
    Store store = new Store();
    int n = 4 + rnd.nextInt(3);
    int cap = 1 + rnd.nextInt(3);
    IntVar[] starts = new IntVar[n];
    IntVar[] dur = new IntVar[n];
    IntVar[] use = new IntVar[n];
    int[] w = new int[n + 1];
    IntVar[] vars = new IntVar[n + 1];
    int range = 0;
    for (int j = 0; j < n; j++) {
      starts[j] = new IntVar(store, "s" + j, rnd.nextInt(3), 12);
      int d = 1 + rnd.nextInt(3);
      dur[j] = new IntVar(store, d, d);
      int u = 1 + rnd.nextInt(cap);
      use[j] = new IntVar(store, u, u);
      w[j] = 1 + rnd.nextInt(4);
      vars[j] = starts[j];
      range += w[j] * 12;
    }
    IntVar cost = new IntVar(store, "cost", 0, range);
    vars[n] = cost;
    w[n] = -1;
    store.impose(new LinearInt(vars, w, "==", 0));
    store.impose(
        new LinearInt(new IntVar[] {starts[0], starts[1]}, new int[] {1, -1}, "<=", -dur[0].min()));
    store.impose(new Cumulative(starts, dur, use, new IntVar(store, cap, cap)));
    if (relaxation != null) {
      LinearRelaxation r = LinearRelaxation.of(store, cost, false);
      if (r != null) {
        r.setTableauCap(1);
        store.impose(r);
      }
      relaxation[0] = r;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    boolean found =
        search.labeling(store, new InputOrderSelect<>(store, starts, new IndomainMin<>()), cost);
    return found ? search.getCostValue() : Long.MIN_VALUE;
  }
}
