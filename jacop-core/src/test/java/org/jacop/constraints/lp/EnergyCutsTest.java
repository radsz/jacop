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
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
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
  void mappedEnergyCutsKeepEverySchedule() {
    Random rnd = new Random(13);
    Store store = new Store();
    int mapped = 0;
    int violated = 0;
    for (int instance = 0; instance < INSTANCES; instance++) {
      int n = 3 + rnd.nextInt(3);
      long cap = 4 + rnd.nextInt(6);
      long[] est = new long[n];
      long[] lst = new long[n];
      long[] dur = new long[n];
      long[] use = new long[n];
      for (int j = 0; j < n; j++) {
        est[j] = rnd.nextInt(3);
        lst[j] = est[j] + rnd.nextInt(4);
        dur[j] = 1 + rnd.nextInt(3);
        use[j] = 1 + rnd.nextInt((int) cap);
      }
      Resource r = new Resource(est, lst, dur, use, cap);
      IntVar[] starts = new IntVar[n];
      long[] lo = new long[n];
      long[] hi = new long[n];
      for (int j = 0; j < n; j++) {
        starts[j] = new IntVar(store, (int) est[j], (int) lst[j]);
        lo[j] = est[j];
        hi[j] = lst[j];
      }
      List<long[]> all = schedules(r);
      for (EnergyCuts cuts : new EnergyCuts(starts, dur, use, cap).mapped(3)) {
        mapped++;
        IntVar[] s = cuts.starts();
        int[] column = new int[s.length];
        for (int k = 0; k < s.length; k++) {
          column[k] = Arrays.asList(starts).indexOf(s[k]);
        }
        for (int trial = 0; trial < 20; trial++) {
          double[] value = new double[n];
          for (int j = 0; j < n; j++) {
            value[j] = trial == 0 ? est[j] : est[j] + rnd.nextDouble() * (lst[j] - est[j]);
          }
          for (MirCut c : cuts.separate(column, value, lo, hi, 10)) {
            violated++;
            for (long[] sched : all) {
              long sum = 0;
              for (int k = 0; k < c.columns.length; k++) {
                sum += c.weights[k] * sched[c.columns[k]];
              }
              assertThat(sum)
                  .as("mapped cut %s of %s at %s", c, r, sched)
                  .isLessThanOrEqualTo(c.rhs);
            }
          }
        }
      }
    }
    assertThat(mapped).isPositive();
    assertThat(violated).isPositive();
  }

  @Test
  void windowCutsKeepEverySchedule() {
    boolean was = EnergyCuts.windows;
    EnergyCuts.windows = true;
    try {
      energyCutsKeepEverySchedule();
      mappedEnergyCutsKeepEverySchedule();
    } finally {
      EnergyCuts.windows = was;
    }
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
}
