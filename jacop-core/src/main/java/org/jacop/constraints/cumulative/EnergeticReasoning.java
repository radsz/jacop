/*
 * EnergeticReasoning.java
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

import java.util.Arrays;
import org.jacop.core.Store;

/**
 * Energetic reasoning for the cumulative constraint on one view (normal or reversed) of the tasks,
 * after Baptiste, Le Pape and Nuijten, "Satisfiability tests and time-bound adjustments for
 * cumulative scheduling problems", Annals of Operations Research 92, 1999.
 *
 * <p>A task i with earliest start est, latest start lst, minimal duration p and minimal resource
 * use c uses at least MI(i, t1, t2) = c * max(0, min(t2 - t1, p, ect - t1, t2 - lst)) units of
 * energy in a window [t1, t2), its smaller overlap when it starts at est or at lst. The check fails
 * if the minimal energies of all tasks exceed capacity * (t2 - t1). The adjustment: the other tasks
 * leave at most avail = capacity * (t2 - t1) - W(t1, t2) + MI(i, t1, t2) for i, so i overlaps the
 * window by at most q = avail / c time units. If i overlaps it by more when it starts at est, it
 * overlaps it by more at every start up to t2 - q, since the overlap only grows until the start
 * reaches t1, and so est can be raised to t2 - q.
 *
 * <p>The windows start at the est, lst and ect of the tasks. For a fixed t1 the minimal energy is a
 * piecewise linear function of t2: task i adds nothing until max(t1, lst), then c per time unit,
 * for min(p, ect - t1) time units. One sweep over its breakpoints, and over the ect of the tasks,
 * checks every window starting at t1. The breakpoints come from four task orders (by lst, lst + p,
 * lst + ect and ect) sorted once per call, so the sweep for one t1 is a linear merge and a call
 * costs O(n^2) for the check and O(n) per window whose slack is smaller than the largest task
 * energy for the adjustments.
 *
 * <p>All rules use the minimal duration and the minimal resource use of each task, so they are
 * sound for variable durations and resources. The arrays are reused between calls.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class EnergeticReasoning {

  // the task orders merged by the sweep; a task changes the slope of the minimal energy at
  private static final int AT_LST = 0; // lst, starting its ramp, if t1 <= lst and t1 < ect
  private static final int AT_LST_DUR = 1; // lst + p, ending it, if t1 <= est
  private static final int AT_LST_ECT =
      2; // lst + ect - t1, ending it, if est < t1 <= lst, t1 < ect
  private static final int AT_ECT = 3; // ect, ending it if lst < t1 < ect; else no change
  private static final int STREAMS = 4;
  // not a stream: the order by est, used with those by lst and ect to sweep the window starts
  private static final int BY_EST = 4;

  private int[] est = new int[0];
  private int[] lst = new int[0];
  private int[] ect = new int[0];
  private int[] dur = new int[0];
  private int[] res = new int[0];
  private int[] update = new int[0];
  private int[] windowStarts = new int[0];
  // sort keys and task orders of the streams, kept between calls and re-sorted by insertion
  private final long[][] keys = new long[STREAMS + 1][0];
  private final int[][] orders = new int[STREAMS + 1][0];
  private final int[] next = new int[STREAMS];
  private int ordered = -1;
  static final boolean EST_ONLY = Boolean.getBoolean("fz_cumulative_er_est");
  // the breakpoints from here on start windows too loose to fail or to adjust a task
  private long horizon;

  private void ensureCapacity(int n) {
    if (est.length >= n) {
      return;
    }
    est = new int[n];
    lst = new int[n];
    ect = new int[n];
    dur = new int[n];
    res = new int[n];
    update = new int[n];
    windowStarts = new int[3 * n];
    for (int k = 0; k <= STREAMS; k++) {
      keys[k] = new long[n];
      orders[k] = new int[n];
    }
    ordered = -1;
  }

  /**
   * Checks the energy of every window and raises the earliest start times it implies.
   *
   * @param ts the tasks of the view; all must have positive minimal duration and resource use.
   * @param n the number of tasks used from ts.
   * @param capacity the maximal capacity.
   * @param store the store.
   */
  void filter(TaskView[] ts, int n, long capacity, Store store) {
    ensureCapacity(n);
    load(ts, n);
    long maxEnergy = 0;
    int m = 0;
    for (int i = 0; i < n; i++) {
      maxEnergy = Math.max(maxEnergy, (long) dur[i] * res[i]);
      windowStarts[m++] = est[i];
      if (!EST_ONLY) {
        windowStarts[m++] = lst[i];
        windowStarts[m++] = ect[i];
      }
    }
    Arrays.sort(windowStarts, 0, m);
    // for the window start t1, swept upwards: the minimal energy of the tasks in [t1, infinity),
    // which is the sum over the tasks with ect > t1 of c * p, less c * (t1 - est) for those with
    // est < t1 < ect, and the slope of the minimal energy at t1, the sum of c over the tasks with
    // lst < t1 < ect
    long total = 0;
    int[] byEst = orders[BY_EST];
    int[] byLst = orders[AT_LST];
    int[] byEct = orders[AT_ECT];
    int pe = 0;
    int pl = 0;
    int pc = 0;
    long started = 0;
    long startedEst = 0;
    long slope = 0;
    for (int i = 0; i < n; i++) {
      total += (long) dur[i] * res[i];
    }
    for (int k = 0; k < m; k++) {
      int t1 = windowStarts[k];
      if (k > 0 && t1 == windowStarts[k - 1]) {
        continue;
      }
      for (; pe < n && est[byEst[pe]] < t1; pe++) {
        started += res[byEst[pe]];
        startedEst += (long) res[byEst[pe]] * est[byEst[pe]];
      }
      for (; pl < n && lst[byLst[pl]] < t1; pl++) {
        int i = byLst[pl];
        if (lst[i] < ect[i]) {
          slope += res[i];
        }
      }
      for (; pc < n && ect[byEct[pc]] <= t1; pc++) {
        int i = byEct[pc];
        total -= (long) dur[i] * res[i];
        started -= res[i];
        startedEst -= (long) res[i] * est[i];
        if (lst[i] < ect[i]) {
          slope -= res[i];
        }
      }
      long remaining = total - (started * t1 - startedEst);
      windowsFrom(t1, n, capacity, maxEnergy, remaining, slope);
    }
    for (int i = 0; i < n; i++) {
      if (update[i] > est[i]) {
        ts[i].updateEdgeFind(store.level, update[i]);
      }
    }
  }

  private void load(TaskView[] ts, int n) {
    for (int i = 0; i < n; i++) {
      TaskView t = ts[i];
      est[i] = t.est();
      lst[i] = t.lst();
      ect[i] = t.ect();
      dur[i] = t.dur.min();
      res[i] = t.res.min();
      update[i] = est[i];
      keys[AT_LST][i] = lst[i];
      keys[AT_LST_DUR][i] = (long) lst[i] + dur[i];
      keys[AT_LST_ECT][i] = (long) lst[i] + ect[i];
      keys[AT_ECT][i] = ect[i];
      keys[BY_EST][i] = est[i];
    }
    if (ordered != n) {
      for (int k = 0; k <= STREAMS; k++) {
        for (int i = 0; i < n; i++) {
          orders[k][i] = i;
        }
      }
      ordered = n;
    }
    for (int k = 0; k <= STREAMS; k++) {
      sortBy(keys[k], orders[k], n);
    }
  }

  // insertion sort of order by key, starting from the order of the previous call
  private static void sortBy(long[] key, int[] order, int n) {
    for (int k = 1; k < n; k++) {
      int i = order[k];
      long v = key[i];
      int m = k - 1;
      while (m >= 0 && key[order[m]] > v) {
        order[m + 1] = order[m];
        m--;
      }
      order[m + 1] = i;
    }
  }

  private boolean inStream(int stream, int i, int t1) {
    return switch (stream) {
      case AT_LST -> t1 <= lst[i] && t1 < ect[i];
      case AT_LST_DUR -> t1 <= est[i];
      case AT_LST_ECT -> est[i] < t1 && t1 <= lst[i] && t1 < ect[i];
      default -> t1 < ect[i];
    };
  }

  private long slopeChange(int stream, int i, int t1) {
    return switch (stream) {
      case AT_LST -> res[i];
      case AT_LST_DUR, AT_LST_ECT -> -res[i];
      default -> lst[i] < t1 ? -res[i] : 0;
    };
  }

  // the first position from p of a task in the stream for windows starting at t1 whose breakpoint
  // is before the horizon, or n
  private int skip(int stream, int p, int n, int t1) {
    int[] order = orders[stream];
    while (p < n && !inStream(stream, order[p], t1)) {
      if (time(stream, p, t1) >= horizon) {
        return n;
      }
      p++;
    }
    return p < n && time(stream, p, t1) < horizon ? p : n;
  }

  private long time(int stream, int p, int t1) {
    long key = keys[stream][orders[stream][p]];
    return stream == AT_LST_ECT ? key - t1 : key;
  }

  // the first position in the stream whose key is larger than bound
  private int firstAbove(int stream, long bound, int n) {
    long[] key = keys[stream];
    int[] order = orders[stream];
    int lo = 0;
    int hi = n;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (key[order[mid]] > bound) {
        hi = mid;
      } else {
        lo = mid + 1;
      }
    }
    return lo;
  }

  // checks the windows [t1, t2) for every breakpoint t2 of the minimal energy; remaining is the
  // minimal energy of the tasks in [t1, infinity) and slope its slope at t1
  private void windowsFrom(
      int t1, int n, long capacity, long maxEnergy, long remaining, long slope) {
    // every window [t1, t2) with capacity * (t2 - t1) >= remaining + maxEnergy has a slack of at
    // least maxEnergy
    horizon = t1 + (remaining + maxEnergy + capacity - 1) / capacity;
    // a task enters a stream only at a key past these bounds: lst >= t1 for AT_LST, lst + p > est
    // >= t1 for AT_LST_DUR, lst + ect > 2 * t1 for AT_LST_ECT and ect > t1 for AT_ECT
    next[AT_LST] = skip(AT_LST, firstAbove(AT_LST, t1 - 1L, n), n, t1);
    next[AT_LST_DUR] = skip(AT_LST_DUR, firstAbove(AT_LST_DUR, t1, n), n, t1);
    next[AT_LST_ECT] = skip(AT_LST_ECT, firstAbove(AT_LST_ECT, 2L * t1, n), n, t1);
    next[AT_ECT] = skip(AT_ECT, firstAbove(AT_ECT, t1, n), n, t1);
    long energy = 0;
    long previous = t1;
    while (true) {
      long t2 = Long.MAX_VALUE;
      for (int k = 0; k < STREAMS; k++) {
        if (next[k] < n) {
          t2 = Math.min(t2, time(k, next[k], t1));
        }
      }
      if (t2 == Long.MAX_VALUE) {
        return;
      }
      long added = slope * (t2 - previous);
      energy += added;
      remaining -= added;
      previous = t2;
      if (t2 > t1) {
        long slack = capacity * (t2 - t1) - energy;
        if (slack < 0) {
          throw Store.failException;
        }
        if (slack < maxEnergy) {
          adjust(t1, (int) t2, slack, n);
        } else if (slack - remaining >= maxEnergy) {
          // the slack of every later window is at least slack - remaining, too large to fail or
          // to adjust a task
          return;
        }
      }
      for (int k = 0; k < STREAMS; k++) {
        while (next[k] < n && time(k, next[k], t1) == t2) {
          slope += slopeChange(k, orders[k][next[k]], t1);
          next[k] = skip(k, next[k] + 1, n, t1);
        }
      }
    }
  }

  // raises the est of the tasks that would overlap [t1, t2) by more than the slack allows
  private void adjust(int t1, int t2, long slack, int n) {
    long length = (long) t2 - t1;
    for (int i = 0; i < n; i++) {
      if (est[i] >= t2 || ect[i] <= t1 || (long) res[i] * Math.min(dur[i], length) <= slack) {
        continue;
      }
      long leftShift = (long) res[i] * (Math.min(ect[i], t2) - Math.max(est[i], t1));
      long minimal =
          (long) res[i]
              * Math.max(0, Math.min(t2 - Math.max(t1, lst[i]), Math.min(dur[i], ect[i] - t1)));
      long available = slack + minimal;
      if (leftShift > available) {
        long newEst = t2 - available / res[i];
        if (newEst > update[i]) {
          update[i] = (int) newEst;
        }
      }
    }
  }
}
