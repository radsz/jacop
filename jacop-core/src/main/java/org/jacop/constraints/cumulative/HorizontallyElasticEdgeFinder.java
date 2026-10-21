/*
 * HorizontallyElasticEdgeFinder.java
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
 * Horizontally elastic edge finding on one view (normal or reversed) of the tasks, after Gingras
 * and Quimper, "Generalizing the Edge-Finder Rule for the Cumulative Constraint", IJCAI 2016, and
 * Fetgo and Djamegni, "Horizontally Elastic Edge-Finder Algorithm for Cumulative Resource
 * Constraint Revisited", Constraints 2022.
 *
 * <p>The relaxation bounds the energy W(t) a set of tasks can process by time t. Task k must
 * process at least e_k = dur.min * res.min units, at a rate of at most res.max, inside [est_k,
 * lct_k). So W(t) is at most U(t) = sum_k min(e_k, res.max_k * (t - est_k)), and W(t+1) - W(t) is
 * at most the capacity and at most the sum of res.max over the tasks whose window contains t. The
 * greedy W(t+1) = min(W(t) + min(capacity, hmax(t)), U(t+1)) is the largest function meeting these
 * limits, so it bounds the energy any schedule processes. Unlike the fully elastic relaxation of
 * classic edge finding, a task cannot use the capacity before its est at a higher rate than its
 * height allows.
 *
 * <p>Detection: let Omega be the tasks other than i with lct at most d. If the relaxation of Omega
 * and i cannot process all their energy by d, then i ends after every task of Omega in every
 * solution. Adjustment: i then uses res.min_i units from its start s to the end of Omega, so Omega
 * has at most capacity - res.min_i from s on and must still be processed by d. The relaxation with
 * the capacity reduced from s gives the smallest such s, found by binary search since the processed
 * energy grows with s.
 *
 * <p>Each detection costs O(n) on presorted events, so a call costs O(n^3) in the worst case plus
 * O(n log H) per adjusted pair, where H is the time horizon.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class HorizontallyElasticEdgeFinder {

  // event kinds; events at the same time are all applied before time advances
  private static final int START = 0;
  private static final int RAMP_END = 1;
  private static final int RAMP_REST = 2;
  private static final int WINDOW_END = 3;

  private int[] est = new int[0];
  private int[] lct = new int[0];
  private int[] resMin = new int[0];
  private int[] resMax = new int[0];
  private int[] dur = new int[0];
  private long[] energy = new long[0];
  // energy modulo resMax: processed in the time unit after the ramp of a task at full rate
  private int[] rest = new int[0];
  private int[] update = new int[0];
  // tasks sorted by lct and their rank in that order
  private long[] lctKeys = new long[0];
  private int[] lctOrder = new int[0];
  private int[] lctRank = new int[0];
  // events: time, kind, task, sorted by time
  private long[] eventKeys = new long[0];
  private int eventCount;
  // events of Omega before the current deadline, and of the task tested with Omega
  private long[] omegaEvents = new long[0];
  private int omegaCount;
  private final long[] extraEvents = new long[3];
  // the relaxed schedule of Omega alone: rate segRate on [segStart, next segStart), up to d
  private int[] segStart = new int[0];
  private long[] segRate = new long[0];
  private int segCount;

  private void ensureCapacity(int n) {
    if (est.length >= n) {
      return;
    }
    est = new int[n];
    lct = new int[n];
    resMin = new int[n];
    resMax = new int[n];
    dur = new int[n];
    energy = new long[n];
    rest = new int[n];
    update = new int[n];
    lctKeys = new long[n];
    lctOrder = new int[n];
    lctRank = new int[n];
    eventKeys = new long[4 * n];
    omegaEvents = new long[4 * n];
    segStart = new int[12 * n + 2];
    segRate = new long[12 * n + 2];
  }

  private void addEvent(int time, int kind, int task) {
    eventKeys[eventCount++] = ((long) time << 32) | ((long) kind << 28) | task;
  }

  private static int eventTime(long key) {
    return (int) (key >> 32);
  }

  private static int eventKind(long key) {
    return (int) (key >>> 28) & 0xF;
  }

  private static int eventTask(long key) {
    return (int) key & 0x0FFFFFFF;
  }

  /**
   * Runs the rule on the tasks of one view.
   *
   * @param ts the tasks of the view, with positive minimal duration and resource use.
   * @param n the number of tasks.
   * @param capacity the maximal capacity.
   * @param store the store.
   */
  void filter(TaskView[] ts, int n, long capacity, Store store) {
    ensureCapacity(n);
    eventCount = 0;
    for (int i = 0; i < n; i++) {
      TaskView t = ts[i];
      est[i] = t.est();
      lct[i] = t.lct();
      resMin[i] = t.res.min();
      resMax[i] = t.res.max();
      dur[i] = t.dur.min();
      energy[i] = (long) dur[i] * resMin[i];
      update[i] = est[i];
      lctKeys[i] = ((long) lct[i] << 32) | i;

      // U_i grows at rate resMax from est until energy is reached, and the remainder of the
      // division is processed in the following time unit
      long ramp = energy[i] / resMax[i];
      rest[i] = (int) (energy[i] % resMax[i]);
      addEvent(est[i], START, i);
      addEvent((int) Math.min(Integer.MAX_VALUE - 1, est[i] + ramp), RAMP_END, i);
      if (rest[i] > 0) {
        addEvent((int) Math.min(Integer.MAX_VALUE, est[i] + ramp + 1), RAMP_REST, i);
      }
      addEvent(lct[i], WINDOW_END, i);
    }
    Arrays.sort(eventKeys, 0, eventCount);
    Arrays.sort(lctKeys, 0, n);
    for (int p = 0; p < n; p++) {
      lctOrder[p] = (int) lctKeys[p];
      lctRank[lctOrder[p]] = p;
    }

    long omegaEnergy = 0;
    for (int p = 0; p < n; p++) {
      int d = lct[lctOrder[p]];
      omegaEnergy += energy[lctOrder[p]];
      if (p + 1 < n && lct[lctOrder[p + 1]] == d) {
        continue;
      }
      // Omega = tasks of lct rank at most p; its events before d, in time order
      omegaCount = 0;
      for (int e = 0; e < eventCount; e++) {
        long key = eventKeys[e];
        if (eventTime(key) >= d) {
          break;
        }
        if (lctRank[eventTask(key)] <= p) {
          omegaEvents[omegaCount++] = key;
        }
      }
      if (recordOmega(d, capacity) < omegaEnergy) {
        // Omega alone cannot be processed by d
        throw Store.failException;
      }
      for (int q = p + 1; q < n; q++) {
        int i = lctOrder[q];
        if (est[i] >= d) {
          // i cannot start before d anyway
          continue;
        }
        long reduced = Math.max(0, capacity - resMin[i]);
        int low = update[i];
        if (low >= d || maxRateFrom(low) <= reduced) {
          // the schedule of Omega alone stays within the reduced capacity from low on
          continue;
        }
        // i ends after Omega if it cannot end by d, or if the relaxation of both cannot
        if (est[i] + dur[i] <= d) {
          if (fitsInFreeCapacity(i, d, capacity)) {
            // Omega as scheduled alone and i in the capacity it leaves form a relaxed schedule
            continue;
          }
          if (processed(i, d, capacity, Integer.MAX_VALUE, 0, omegaEnergy + energy[i])
              >= omegaEnergy + energy[i]) {
            continue;
          }
        }
        // Omega precedes i; i starts at the earliest s at which Omega still fits by d
        if (processed(-1, d, capacity, low, reduced, omegaEnergy) >= omegaEnergy) {
          continue;
        }
        int high = d;
        // processed is below omegaEnergy at low and reaches it at high
        while (high - low > 1) {
          int mid = (int) (((long) low + high) >>> 1);
          if (processed(-1, d, capacity, mid, reduced, omegaEnergy) >= omegaEnergy) {
            high = mid;
          } else {
            low = mid;
          }
        }
        update[i] = high;
      }
    }

    for (int i = 0; i < n; i++) {
      if (update[i] > est[i]) {
        ts[i].updateEdgeFind(store.level, update[i]);
      }
    }
  }

  private void addSegment(long start, long rate) {
    if (segCount > 0 && segRate[segCount - 1] == rate) {
      return;
    }
    segStart[segCount] = (int) start;
    segRate[segCount++] = rate;
  }

  /**
   * Computes the relaxed schedule of Omega alone up to d, as segments of constant rate.
   *
   * @return the energy processed by d.
   */
  private long recordOmega(int d, long capacity) {
    segCount = 0;
    long processed = 0;
    long bound = 0;
    long slope = 0;
    long hmax = 0;
    long time = Long.MIN_VALUE;
    int e = 0;
    while (true) {
      long next = e < omegaCount ? eventTime(omegaEvents[e]) : d;
      if (time != Long.MIN_VALUE && next > time) {
        long rate = Math.min(capacity, hmax);
        long length = next - time;
        long gap = bound - processed;
        long nextBound = bound + slope * length;
        if (slope >= rate || gap / (rate - slope) >= length) {
          addSegment(time, rate);
          processed += rate * length;
        } else {
          // rate until the gap closes, one step that closes it, then the slope of U
          long m = gap / (rate - slope);
          if (m > 0) {
            addSegment(time, rate);
          }
          addSegment(time + m, gap - m * (rate - slope) + slope);
          if (time + m + 1 < next) {
            addSegment(time + m + 1, slope);
          }
          processed = nextBound;
        }
        bound = nextBound;
      }
      time = next;
      if (time >= d) {
        segStart[segCount] = d;
        return processed;
      }
      while (e < omegaCount && eventTime(omegaEvents[e]) == time) {
        long key = omegaEvents[e++];
        int k = eventTask(key);
        switch (eventKind(key)) {
          case START:
            slope += resMax[k];
            hmax += resMax[k];
            break;
          case RAMP_END:
            slope -= resMax[k] - rest[k];
            break;
          case RAMP_REST:
            slope -= rest[k];
            break;
          default:
            hmax -= resMax[k];
            break;
        }
      }
    }
  }

  // the largest rate of the schedule of Omega alone from time t to d
  private long maxRateFrom(int t) {
    long max = 0;
    for (int g = segCount - 1; g >= 0 && segStart[g + 1] > t; g--) {
      max = Math.max(max, segRate[g]);
    }
    return max;
  }

  // whether task i, from its est at rate at most resMax, fits by d in the capacity Omega leaves
  private boolean fitsInFreeCapacity(int i, int d, long capacity) {
    long needed = energy[i];
    for (int g = segCount - 1; g >= 0 && segStart[g + 1] > est[i]; g--) {
      long length = segStart[g + 1] - Math.max(segStart[g], est[i]);
      needed -= Math.min(resMax[i], capacity - segRate[g]) * length;
      if (needed <= 0) {
        return true;
      }
    }
    return false;
  }

  /**
   * The relaxed energy processed by time d by the tasks of Omega and task extra (if not -1), with
   * the capacity reduced from time cut on. It stops once the energy reaches target.
   */
  private long processed(
      int extra, int d, long capacity, int cut, long reducedCapacity, long target) {
    int extraCount = 0;
    if (extra >= 0) {
      long ramp = energy[extra] / resMax[extra];
      extraEvents[extraCount++] = ((long) est[extra] << 32) | ((long) START << 28) | extra;
      extraEvents[extraCount++] =
          (Math.min(Integer.MAX_VALUE - 1, est[extra] + ramp) << 32)
              | ((long) RAMP_END << 28)
              | extra;
      if (rest[extra] > 0) {
        extraEvents[extraCount++] =
            (Math.min(Integer.MAX_VALUE, est[extra] + ramp + 1) << 32)
                | ((long) RAMP_REST << 28)
                | extra;
      }
    }
    long processed = 0;
    long bound = 0; // U(t)
    long slope = 0; // slope of U
    long hmax = 0;
    long time = Long.MIN_VALUE;
    int e = 0;
    int x = 0;
    while (true) {
      long next = e < omegaCount ? eventTime(omegaEvents[e]) : Long.MAX_VALUE;
      if (x < extraCount && eventTime(extraEvents[x]) < next) {
        next = eventTime(extraEvents[x]);
      }
      if (time < cut && cut < next) {
        next = cut;
      }
      if (next > d) {
        next = d;
      }
      if (time != Long.MIN_VALUE && next > time) {
        long rate = Math.min(time >= cut ? reducedCapacity : capacity, hmax);
        long length = next - time;
        long gap = bound - processed;
        long nextBound = bound + slope * length;
        if (slope >= rate || gap / (rate - slope) >= length) {
          processed += rate * length;
        } else {
          processed = nextBound;
        }
        bound = nextBound;
        if (processed >= target) {
          return processed;
        }
      }
      time = next;
      if (time >= d) {
        return processed;
      }
      while (e < omegaCount && eventTime(omegaEvents[e]) == time) {
        long key = omegaEvents[e++];
        int k = eventTask(key);
        switch (eventKind(key)) {
          case START:
            slope += resMax[k];
            hmax += resMax[k];
            break;
          case RAMP_END:
            slope -= resMax[k] - rest[k];
            break;
          case RAMP_REST:
            slope -= rest[k];
            break;
          default:
            hmax -= resMax[k];
            break;
        }
      }
      while (x < extraCount && eventTime(extraEvents[x]) == time) {
        long key = extraEvents[x++];
        switch (eventKind(key)) {
          case START:
            slope += resMax[extra];
            hmax += resMax[extra];
            break;
          case RAMP_END:
            slope -= resMax[extra] - rest[extra];
            break;
          default:
            slope -= rest[extra];
            break;
        }
      }
    }
  }
}
