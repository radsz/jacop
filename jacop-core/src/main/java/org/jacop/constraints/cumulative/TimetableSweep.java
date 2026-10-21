/*
 * TimetableSweep.java
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
import java.util.BitSet;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * The time-table sweep of {@link CumulativeBasic} and {@link ProfileOptional} on tasks with
 * variable durations and resource uses: it builds the profile of compulsory parts and prunes the
 * starts, durations and resource uses of the tasks against it.
 *
 * <p>Events are encoded as long keys (date, type, insertion sequence), so sorting them gives the
 * order of a stable sort by date and type, and the work arrays are reused between calls.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
class TimetableSweep {

  // event types, in the order events of the same date are processed
  static final int PROFILE = 0;
  static final int PRUNE_START = 1;
  static final int PRUNE_END = 2;

  private static final int SEQUENCE_MASK = (1 << 30) - 1;

  /** Receives each profile event before it is added to the profile. */
  @FunctionalInterface
  interface ProfileListener {
    void onProfileEvent(int date, int value);
  }

  private long[] eventKeys = new long[0];
  private TaskView[] eventTask = new TaskView[0];
  private int[] eventValue = new int[0];

  private BitSet tasksToPrune = new BitSet();
  private boolean[] inProfile = new boolean[0];
  // used for start variable pruning
  private int[] startExcluded = new int[0];
  private boolean[] startConsidered = new boolean[0];
  // used for duration variable pruning; Integer.MIN_VALUE means no pruning of the duration
  private int[] maxDuration = new int[0];
  private int[] lastStart = new int[0];
  private int[] lastFree = new int[0];
  private boolean[] barier = new boolean[0];

  private void ensureCapacity(int n) {
    if (inProfile.length < n) {
      eventKeys = new long[4 * n];
      eventTask = new TaskView[4 * n];
      eventValue = new int[4 * n];
      tasksToPrune = new BitSet(n);
      inProfile = new boolean[n];
      startExcluded = new int[n];
      startConsidered = new boolean[n];
      maxDuration = new int[n];
      lastStart = new int[n];
      lastFree = new int[n];
      barier = new boolean[n];
    }
  }

  private static int date(long key) {
    return (int) (key >> 32);
  }

  private static int type(long key) {
    return (int) (key >>> 30) & 3;
  }

  private static int sequence(long key) {
    return (int) key & SEQUENCE_MASK;
  }

  private void addEvent(int seq, int type, TaskView t, int date, int value) {
    eventKeys[seq] = ((long) date << 32) | ((long) type << 30) | seq;
    eventTask[seq] = t;
    eventValue[seq] = value;
  }

  /**
   * Runs the sweep.
   *
   * @param store the store.
   * @param tasks the tasks; their field index is set to their position.
   * @param limitVar the resource limit.
   * @param debug whether to log the profile.
   * @param debugNarr whether to log the pruning.
   * @param listener called on each profile event, or null.
   * @param postProcess run after the sweep, or null.
   */
  void prune(
      Store store,
      TaskView[] tasks,
      IntVar limitVar,
      boolean debug,
      boolean debugNarr,
      ProfileListener listener,
      Runnable postProcess) {

    final int n = tasks.length;
    ensureCapacity(n);
    final int limitMax = limitVar.max();

    int j = 0;
    int minProfile = Integer.MAX_VALUE;
    int maxProfile = Integer.MIN_VALUE;
    for (int i = 0; i < n; i++) {
      TaskView t = tasks[i];
      t.index = i;

      // mandatory task parts to create PROFILE
      int min = t.lst();
      int max = t.ect();
      int tResMin = t.res.min();
      if (min < max && tResMin > 0) {
        addEvent(j, PROFILE, t, min, tResMin);
        j++;
        addEvent(j, PROFILE, t, max, -tResMin);
        j++;
        minProfile = Math.min(min, minProfile);
        maxProfile = Math.max(max, maxProfile);
      }
    }
    if (j == 0) {
      return;
    }

    for (int i = 0; i < n; i++) {
      TaskView t = tasks[i];
      // overlapping tasks for pruning, from start to end
      int min = t.est();
      int max = t.lct();
      if (t.maxNonZero() && min <= maxProfile && max >= minProfile) {
        addEvent(j, PRUNE_START, t, min, 0);
        j++;
        addEvent(j, PRUNE_END, t, max, 0);
        j++;
      }
    }

    final int count = j;
    Arrays.sort(eventKeys, 0, count);

    if (debugNarr) {
      for (int i = 0; i < count; i++) {
        long key = eventKeys[i];
        log.debug(
            "({}, {}, {}, {})",
            type(key),
            eventTask[sequence(key)],
            date(key),
            eventValue[sequence(key)]);
      }
      log.debug("limit.max() = {}", limitMax);
      log.debug("===========================");
    }

    tasksToPrune.clear();
    Arrays.fill(inProfile, 0, n, false);
    Arrays.fill(startExcluded, 0, n, 0);
    Arrays.fill(startConsidered, 0, n, false);
    Arrays.fill(maxDuration, 0, n, Integer.MIN_VALUE);
    Arrays.fill(lastStart, 0, n, Integer.MAX_VALUE);
    Arrays.fill(lastFree, 0, n, Integer.MAX_VALUE);
    Arrays.fill(barier, 0, n, false);

    int curProfile = 0;
    for (int i = 0; i < count; i++) {
      long key = eventKeys[i];
      int seq = sequence(key);
      int date = date(key);
      TaskView t = eventTask[seq];

      switch (type(key)) {
        case PROFILE:
          int value = eventValue[seq];
          if (listener != null) {
            listener.onProfileEvent(date, value);
          }
          curProfile += value;
          inProfile[t.index] = value > 0;

          if (i == count - 1
              || type(eventKeys[i + 1]) != PROFILE
              || date < date(eventKeys[i + 1])) {
            if (debug) {
              log.debug("Profile at {}: {}", date, curProfile);
            }
            if (curProfile > limitVar.min()) {
              limitVar.domain.inMin(store.level, limitVar, curProfile);
            }
            pruneAtProfileChange(store, date, curProfile, limitMax, tasks, debugNarr);
          }
          break;

        case PRUNE_START:
          pruneStart(store, t, date, curProfile, limitMax);
          break;

        case PRUNE_END:
          pruneEnd(store, t, date, curProfile, limitMax, debugNarr);
          break;

        default:
          throw new IllegalStateException("Unknown event type");
      }
    }

    if (postProcess != null) {
      postProcess.run();
    }
  }

  private void pruneStart(Store store, TaskView t, int date, int curProfile, int limitMax) {
    int ti = t.index;
    int profileValue = inProfile[ti] ? curProfile - t.res.min() : curProfile;
    boolean noSpace = limitMax - profileValue < t.res.min();

    if (t.exists() && noSpace) {
      startExcluded[ti] = date;
      startConsidered[ti] = true;
    }

    if (noSpace) {
      barier[ti] = true;
    } else {
      lastStart[ti] = t.start.min();
      lastFree[ti] = t.start.min();
      barier[ti] = false;
    }

    if (limitMax - profileValue < t.res.max() && t.lst() <= date && date < t.ect()) {
      t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
    }

    tasksToPrune.set(ti);
  }

  private void pruneEnd(
      Store store, TaskView t, int date, int curProfile, int limitMax, boolean debugNarr) {
    int ti = t.index;
    int profileValue = inProfile[ti] ? curProfile - t.res.min() : curProfile;

    if (t.exists() && startConsidered[ti]) {
      if (debugNarr) {
        log.debug(
            ">>> CumulativeBasic Profile 2. Narrowed {} inMax {}", t.start, startExcluded[ti] - 1);
      }

      t.start.domain.inMax(store.level, t.start, startExcluded[ti] - 1);

      if (debugNarr) {
        log.debug(" => {}", t.start);
      }
    }

    startConsidered[ti] = false;

    if (limitMax - profileValue < t.res.max() && t.lst() <= date && date < t.ect()) {
      t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
    }

    if (lastStart[ti] >= lastFree[ti] && limitMax - profileValue >= t.res.min()) {
      maxDuration[ti] = Math.max(maxDuration[ti], date - lastStart[ti]);
    }

    if (lastStart[ti] == Integer.MAX_VALUE) {
      maxDuration[ti] = 0;
    }

    if (maxDuration[ti] != Integer.MIN_VALUE && maxDuration[ti] < t.dur.max()) {
      if (debugNarr) {
        log.debug(
            ">>> CumulativeBasic Profile 3. Narrowed {} in 0..{} => {}",
            t.dur,
            maxDuration[ti],
            t.dur);
      }

      t.dur.domain.inMax(store.level, t.dur, maxDuration[ti]);
    }

    tasksToPrune.clear(ti);
  }

  private void pruneAtProfileChange(
      Store store, int date, int curProfile, int limitMax, TaskView[] tasks, boolean debugNarr) {
    for (int ti = tasksToPrune.nextSetBit(0); ti >= 0; ti = tasksToPrune.nextSetBit(ti + 1)) {
      TaskView t = tasks[ti];
      int profileValue = inProfile[ti] ? curProfile - t.res.min() : curProfile;
      boolean noSpace = limitMax - profileValue < t.res.min();

      if (t.exists()) {
        if (!startConsidered[ti]) {
          if (noSpace) {
            startExcluded[ti] = date - t.dur.min() + 1;
            startConsidered[ti] = true;
          }
        } else if (!noSpace) {
          if (debugNarr) {
            log.debug(
                ">>> CumulativeBasic Profile 1. Narrowed {} \\ {} => {}",
                t.start,
                new IntervalDomain(startExcluded[ti], date - 1),
                t.start);
          }
          t.start.domain.inComplement(store.level, t.start, startExcluded[ti], date - 1);
          startConsidered[ti] = false;
        }
      }

      if (noSpace) {
        maxDuration[ti] = Math.max(maxDuration[ti], date - lastFree[ti]);
        barier[ti] = true;
      } else if (barier[ti]) {
        barier[ti] = false;
        lastFree[ti] = date;
        if (date <= t.start.max()) {
          lastStart[ti] = date;
        }
      }

      if (limitMax - profileValue < t.res.max() && t.lst() <= date && date < t.ect()) {
        t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
      }
    }
  }
}
