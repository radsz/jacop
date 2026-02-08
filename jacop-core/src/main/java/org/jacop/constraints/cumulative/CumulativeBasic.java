/*
 * CumulativeBasic.java
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
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * CumulativeBasic implements the cumulative constraint using time tabling algorithm.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class CumulativeBasic extends Constraint {

  private static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final boolean debug = false;
  private static final boolean debugNarr = false;
  // event type
  private static final int profile = 0;
  private static final int pruneStart = 1;
  private static final int pruneEnd = 2;

  /** It specifies the limit of the profile of cumulative use of resources. */
  public final IntVar limit;

  /*
   * All tasks of the constraint
   */
  final TaskView[] taskNormal;
  private final Comparator<Event> eventComparator =
      (Event o1, Event o2) -> {
        int dateDiff = o1.date() - o2.date();
        return dateDiff == 0 ? (o1.type() - o2.type()) : dateDiff;
      };

  /**
   * It specifies whether there possibly exist tasks that have duration or resource variable min
   * value equal zero.
   */
  boolean possibleZeroTasks;

  CumulativePrimary cumulativeForConstants;

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeBasic(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

    checkInputForNullness(
        new String[] {"starts", "durations", "resources", "limit"},
        new Object[][] {starts, durations, resources, {limit}});
    checkInput(durations, i -> i.min() >= 0, "durations cannot allow non-negative values");
    checkInput(resources, i -> i.min() >= 0, "resources cannot allow non-negative values");

    if (starts.length != durations.length) {
      throw new IllegalArgumentException(
          "Cumulative constraint needs to have starts and durations lists the same length.");
    }
    if (starts.length != resources.length) {
      throw new IllegalArgumentException(
          "Cumulative constraint needs to have starts and resources lists the same length.");
    }

    if (limit.min() >= 0) {
      this.limit = limit;
    } else {
      throw new IllegalArgumentException("\nResource limit must be >= 0 in cumulative");
    }

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();
    this.taskNormal = new TaskNormalView[starts.length];

    for (int i = 0; i < starts.length; i++) {
      taskNormal[i] = new TaskNormalView(starts[i], durations[i], resources[i]);
      taskNormal[i].index = i;
      if (durations[i].min() == 0 || resources[i].min() == 0) {
        possibleZeroTasks = true;
      }
    }

    if (grounded(durations) && grounded(resources)) {
      int[] durInt = new int[durations.length];
      for (int i = 0; i < durations.length; i++) {
        durInt[i] = durations[i].value();
      }
      int[] resInt = new int[resources.length];
      for (int i = 0; i < resources.length; i++) {
        resInt[i] = resources[i].value();
      }

      cumulativeForConstants = new CumulativePrimary(starts, durInt, resInt, limit);
    }

    setScope(
        Stream.concat(
            Stream.concat(Arrays.stream(starts), Arrays.stream(durations)),
            Stream.concat(Arrays.stream(resources), Stream.of(limit))));
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeBasic(
      List<? extends IntVar> starts,
      List<? extends IntVar> durations,
      List<? extends IntVar> resources,
      IntVar limit) {

    this(
        starts.toArray(new IntVar[0]),
        durations.toArray(new IntVar[0]),
        resources.toArray(new IntVar[0]),
        limit);
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;
      profileProp(store);

    } while (store.propagationHasOccurred);
  }

  void profileProp(Store store) {

    if (cumulativeForConstants == null) {
      sweepPruning(store);
    } else {
      cumulativeForConstants.sweepPruning(store);
    }
    updateTasksRes(store);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  private void updateTasksRes(Store store) {
    int limitMax = limit.max();
    for (TaskView t : taskNormal) {
      t.res.domain.inMax(store.level, t.res, limitMax);
    }
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : cumulativeBasic([ ");
    for (int i = 0; i < taskNormal.length - 1; i++) {
      result.append(taskNormal[i]).append(", ");
    }

    result.append(taskNormal[taskNormal.length - 1]);

    result.append(" ]").append(", limit = ").append(limit).append(" )");

    return result.toString();
  }

  // Sweep algorithm for profile
  private void sweepPruning(Store store) {

    Event[] es = new Event[4 * taskNormal.length];
    final int limitMax = limit.max();

    int j = 0;
    int minProfile = Integer.MAX_VALUE;
    int maxProfile = Integer.MIN_VALUE;
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView t = taskNormal[i];
      t.index = i;

      // mandatory task parts to create profile
      int min = t.lst();
      int max = t.ect();
      int tResMin = t.res.min();
      if (min < max && tResMin > 0) {
        es[j++] = new Event(profile, t, min, tResMin);
        es[j++] = new Event(profile, t, max, -tResMin);
        minProfile = Math.min(min, minProfile);
        maxProfile = Math.max(max, maxProfile);
      }
    }
    if (j == 0) {
      return;
    }

    for (TaskView t : taskNormal) {
      // overlapping tasks for pruning
      // from start to end
      int min = t.est();
      int max = t.lct();
      if (t.maxNonZero()
          && !(min > maxProfile || max < minProfile)) { // t.dur.max() > 0 && t.res.max() > 0
        es[j++] = new Event(pruneStart, t, min, 0);
        es[j++] = new Event(pruneEnd, t, max, 0);
      }
    }

    int N = j;
    Arrays.sort(es, 0, N, eventComparator);

    if (debugNarr) {
      log.debug("{}", Arrays.asList(es));
      log.debug("limit.max() = {}", limitMax);
      log.debug("===========================");
    }

    final BitSet tasksToPrune = new BitSet(taskNormal.length);
    final boolean[] inProfile = new boolean[taskNormal.length];

    // used for start variable pruning
    final int[] startExcluded = new int[taskNormal.length];
    final boolean[] startConsidered = new boolean[taskNormal.length];

    // used for duration variable pruning
    int[] maxDuration = new int[taskNormal.length];
    // value Integer.MIN_VALUE for maxDuration means that the
    // duration does not need to be prunned
    Arrays.fill(maxDuration, Integer.MIN_VALUE);
    int[] lastStart = new int[taskNormal.length];
    Arrays.fill(lastStart, Integer.MAX_VALUE);
    int[] lastFree = new int[taskNormal.length];
    Arrays.fill(lastFree, Integer.MAX_VALUE);
    boolean[] barier = new boolean[taskNormal.length];

    int curProfile = 0;
    for (int i = 0; i < N; i++) {

      Event e = es[i];
      Event ne = null; // next event
      if (i < N - 1) {
        ne = es[i + 1];
      }

      switch (e.type()) {
        case profile: // =========== profile event ===========
          curProfile += e.value();
          inProfile[e.task().index] = e.value() > 0;

          if (ne == null || ne.type() != profile || e.date < ne.date()) {
            // check the tasks for pruning only at the end of all profile events

            if (debug) {
              log.debug("Profile at {}: {}", e.date(), curProfile);
            }

            // prune limit variable
            if (curProfile > limit.min()) {
              limit.domain.inMin(store.level, limit, curProfile);
            }

            for (int ti = tasksToPrune.nextSetBit(0);
                ti >= 0;
                ti = tasksToPrune.nextSetBit(ti + 1)) {
              TaskView t = taskNormal[ti];

              int profileValue = curProfile;
              if (inProfile[ti]) {
                profileValue -= t.res.min();
              }
              boolean noSpace = limitMax - profileValue < t.res.min();

              // ========= Pruning start variable
              if (t.exists()) { // t.res.min() > 0 && t.dur.min() > 0
                if (!startConsidered[ti]) {
                  if (noSpace) {
                    startExcluded[ti] = e.date() - t.dur.min() + 1;
                    startConsidered[ti] = true;
                  }
                } else // startExcluded[ti] != Integer.MAX_VALUE
                if (!noSpace) {
                  // end of excluded interval

                  if (debugNarr) {
                    log.debug(
                        ">>> CumulativeBasic Profile 1. Narrowed {} \\ {} => {}",
                        t.start,
                        new IntervalDomain(startExcluded[ti], e.date() - 1),
                        t.start);
                  }

                  t.start.domain.inComplement(
                      store.level, t.start, startExcluded[ti], e.date() - 1);

                  startConsidered[ti] = false;
                }
              }

              // ========= for duration pruning
              if (noSpace) {
                maxDuration[ti] = Math.max(maxDuration[ti], e.date() - lastFree[ti]);
                barier[ti] = true;
              } else if (barier[ti]) { // free to go
                barier[ti] = false;
                lastFree[ti] = e.date();
                if (e.date() <= t.start.max()) {
                  lastStart[ti] = e.date();
                }
              }

              // ========= resource pruning;

              // cannot use more efficient inProfile[ti] (instead of t.lst() <= e.date() && e.date()
              // < t.ect())
              // since tasks with res = 0 are not in the profile :(
              if (limitMax - profileValue < t.res.max()
                  && t.lst() <= e.date()
                  && e.date() < t.ect()) {
                t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
              }
            }
          }

          break;

        case pruneStart: // =========== start of a task ===========
          int profileValue = curProfile;
          TaskView t = e.task();
          int ti = t.index;

          if (inProfile[ti]) {
            profileValue -= t.res.min();
          }
          boolean noSpace = limitMax - profileValue < t.res.min();

          // ========= for start pruning
          if (t.exists() && noSpace) { // t.res.min() > 0 && t.dur.min() > 0
            startExcluded[ti] = e.date();
            startConsidered[ti] = true;
          }

          // ========= for duration pruning
          if (noSpace) {
            barier[ti] = true;
          } else {
            lastStart[ti] = t.start.min();
            lastFree[ti] = t.start.min();
            barier[ti] = false;
          }

          // ========= resource pruning
          if (limitMax - profileValue < t.res.max() && t.lst() <= e.date() && e.date() < t.ect()) {
            t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
          }

          tasksToPrune.set(ti);
          break;

        case pruneEnd: // =========== end of a task ===========
          profileValue = curProfile;
          t = e.task();
          ti = t.index;

          if (inProfile[ti]) {
            profileValue -= t.res.min();
          }

          // ========= pruning start variable
          if (t.exists() && startConsidered[ti]) {
            // task ends and we remove forbidden area

            if (debugNarr) {
              log.debug(
                  ">>> CumulativeBasic Profile 2. Narrowed {} inMax {}",
                  t.start,
                  startExcluded[ti] - 1);
            }

            t.start.domain.inMax(store.level, t.start, startExcluded[ti] - 1);

            if (debugNarr) {
              log.debug(" => {}", t.start);
            }
          }

          startConsidered[ti] = false;

          // ========= resource pruning
          if (limitMax - profileValue < t.res.max() && t.lst() <= e.date() && e.date() < t.ect()) {
            t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
          }

          // ========= duration pruning
          if (lastStart[ti] >= lastFree[ti] && limitMax - profileValue >= t.res.min()) {
            maxDuration[ti] = Math.max(maxDuration[ti], e.date() - lastStart[ti]);
          }

          if (lastStart[ti] == Integer.MAX_VALUE) { // no room for the task; must have 0 duration
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

          tasksToPrune.set(ti, false);
          break;

        default:
          throw new RuntimeException("Internal error in " + getClass().getName());
      }
    }
  }

  private record Event(int type, TaskView t, int date, int value) {

    TaskView task() {
      return t;
    }

    @Override
    public String toString() {
      String result = "(";
      result += type == profile ? "profile, " : type == pruneStart ? "pruneStart, " : "pruneEnd, ";
      result += t + ", " + date + ", " + value + ")\n";
      return result;
    }
  }
}
