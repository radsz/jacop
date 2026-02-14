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

  private static final boolean DEBUG = false;
  private static final boolean DEBUG_NARR = false;
  // event type
  protected static final int PROFILE = 0;
  protected static final int PRUNE_START = 1;
  protected static final int PRUNE_END = 2;

  /** It specifies the limit of the PROFILE of cumulative use of resources. */
  protected final IntVar limit;

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

  // Sweep algorithm for PROFILE
  private void sweepPruning(Store store) {
    sweepPruningCore(
        store,
        taskNormal,
        limit,
        DEBUG,
        DEBUG_NARR,
        (type, t, date, value) -> new Event(type, t, date, value),
        eventComparator,
        null,
        null);
  }

  /**
   * Shared core sweep pruning logic extracted from CumulativeBasic and ProfileOptional.
   *
   * @param store the store
   * @param tasks the tasks to process
   * @param limitVar the limit variable
   * @param debug debug flag
   * @param debugNarr detailed debug flag
   * @param eventFactory factory for creating events
   * @param eventComparator comparator for sorting events
   * @param profileUpdateCallback optional callback for profile updates (for optional tasks)
   * @param postProcessCallback optional callback for post-processing (for optional tasks)
   */
  @SuppressWarnings("unchecked")
  protected static <E> void sweepPruningCore(
      Store store,
      TaskView[] tasks,
      IntVar limitVar,
      boolean debug,
      boolean debugNarr,
      EventFactory<E> eventFactory,
      Comparator<E> eventComparator,
      ProfileUpdateCallback<E> profileUpdateCallback,
      Runnable postProcessCallback) {

    E[] es = (E[]) new Object[4 * tasks.length];
    final int limitMax = limitVar.max();

    int j = 0;
    int minProfile = Integer.MAX_VALUE;
    int maxProfile = Integer.MIN_VALUE;
    for (int i = 0; i < tasks.length; i++) {
      TaskView t = tasks[i];
      t.index = i;

      // mandatory task parts to create PROFILE
      int min = t.lst();
      int max = t.ect();
      int tResMin = t.res.min();
      if (min < max && tResMin > 0) {
        es[j++] = eventFactory.create(PROFILE, t, min, tResMin);
        es[j++] = eventFactory.create(PROFILE, t, max, -tResMin);
        minProfile = Math.min(min, minProfile);
        maxProfile = Math.max(max, maxProfile);
      }
    }
    if (j == 0) {
      return;
    }

    for (TaskView t : tasks) {
      // overlapping tasks for pruning
      // from start to end
      int min = t.est();
      int max = t.lct();
      if (t.maxNonZero()
          && !(min > maxProfile || max < minProfile)) { // t.dur.max() > 0 && t.res.max() > 0
        es[j++] = eventFactory.create(PRUNE_START, t, min, 0);
        es[j++] = eventFactory.create(PRUNE_END, t, max, 0);
      }
    }

    int N = j;
    Arrays.sort(es, 0, N, eventComparator);

    if (debugNarr) {
      log.debug("{}", Arrays.asList(es));
      log.debug("limit.max() = {}", limitMax);
      log.debug("===========================");
    }

    final BitSet tasksToPrune = new BitSet(tasks.length);
    final boolean[] inProfile = new boolean[tasks.length];

    // used for start variable pruning
    final int[] startExcluded = new int[tasks.length];
    final boolean[] startConsidered = new boolean[tasks.length];

    // used for duration variable pruning
    int[] maxDuration = new int[tasks.length];
    // value Integer.MIN_VALUE for maxDuration means that the
    // duration does not need to be prunned
    Arrays.fill(maxDuration, Integer.MIN_VALUE);
    int[] lastStart = new int[tasks.length];
    Arrays.fill(lastStart, Integer.MAX_VALUE);
    int[] lastFree = new int[tasks.length];
    Arrays.fill(lastFree, Integer.MAX_VALUE);
    boolean[] barier = new boolean[tasks.length];

    int curProfile = 0;
    for (int i = 0; i < N; i++) {

      E e = es[i];
      E ne = null; // next event
      if (i < N - 1) {
        ne = es[i + 1];
      }

      int eventType = getEventType(e);
      switch (eventType) {
        case PROFILE: // =========== PROFILE event ===========

          // Profile update callback for optional tasks
          if (profileUpdateCallback != null) {
            profileUpdateCallback.onProfileEvent(e, curProfile);
          }

          curProfile += getEventValue(e);
          inProfile[getEventTask(e).index] = getEventValue(e) > 0;

          if (ne == null || getEventType(ne) != PROFILE || getEventDate(e) < getEventDate(ne)) {
            // check the tasks for pruning only at the end of all PROFILE events

            if (debug) {
              log.debug("Profile at {}: {}", getEventDate(e), curProfile);
            }

            // prune limit variable
            if (curProfile > limitVar.min()) {
              limitVar.domain.inMin(store.level, limitVar, curProfile);
            }

            for (int ti = tasksToPrune.nextSetBit(0);
                ti >= 0;
                ti = tasksToPrune.nextSetBit(ti + 1)) {
              TaskView t = tasks[ti];

              int profileValue = curProfile;
              if (inProfile[ti]) {
                profileValue -= t.res.min();
              }
              boolean noSpace = limitMax - profileValue < t.res.min();

              // ========= Pruning start variable
              if (t.exists()) { // t.res.min() > 0 && t.dur.min() > 0
                if (!startConsidered[ti]) {
                  if (noSpace) {
                    startExcluded[ti] = getEventDate(e) - t.dur.min() + 1;
                    startConsidered[ti] = true;
                  }
                } else // startExcluded[ti] != Integer.MAX_VALUE
                if (!noSpace) {
                  // end of excluded interval

                  if (debugNarr) {
                    log.debug(
                        ">>> CumulativeBasic Profile 1. Narrowed {} \\ {} => {}",
                        t.start,
                        new IntervalDomain(startExcluded[ti], getEventDate(e) - 1),
                        t.start);
                  }

                  t.start.domain.inComplement(
                      store.level, t.start, startExcluded[ti], getEventDate(e) - 1);

                  startConsidered[ti] = false;
                }
              }

              // ========= for duration pruning
              if (noSpace) {
                maxDuration[ti] = Math.max(maxDuration[ti], getEventDate(e) - lastFree[ti]);
                barier[ti] = true;
              } else if (barier[ti]) { // free to go
                barier[ti] = false;
                lastFree[ti] = getEventDate(e);
                if (getEventDate(e) <= t.start.max()) {
                  lastStart[ti] = getEventDate(e);
                }
              }

              // ========= resource pruning;

              // cannot use more efficient inProfile[ti] (instead of t.lst() <= e.date() && e.date()
              // < t.ect())
              // since tasks with res = 0 are not in the PROFILE :(
              if (limitMax - profileValue < t.res.max()
                  && t.lst() <= getEventDate(e)
                  && getEventDate(e) < t.ect()) {
                t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
              }
            }
          }

          break;

        case PRUNE_START: // =========== start of a task ===========
          int profileValue = curProfile;
          TaskView t = getEventTask(e);
          int ti = t.index;

          if (inProfile[ti]) {
            profileValue -= t.res.min();
          }
          boolean noSpace = limitMax - profileValue < t.res.min();

          // ========= for start pruning
          if (t.exists() && noSpace) { // t.res.min() > 0 && t.dur.min() > 0
            startExcluded[ti] = getEventDate(e);
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
          if (limitMax - profileValue < t.res.max()
              && t.lst() <= getEventDate(e)
              && getEventDate(e) < t.ect()) {
            t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
          }

          tasksToPrune.set(ti);
          break;

        case PRUNE_END: // =========== end of a task ===========
          profileValue = curProfile;
          t = getEventTask(e);
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
          if (limitMax - profileValue < t.res.max()
              && t.lst() <= getEventDate(e)
              && getEventDate(e) < t.ect()) {
            t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
          }

          // ========= duration pruning
          if (lastStart[ti] >= lastFree[ti] && limitMax - profileValue >= t.res.min()) {
            maxDuration[ti] = Math.max(maxDuration[ti], getEventDate(e) - lastStart[ti]);
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
          throw new RuntimeException("Internal error");
      }
    }

    if (postProcessCallback != null) {
      postProcessCallback.run();
    }
  }

  // Functional interfaces for event handling
  @FunctionalInterface
  interface EventFactory<E> {
    E create(int type, TaskView task, int date, int value);
  }

  @FunctionalInterface
  interface ProfileUpdateCallback<E> {
    void onProfileEvent(E event, int currentProfile);
  }

  // Event accessor methods - handle both CumulativeBasic.Event (record) and ProfileOptional.Event
  // (class)
  @SuppressWarnings("unchecked")
  private static <E> int getEventType(E event) {
    if (event instanceof Event) {
      return ((Event) event).type();
    }
    // ProfileOptional.Event case - use reflection as fallback
    try {
      return (Integer) event.getClass().getMethod("type").invoke(event);
    } catch (Exception e) {
      throw new RuntimeException("Failed to get event type", e);
    }
  }

  @SuppressWarnings("unchecked")
  private static <E> int getEventDate(E event) {
    if (event instanceof Event) {
      return ((Event) event).date();
    }
    // ProfileOptional.Event case
    try {
      return (Integer) event.getClass().getMethod("date").invoke(event);
    } catch (Exception e) {
      throw new RuntimeException("Failed to get event date", e);
    }
  }

  @SuppressWarnings("unchecked")
  private static <E> int getEventValue(E event) {
    if (event instanceof Event) {
      return ((Event) event).value();
    }
    // ProfileOptional.Event case
    try {
      return (Integer) event.getClass().getMethod("value").invoke(event);
    } catch (Exception e) {
      throw new RuntimeException("Failed to get event value", e);
    }
  }

  @SuppressWarnings("unchecked")
  private static <E> TaskView getEventTask(E event) {
    if (event instanceof Event) {
      return ((Event) event).task();
    }
    // ProfileOptional.Event case
    try {
      return (TaskView) event.getClass().getMethod("task").invoke(event);
    } catch (Exception e) {
      throw new RuntimeException("Failed to get event task", e);
    }
  }

  private record Event(int type, TaskView t, int date, int value) {

    TaskView task() {
      return t;
    }

    @Override
    public String toString() {
      String result = "(";
      result +=
          type == PROFILE ? "PROFILE, " : type == PRUNE_START ? "PRUNE_START, " : "PRUNE_END, ";
      result += t + ", " + date + ", " + value + ")\n";
      return result;
    }
  }
}
