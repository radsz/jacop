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
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * CumulativeBasic implements the cumulative constraint using time tabling algorithm.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class CumulativeBasic extends Constraint implements Copyable<CumulativeBasic>, Explainable {

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

  private final TimetableSweep sweep = new TimetableSweep();

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
        starts,
        durations,
        resources,
        new Object[] {limit});
    checkInput(durations, i -> i.min() >= 0, "durations cannot allow negative values");
    checkInput(resources, i -> i.min() >= 0, "resources cannot allow negative values");

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
        starts.toArray(IntVar[]::new),
        durations.toArray(IntVar[]::new),
        resources.toArray(IntVar[]::new),
        limit);
  }

  /**
   * It imposes the constraint; a constraint without tasks is always satisfied, since the limit is
   * not negative, so it is not imposed.
   *
   * @param store the constraint store in which the constraint is imposed.
   */
  @Override
  public void impose(Store store) {
    if (taskNormal.length == 0) {
      return;
    }
    super.impose(store);
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
      // a task with zero duration does not use the resource, so it may use more than the limit
      if (t.dur.min() > 0) {
        t.res.domain.inMax(store.level, t.res, limitMax);
      } else if (t.res.min() > limitMax) {
        t.dur.domain.inMax(store.level, t.dur, 0);
      }
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
    sweep.prune(store, taskNormal, limit, DEBUG, DEBUG_NARR, null, null);
  }

  /**
   * Returns the counterparts of the variables of the tasks in the order the tasks were given.
   *
   * @param map the counterparts of the variables of this constraint.
   * @return the starts, the durations and the resources.
   */
  IntVar[][] taskVariables(VarMap map) {
    int n = taskNormal.length;
    IntVar[][] vars = new IntVar[3][n];
    // the array keeps the order of the tasks; their index field is reused by propagation
    for (int i = 0; i < n; i++) {
      vars[0][i] = map.get(taskNormal[i].start);
      vars[1][i] = map.get(taskNormal[i].dur);
      vars[2][i] = map.get(taskNormal[i].res);
    }
    return vars;
  }

  @Override
  public CumulativeBasic copy(VarMap map) {
    IntVar[][] t = taskVariables(map);
    return new CumulativeBasic(t[0], t[1], t[2], map.get(limit));
  }

  /**
   * Explains a bound of a start time by the time table: each start value it removed overlaps a time
   * point where the compulsory parts of other tasks leave too little capacity. It needs fixed
   * durations, resource uses and limit; otherwise, and for holes, the generic reason is used.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (!fixedTasks()) {
      return false;
    }
    IntVar y = trail.var(entry);
    int j = -1;
    for (int i = 0; i < taskNormal.length; i++) {
      if (taskNormal[i].start == y) {
        if (j >= 0) {
          return false;
        }
        j = i;
      }
    }
    if (j < 0 || taskNormal[j].dur.value() <= 0 || taskNormal[j].res.value() <= 0) {
      return false;
    }
    int d = taskNormal[j].dur.value();
    int room = limit.value() - taskNormal[j].res.value();
    int v = trail.value(entry);
    if (kind == AtomicTrail.NE) {
      for (int t = v; t < v + d; t++) {
        if (overloaded(trail, entry, j, t, room, null)) {
          overloaded(trail, entry, j, t, room, out);
          return true;
        }
      }
      return false;
    } else if (kind == AtomicTrail.GE) {
      trail.addLowerBound(y, entry, out);
      int u = trail.minBefore(y, entry);
      while (u < v) {
        if (trail.excludedBefore(y, u, entry, out)) {
          u++;
          continue;
        }
        int t = u + d - 1;
        while (t >= u && !overloaded(trail, entry, j, t, room, null)) {
          t--;
        }
        if (t < u) {
          return false;
        }
        overloaded(trail, entry, j, t, room, out);
        u = t + 1;
      }
    } else {
      trail.addUpperBound(y, entry, out);
      int u = trail.maxBefore(y, entry);
      while (u > v) {
        if (trail.excludedBefore(y, u, entry, out)) {
          u--;
          continue;
        }
        int t = u;
        while (t < u + d && !overloaded(trail, entry, j, t, room, null)) {
          t++;
        }
        if (t == u + d) {
          return false;
        }
        overloaded(trail, entry, j, t, room, out);
        u = t - d;
      }
    }
    return true;
  }

  /** Explains a failure by a time point where the compulsory parts exceed the limit. */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!fixedTasks()) {
      return false;
    }
    int position = trail.size();
    int room = limit.value();
    for (TaskView task : taskNormal) {
      int from = trail.maxBefore(task.start, position);
      int to = trail.minBefore(task.start, position) + task.dur.value();
      for (int t = from; t < to; t++) {
        if (overloaded(trail, position, -1, t, room, null)) {
          overloaded(trail, position, -1, t, room, out);
          return true;
        }
      }
    }
    return false;
  }

  private boolean fixedTasks() {
    if (!limit.singleton() || possibleZeroTasks) {
      return false;
    }
    for (TaskView task : taskNormal) {
      if (!task.dur.singleton() || !task.res.singleton()) {
        return false;
      }
    }
    return true;
  }

  /**
   * Tells whether the compulsory parts of the tasks other than {@code skip}, just before a trail
   * position, use more than {@code room} at time t; with {@code out}, adds the bounds of the
   * largest of those tasks until they exceed it.
   */
  private boolean overloaded(
      AtomicTrail trail, int position, int skip, int t, int room, EntryList out) {
    long load = 0;
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      if (i != skip && covers(trail, position, task, t)) {
        load += task.res.value();
      }
    }
    if (load <= room || out == null) {
      return load > room;
    }
    Integer[] order = new Integer[taskNormal.length];
    for (int i = 0; i < order.length; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (a, b) -> taskNormal[b].res.value() - taskNormal[a].res.value());
    long sum = 0;
    for (int i : order) {
      TaskView task = taskNormal[i];
      if (i != skip && covers(trail, position, task, t)) {
        trail.addLowerBound(task.start, position, out);
        trail.addUpperBound(task.start, position, out);
        sum += task.res.value();
        if (sum > room) {
          break;
        }
      }
    }
    return true;
  }

  private static boolean covers(AtomicTrail trail, int position, TaskView task, int t) {
    return trail.maxBefore(task.start, position) <= t
        && t < trail.minBefore(task.start, position) + task.dur.value();
  }
}
