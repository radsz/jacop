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
import java.util.IdentityHashMap;
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
   * point where the compulsory parts of other tasks leave too little capacity, or a time window
   * where the tasks need more energy than the limit gives. Durations and resource uses count at
   * their smallest values and the limit at its largest, each with its bound in the reason.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (!explainable()) {
      return false;
    }
    snapshot(trail, entry);
    IntVar y = trail.variable(entry);
    int j = -1;
    for (int i = 0; i < taskNormal.length; i++) {
      if (taskNormal[i].start == y) {
        if (j >= 0) {
          return false;
        }
        j = i;
      }
    }
    if (j < 0) {
      return y == limit && kind == AtomicTrail.GE && explainLimit(trail, entry, out);
    }
    TaskView own = taskNormal[j];
    int d = dmin(entry, own);
    int r = rmin(entry, own);
    if (d <= 0 || r <= 0) {
      return false;
    }
    trail.addLowerBound(own.dur, entry, out);
    trail.addLowerBound(own.res, entry, out);
    int room = limitMax - r;
    int v = trail.value(entry);
    if (kind == AtomicTrail.NE) {
      for (int t = v; t < v + d; t++) {
        if (overloaded(trail, entry, j, t, room, null)) {
          overloaded(trail, entry, j, t, room, out);
          return true;
        }
      }
      int[] window = overloadedWindow(trail, entry, j, v);
      if (window == null) {
        return false;
      }
      addWindowReason(trail, entry, j, window, out);
      return true;
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
        if (t >= u) {
          overloaded(trail, entry, j, t, room, out);
          u = t + 1;
          continue;
        }
        int[] window = overloadedWindow(trail, entry, j, u);
        if (window == null) {
          return false;
        }
        addWindowReason(trail, entry, j, window, out);
        u++;
        while (u < v && windowExcess(trail, entry, j, u, window[0], window[1]) > 0) {
          u++;
        }
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
        if (t < u + d) {
          overloaded(trail, entry, j, t, room, out);
          u = t - d;
          continue;
        }
        int[] window = overloadedWindow(trail, entry, j, u);
        if (window == null) {
          return false;
        }
        addWindowReason(trail, entry, j, window, out);
        u--;
        while (u > v && windowExcess(trail, entry, j, u, window[0], window[1]) > 0) {
          u--;
        }
      }
    }
    return true;
  }

  /**
   * Explains a failure by a time point where the compulsory parts exceed the limit, or else by a
   * time window where the tasks need more energy than the limit gives.
   */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!explainable()) {
      return false;
    }
    int position = trail.size();
    snapshot(trail, position);
    int room = limitMax;
    for (TaskView task : taskNormal) {
      int from = lst(task);
      int to = est(task) + dmin(position, task);
      for (int t = from; t < to; t++) {
        if (overloaded(trail, position, -1, t, room, null)) {
          overloaded(trail, position, -1, t, room, out);
          return true;
        }
      }
    }
    int[] window = overloadedWindow(trail, position, -1, 0);
    if (window != null) {
      addWindowReason(trail, position, -1, window, out);
      return true;
    }
    return false;
  }

  /** The most windows one explanation weighs before it leaves the atom to the generic reason. */
  private static final int WINDOW_BUDGET = 1 << 16;

  // the bounds of the tasks and the limit's maximum just before the position being explained
  private TaskView[] snapshotTasks;
  private IdentityHashMap<TaskView, Integer> taskSlot;
  private int[] snapshotEst;
  private int[] snapshotLst;
  private int[] snapshotDur;
  private int[] snapshotRes;
  private int limitMax;
  private int snapshotPosition = -1;
  private int windowBudget;

  // the explanations hold for the relation of every task present, using the smallest durations
  // and resource uses and the largest limit; CumulativeOptional and other subclasses with another
  // relation use the generic reason
  private boolean explainable() {
    Class<?> type = getClass();
    return type == CumulativeBasic.class
        || type == Cumulative.class
        || type == CumulativeUnary.class;
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
        load += rmin(position, task);
      }
    }
    if (load <= room || out == null) {
      return load > room;
    }
    Integer[] order = new Integer[taskNormal.length];
    for (int i = 0; i < order.length; i++) {
      order[i] = i;
    }
    Arrays.sort(
        order,
        (a, b) -> Integer.compare(rmin(position, taskNormal[b]), rmin(position, taskNormal[a])));
    trail.addUpperBound(limit, position, out);
    long sum = 0;
    for (int i : order) {
      TaskView task = taskNormal[i];
      if (i != skip && covers(trail, position, task, t)) {
        addTaskReasonAt(trail, position, task, t, out);
        sum += rmin(position, task);
        if (sum > room) {
          break;
        }
      }
    }
    return true;
  }

  /**
   * Finds a time window [a, b) where the tasks other than j, with task j started at u (when j is
   * not -1), need more energy than the limit gives over the window, just before a trail position:
   * each task needs at least its smallest overlap with the window over its start range. Returns the
   * window of the largest excess, or null.
   */
  private int[] overloadedWindow(AtomicTrail trail, int position, int j, int u) {
    int n = taskNormal.length;
    int[] from = new int[n + 1];
    int[] to = new int[2 * n + 1];
    int nf = 0;
    int nt = 0;
    for (int i = 0; i < n; i++) {
      if (i == j) {
        continue;
      }
      TaskView task = taskNormal[i];
      int est = est(task);
      int lst = lst(task);
      from[nf++] = est;
      int d = dmin(position, task);
      to[nt++] = est + d;
      to[nt++] = lst + d;
    }
    if (j >= 0) {
      from[nf++] = u;
      to[nt++] = u + dmin(position, taskNormal[j]);
    }
    int[] best = null;
    long bestExcess = 0;
    for (int f = 0; f < nf; f++) {
      for (int t = 0; t < nt; t++) {
        if (to[t] > from[f]) {
          if (--windowBudget < 0) {
            return null;
          }
          long excess = windowExcess(trail, position, j, u, from[f], to[t]);
          if (excess > bestExcess) {
            bestExcess = excess;
            best = new int[] {from[f], to[t]};
          }
        }
      }
    }
    return best;
  }

  /** The energy the tasks need in [a, b) beyond what the limit gives (see overloadedWindow). */
  private long windowExcess(AtomicTrail trail, int position, int j, int u, int a, int b) {
    long need = 0;
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      int d = dmin(position, task);
      long r = rmin(position, task);
      if (i == j) {
        need += r * overlap(u, d, a, b);
      } else {
        int est = est(task);
        int lst = lst(task);
        need += r * Math.min(overlap(est, d, a, b), overlap(lst, d, a, b));
      }
    }
    return need - (long) limitMax * (b - a);
  }

  private static int overlap(int start, int d, int a, int b) {
    return Math.max(0, Math.min(start + d, b) - Math.max(start, a));
  }

  /**
   * Explains a lower bound of the limit by the time point where the compulsory parts use the most,
   * with the values between that use and the bound already out of the limit's domain.
   */
  private boolean explainLimit(AtomicTrail trail, int entry, EntryList out) {
    int v = trail.value(entry);
    int best = Integer.MIN_VALUE;
    long bestLoad = -1;
    for (TaskView task : taskNormal) {
      int t = lst(task);
      long load = 0;
      for (TaskView other : taskNormal) {
        if (covers(trail, entry, other, t)) {
          load += rmin(entry, other);
        }
      }
      if (load > bestLoad) {
        bestLoad = load;
        best = t;
      }
    }
    long from = Math.max(bestLoad, trail.minBefore(limit, entry));
    if (v - from > 1024) {
      return false; // too many values to check one by one
    }
    int mark = out.size();
    for (long u = from; u < v; u++) {
      if (!trail.excludedBefore(limit, (int) u, entry, out)) {
        out.truncate(mark);
        return false;
      }
    }
    if (bestLoad > trail.minBefore(limit, entry)) {
      for (TaskView task : taskNormal) {
        if (covers(trail, entry, task, best) && rmin(entry, task) > 0) {
          addTaskReasonAt(trail, entry, task, best, out);
        }
      }
    } else {
      trail.addLowerBound(limit, entry, out);
    }
    return true;
  }

  /** Adds the bounds of the tasks other than j that need energy in the window. */
  private void addWindowReason(
      AtomicTrail trail, int position, int j, int[] window, EntryList out) {
    trail.addUpperBound(limit, position, out);
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      if (i == j) {
        continue;
      }
      int d = dmin(position, task);
      int est = est(task);
      int lst = lst(task);
      if (rmin(position, task) > 0
          && Math.min(overlap(est, d, window[0], window[1]), overlap(lst, d, window[0], window[1]))
              > 0) {
        addTaskReason(trail, position, task, out);
      }
    }
  }

  private boolean covers(AtomicTrail trail, int position, TaskView task, int t) {
    return lst(task) <= t && t < est(task) + dmin(position, task);
  }

  // the smallest duration and resource use of a task just before a trail position
  private int dmin(int position, TaskView task) {
    assert position == snapshotPosition : "bounds read at another position than the snapshot";
    return snapshotDur[slot(task)];
  }

  private int rmin(int position, TaskView task) {
    assert position == snapshotPosition : "bounds read at another position than the snapshot";
    return snapshotRes[slot(task)];
  }

  private int est(TaskView task) {
    return snapshotEst[slot(task)];
  }

  private int lst(TaskView task) {
    return snapshotLst[slot(task)];
  }

  private int slot(TaskView task) {
    return taskSlot.get(task);
  }

  /**
   * Reads the bounds of every task and the limit's maximum just before a trail position, once per
   * explanation, since each read walks the variable's entries; and sets the work an explanation may
   * spend on windows.
   */
  private void snapshot(AtomicTrail trail, int position) {
    int n = taskNormal.length;
    if (taskSlot == null) {
      // the propagators reorder taskNormal, so the slots follow a copy of their own
      snapshotTasks = taskNormal.clone();
      taskSlot = new IdentityHashMap<>();
      for (int i = 0; i < n; i++) {
        taskSlot.put(snapshotTasks[i], i);
      }
      snapshotEst = new int[n];
      snapshotLst = new int[n];
      snapshotDur = new int[n];
      snapshotRes = new int[n];
    }
    for (int i = 0; i < n; i++) {
      TaskView task = snapshotTasks[i];
      snapshotEst[i] = trail.minBefore(task.start, position);
      snapshotLst[i] = trail.maxBefore(task.start, position);
      snapshotDur[i] = trail.minBefore(task.dur, position);
      snapshotRes[i] = trail.minBefore(task.res, position);
    }
    limitMax = trail.maxBefore(limit, position);
    snapshotPosition = position;
    windowBudget = WINDOW_BUDGET;
  }

  /**
   * Adds what makes a task's compulsory part cover time t, lifted: the earliest bounds of its start
   * on the trail that keep it within [t - d + 1, t] for its smallest duration d, and the lower
   * bounds of its duration and resource use.
   */
  private void addTaskReasonAt(
      AtomicTrail trail, int position, TaskView task, int t, EntryList out) {
    trail.addBoundReaching(task.start, position, true, (long) t - dmin(position, task) + 1, out);
    trail.addBoundReaching(task.start, position, false, t, out);
    trail.addLowerBound(task.dur, position, out);
    trail.addLowerBound(task.res, position, out);
  }

  /** Adds the bounds of a task's start and the lower bounds of its duration and resource use. */
  private static void addTaskReason(AtomicTrail trail, int position, TaskView task, EntryList out) {
    trail.addLowerBound(task.start, position, out);
    trail.addUpperBound(task.start, position, out);
    trail.addLowerBound(task.dur, position, out);
    trail.addLowerBound(task.res, position, out);
  }
}
