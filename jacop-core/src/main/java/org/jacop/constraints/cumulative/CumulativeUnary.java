/*
 * CumulativeUnary.java
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

import java.util.List;
import java.util.Optional;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * CumulativeUnary implements the scheduling constraint for unary resources using the overload
 * check, detectable precedences, not-first/not-last and edge finding of
 *
 * <p>Petr Vilim, "O(n log n) Filtering Algorithms for Unary Resource Constraints", Proceedings of
 * CP-AI-OR 2004,
 *
 * <p>with the overload check and detectable precedences in linear time after sorting on the time
 * line of Fahimi, Ouellet and Quimper, Constraints 23(3), 2018 (see {@link UnaryReasoning}).
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class CumulativeUnary extends Cumulative {

  /*
   * Local copies of tasks in normal and reserved views
   */
  final TaskView[] tvn;
  final TaskView[] tvr;
  // the rules of each view; they keep their task orders between calls
  private final UnaryReasoning unaryNormal = new UnaryReasoning();
  private final UnaryReasoning unaryReversed = new UnaryReasoning();
  boolean doProfile;
  boolean doUnaryEdgeFind;
  // the time-table rule for constant durations and resource uses, created on first use
  private UnaryTimetable timetable;

  // the rules in the order unaryRules runs them
  private static final int OVERLOAD = 0;
  private static final int DETECTABLE_NORMAL = 1;
  private static final int DETECTABLE_REVERSED = 2;
  private static final int NOT_LAST_NORMAL = 3;
  private static final int NOT_LAST_REVERSED = 4;
  private static final int EDGE_FIND_NORMAL = 5;
  private static final int EDGE_FIND_REVERSED = 6;
  // counts the changes of the bounds seen by the rules; a rule that pruned nothing at the current
  // count would prune nothing again
  private int boundsVersion;
  private final int[] quietAt = new int[EDGE_FIND_REVERSED + 1];
  // the tasks loaded into the rules: all of them, or those left after the fixed tasks that end
  // before all others, which only the time-table of CumulativeUnary must still check
  private boolean leaveOutFixedPrefix;
  private TaskView[] keptNormal = new TaskView[0];
  private TaskView[] keptReversed = new TaskView[0];
  private TaskView[] loadedNormal;
  private TaskView[] loadedReversed;
  private int loadedCount;
  private int[] leftOutTasks = new int[0];
  // with all tasks under the rules (no task can have a zero duration or resource use), the tasks
  // left out stay out in the subtree: tasks[0, leftOut) are left out, tasks[leftOut, n) are not
  private int[] tasks;
  private int[] positionOf;
  private TimeStamp<Integer> leftOut;
  private boolean trailLeftOut;
  private int from;
  private boolean firstLoad;

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doProfile defines whether to do profile-based propagation (true) or not (false).
   * @param doEdgeFind defines whether to do edge finding propagation (true) or not (false).
   */
  public CumulativeUnary(
      IntVar[] starts,
      IntVar[] durations,
      IntVar[] resources,
      IntVar limit,
      boolean doProfile,
      boolean doEdgeFind) {

    super(starts, durations, resources, limit);
    checkInput(durations, i -> i.min() >= 0, "duration does not allow negative values");
    checkInput(resources, i -> i.min() >= 0, "resource does not allow negative values");
    checkUnary(resources, limit);
    queueIndex = 2;

    tvn = new TaskNormalView[starts.length];
    tvr = super.taskReversed;
    for (int i = 0; i < starts.length; i++) {
      tvn[i] = new TaskNormalView(starts[i], durations[i], resources[i]);
      tvn[i].index = i;
    }

    if (!doProfile && !doEdgeFind) {
      log.warn("CumulativeUnary has no effect (no propagators defined).");
    }
    this.doProfile = doProfile;
    this.doUnaryEdgeFind = doEdgeFind;
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeUnary(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {
    this(starts, durations, resources, limit, false, true);
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doProfile defines whether to do profile-based propagation (true) or not (false); default
   *     is false
   */
  public CumulativeUnary(
      IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit, boolean doProfile) {
    this(starts, durations, resources, limit, doProfile, true);
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeUnary(
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
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doProfile defines whether to do profile-based propagation (true) or not (false); default
   *     is false
   */
  public CumulativeUnary(
      List<? extends IntVar> starts,
      List<? extends IntVar> durations,
      List<? extends IntVar> resources,
      IntVar limit,
      boolean doProfile) {

    this(
        starts.toArray(IntVar[]::new),
        durations.toArray(IntVar[]::new),
        resources.toArray(IntVar[]::new),
        limit,
        doProfile);
  }

  /**
   * Checks that the resource is unary: any two tasks that use the resource cannot run at the same
   * time, since the propagation of this constraint never lets them overlap.
   *
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources.
   */
  private static void checkUnary(IntVar[] resources, IntVar limit) {
    // the two smallest positive resource usages of different tasks
    long smallest = Long.MAX_VALUE;
    long nextSmallest = Long.MAX_VALUE;
    for (IntVar r : resources) {
      if (r.max() <= 0) {
        continue;
      }
      long positive = r.min() > 0 ? r.min() : r.dom().nextValue(0);
      if (positive < smallest) {
        nextSmallest = smallest;
        smallest = positive;
      } else if (positive < nextSmallest) {
        nextSmallest = positive;
      }
    }
    if (nextSmallest != Long.MAX_VALUE && smallest + nextSmallest <= limit.max()) {
      throw new IllegalArgumentException(
          "CumulativeUnary requires that no two tasks fit within the limit together, but two tasks"
              + " using "
              + smallest
              + " and "
              + nextSmallest
              + " fit within limit "
              + limit
              + "; use Cumulative instead.");
    }
  }

  @Override
  public void consistency(Store store) {

    if (!doProfile) {
      // the profile bounds the resource use by the limit; edge finding assumes each task fits
      fitTasksInLimit(store);
    }

    TaskView[] tn = filterZeroTasks(tvn);
    if (tn == null) {
      return;
    }
    TaskView[] tr = filterZeroTasks(tvr);

    boundsChanged();
    // the rules run only after a time-table call that pruned nothing, so the compulsory parts do
    // not overlap when the rules first load the tasks; a rule that fixes overlapping tasks makes
    // the
    // time-table fail in the next pass
    leaveOutFixedPrefix = doProfile;
    trailLeftOut = doProfile && !possibleZeroTasks;
    if (tasks == null) {
      initTasks(store);
    }
    from = trailLeftOut ? leftOut.value() : 0;
    do {

      store.propagationHasOccurred = false;

      if (doProfile) {
        unaryProfile(store);
        if (store.propagationHasOccurred) {
          boundsChanged();
        }
      }

      if (doUnaryEdgeFind && !store.propagationHasOccurred) {
        unaryRules(store, tn, tr, !doProfile);
      }

    } while (store.propagationHasOccurred);
  }

  /**
   * The time-table rule: the unary time-table for constant durations and resource uses, the general
   * profile otherwise. Both prune the same values.
   *
   * @param store the constraint store.
   */
  void unaryProfile(Store store) {
    if (cumulativeForConstants != null) {
      if (timetable == null) {
        timetable = newTimetable();
      }
      if (tasks == null) {
        initTasks(store);
      }
      if (timetable.prune(store, tasks, from)) {
        return;
      }
    }
    profileProp(store);
  }

  private UnaryTimetable newTimetable() {
    int n = taskNormal.length;
    IntVar[] starts = new IntVar[n];
    int[] durs = new int[n];
    int[] ress = new int[n];
    for (int i = 0; i < n; i++) {
      starts[i] = taskNormal[i].start;
      durs[i] = taskNormal[i].dur.value();
      ress[i] = taskNormal[i].res.value();
    }
    return new UnaryTimetable(starts, durs, ress, limit);
  }

  /**
   * A task that occupies the resource uses at most the limit, and a task that uses more than the
   * limit does not occupy it (has zero duration).
   *
   * @param store the constraint store.
   */
  void fitTasksInLimit(Store store) {
    int limitMax = limit.max();
    for (TaskView t : tvn) {
      if (t.dur.min() > 0) {
        t.res.domain.inMax(store.level, t.res, limitMax);
      } else if (t.res.min() > limitMax) {
        t.dur.domain.inMax(store.level, t.dur, 0);
      }
    }
  }

  /**
   * The overload check (optional), detectable precedences, not-last and edge finding on the normal
   * and the reversed view. Each rule sees the current bounds: the bounds are read once and again
   * only after a rule changed some of them. A rule that pruned nothing is skipped until some bound
   * changes, which saves most of the last pass that only confirms the fixpoint.
   *
   * @param store the constraint store.
   * @param tn the tasks in the normal view.
   * @param tr the same tasks in the reversed view, in the same order.
   * @param overload true to run the overload check first.
   */
  void unaryRules(Store store, TaskView[] tn, TaskView[] tr, boolean overload) {
    boolean changed = store.propagationHasOccurred;
    store.propagationHasOccurred = false;
    boolean loaded = false;
    // the time-table has just pruned nothing, so tasks left out now may stay out
    firstLoad = true;
    for (int rule = overload ? OVERLOAD : DETECTABLE_NORMAL; rule <= EDGE_FIND_REVERSED; rule++) {
      if (quietAt[rule] == boundsVersion) {
        continue;
      }
      if (!loaded) {
        loadViews(tn, tr);
        loaded = true;
      }
      if (loadedCount > 0) {
        runRule(rule, store, loadedNormal, loadedReversed, loadedCount);
      }
      if (store.propagationHasOccurred) {
        store.propagationHasOccurred = false;
        changed = true;
        loaded = false;
        boundsChanged();
      } else {
        quietAt[rule] = boundsVersion;
      }
    }
    store.propagationHasOccurred |= changed;
  }

  /**
   * Tells the rules that the bounds of the tasks may have changed since they last ran, so each of
   * them runs again. A rule is skipped only while no bound changed since it last pruned nothing.
   */
  void boundsChanged() {
    boundsVersion++;
  }

  private void runRule(int rule, Store store, TaskView[] tn, TaskView[] tr, int n) {
    switch (rule) {
      case OVERLOAD -> unaryNormal.overload(n);
      case DETECTABLE_NORMAL -> unaryNormal.detectable(tn, n, store);
      case DETECTABLE_REVERSED -> unaryReversed.detectable(tr, n, store);
      case NOT_LAST_NORMAL -> unaryNormal.notLast(tn, n, store);
      case NOT_LAST_REVERSED -> unaryReversed.notLast(tr, n, store);
      case EDGE_FIND_NORMAL -> unaryNormal.edgeFind(tn, n, store);
      default -> unaryReversed.edgeFind(tr, n, store);
    }
  }

  private void initTasks(Store store) {
    int n = tvn.length;
    tasks = new int[n];
    positionOf = new int[n];
    for (int i = 0; i < n; i++) {
      tasks[i] = i;
      positionOf[i] = i;
    }
    leftOut = new TimeStamp<>(store, 0);
  }

  // loads the bounds of the tasks into both views, leaving out the fixed tasks that end before the
  // other tasks when the time-table has checked that the compulsory parts do not overlap
  private void loadViews(TaskView[] tn, TaskView[] tr) {
    int n = tn.length;
    if (leaveOutFixedPrefix) {
      if (keptNormal.length < n) {
        keptNormal = new TaskView[n];
        keptReversed = new TaskView[n];
        leftOutTasks = new int[n];
      }
      // without trailing, tn holds the tasks that may use the resource now, in positions 0..n-1
      int[] order = trailLeftOut ? tasks : identity(n);
      loadedCount =
          unaryNormal.loadNormalActive(tn, tr, order, from, keptNormal, keptReversed, leftOutTasks);
      loadedNormal = keptNormal;
      loadedReversed = keptReversed;
      if (trailLeftOut && firstLoad) {
        leaveOut(unaryNormal.leftOutCount());
      }
    } else {
      unaryNormal.loadNormal(tn, n);
      loadedCount = n;
      loadedNormal = tn;
      loadedReversed = tr;
    }
    firstLoad = false;
    if (loadedCount > 0) {
      unaryReversed.loadReversed(unaryNormal, loadedCount);
    }
  }

  // moves the tasks just left out to the front of tasks and leaves them out in the subtree
  private void leaveOut(int count) {
    if (count == 0) {
      return;
    }
    for (int k = 0; k < count; k++) {
      int i = leftOutTasks[k];
      int p = positionOf[i];
      int j = tasks[from];
      tasks[p] = j;
      positionOf[j] = p;
      tasks[from] = i;
      positionOf[i] = from;
      from++;
    }
    leftOut.update(from);
  }

  private int[] identityOrder = new int[0];

  private int[] identity(int n) {
    if (identityOrder.length != n) {
      identityOrder = new int[n];
      for (int i = 0; i < n; i++) {
        identityOrder[i] = i;
      }
    }
    return identityOrder;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : cumulativeUnary([ ");
    for (int i = 0; i < taskNormal.length - 1; i++) {
      result.append(taskNormal[i]).append(", ");
    }

    result.append(taskNormal[taskNormal.length - 1]);

    result.append(" ]").append(", limit = ").append(limit).append(" )");

    return result.toString();
  }

  @Override
  public Optional<List<Constraint>> simplify() {
    if (getClass() != CumulativeUnary.class) {
      return Optional.empty();
    }
    return simplifyTasks(
        t ->
            withOptionsOf(
                new CumulativeUnary(t[0], t[1], t[2], limit, doProfile, doUnaryEdgeFind)));
  }

  @Override
  public CumulativeUnary copy(VarMap map) {
    IntVar[][] t = taskVariables(map);
    return withOptionsOf(
        new CumulativeUnary(t[0], t[1], t[2], map.get(limit), doProfile, doUnaryEdgeFind));
  }
}
