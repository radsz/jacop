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

    do {

      store.propagationHasOccurred = false;

      if (doProfile) {
        profileProp(store);
      }

      if (doUnaryEdgeFind && !store.propagationHasOccurred) {
        unaryRules(store, tn, tr, !doProfile);
      }

    } while (store.propagationHasOccurred);
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
   * only after a rule changed some of them.
   *
   * @param store the constraint store.
   * @param tn the tasks in the normal view.
   * @param tr the same tasks in the reversed view, in the same order.
   * @param overload true to run the overload check first.
   */
  void unaryRules(Store store, TaskView[] tn, TaskView[] tr, boolean overload) {
    int n = tn.length;
    boolean changed = store.propagationHasOccurred;
    store.propagationHasOccurred = false;
    loadViews(tn, n);
    if (overload) {
      unaryNormal.overload(n);
    }
    unaryNormal.detectable(tn, n, store);
    changed |= reloadIfChanged(store, tn, n);
    unaryReversed.detectable(tr, n, store);
    changed |= reloadIfChanged(store, tn, n);
    unaryNormal.notLast(tn, n, store);
    changed |= reloadIfChanged(store, tn, n);
    unaryReversed.notLast(tr, n, store);
    changed |= reloadIfChanged(store, tn, n);
    unaryNormal.edgeFind(tn, n, store);
    changed |= reloadIfChanged(store, tn, n);
    unaryReversed.edgeFind(tr, n, store);
    store.propagationHasOccurred |= changed;
  }

  private void loadViews(TaskView[] tn, int n) {
    unaryNormal.loadNormal(tn, n);
    unaryReversed.loadReversed(unaryNormal, n);
  }

  // reloads the bounds if the previous rule changed some, and tells whether it did
  private boolean reloadIfChanged(Store store, TaskView[] tn, int n) {
    if (!store.propagationHasOccurred) {
      return false;
    }
    store.propagationHasOccurred = false;
    loadViews(tn, n);
    return true;
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
