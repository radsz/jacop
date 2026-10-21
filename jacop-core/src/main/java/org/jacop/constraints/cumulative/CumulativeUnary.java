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
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * CumulativeUnary implements the scheduling constraint for unary resources using.
 *
 * <p>overload, not-first-not-last and detectable algorithms based on
 *
 * <p>Petr Vilim, "O(n log n) Filtering Algorithms for Unary Resource Constraints", Proceedings of
 * CP-AI-OR 2004,
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
    this(
        starts,
        durations,
        resources,
        limit,
        starts.length > getEdgeFindLimit(),
        starts.length <= getEdgeFindLimit());
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
    this(
        starts,
        durations,
        resources,
        limit,
        starts.length <= getEdgeFindLimit() ? doProfile : true,
        starts.length <= getEdgeFindLimit());
  }

  private static int getEdgeFindLimit() {
    String s = System.getProperty("max_edge_find_size");
    return s != null ? Integer.parseInt(s) : 100;
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

  @Override
  public void consistency(Store store) {

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

        if (!doProfile) {
          overload(tn);
        }
        detectable(store, tn, tr);
        notFirstNotLast(store, tn, tr);
        edgeFind(store, tn, tr);
      }

    } while (store.propagationHasOccurred);
  }

  void overload(TaskView[] ts) {
    unaryNormal.load(ts, ts.length);
    unaryNormal.overload(ts.length);
  }

  void notFirstNotLast(Store store, TaskView[] tn, TaskView[] tr) {
    unaryNormal.load(tn, tn.length);
    unaryNormal.notLast(tn, tn.length, store);
    unaryReversed.load(tr, tr.length);
    unaryReversed.notLast(tr, tr.length, store);
  }

  void detectable(Store store, TaskView[] tn, TaskView[] tr) {
    unaryNormal.load(tn, tn.length);
    unaryNormal.detectable(tn, tn.length, store);
    unaryReversed.load(tr, tr.length);
    unaryReversed.detectable(tr, tr.length, store);
  }

  void edgeFind(Store store, TaskView[] tn, TaskView[] tr) {
    unaryNormal.load(tn, tn.length);
    unaryNormal.edgeFind(tn, tn.length, store);
    unaryReversed.load(tr, tr.length);
    unaryReversed.edgeFind(tr, tr.length, store);
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
}
