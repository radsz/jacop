/*
 * ProfileOptional.java
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

// import org.jacop.constraints.Constraint;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * ProfileOptional implements the cumulative profile and propagation for optional tasks.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class ProfileOptional {

  // event type
  private static final int PROFILE = 0;
  private static final int PRUNE_START = 1;
  private static final int PRUNE_END = 2;

  /*
   * All tasks of the constraint
   */
  // final TaskView[] taskNormal;
  final boolean debugNarr = false;
  final boolean debug = false;

  /** It specifies the limit of the PROFILE of cumulative use of resources. */
  private final IntVar limit;

  private final Comparator<Event> eventComparator =
      (Event o1, Event o2) -> {
        int dateDiff = o1.date() - o2.date();
        return dateDiff == 0 ? (o1.type() - o2.type()) : dateDiff;
      };
  List<Event> utilizationProfile;
  boolean existsOpt = true;

  /**
   * It creates a PROFILE for optional tasks.
   *
   * @param limit the overall limit of resources which has to be used.
   */
  public ProfileOptional(IntVar limit) {
    this.limit = limit;
  }

  void updateTasksRes(Store store, TaskView[] ts) {
    int limitMax = limit.max();
    for (TaskView t : ts) {
      t.res.domain.inMax(store.level, t.res, limitMax);
    }
  }

  TaskView[] filterOptionalTasks(TaskView[] ts, IntVar[] opt) {

    TaskView[] nonOptionalTasks = new TaskView[ts.length];
    int k = 0;

    for (int i = 0; i < ts.length; i++) {
      if (opt[i].min() != 0) {
        nonOptionalTasks[k] = ts[i];
        ts[i].index = k++;
      }
    }

    if (k == 0) {
      return null;
    }
    TaskView[] t = new TaskView[k];
    System.arraycopy(nonOptionalTasks, 0, t, 0, k);
    return t;
  }

  @Override
  public String toString() {

    return "";
  }

  int minStartOpt(TaskView[] ts, IntVar[] opt) {
    existsOpt = false;
    int min = Integer.MAX_VALUE;
    for (int i = 0; i < ts.length; i++) {

      if (min > ts[i].start().min()) {
        min = ts[i].start().min();
      }

      if (!opt[i].singleton()) {
        existsOpt = true;
      }
    }
    return min;
  }

  // Sweep algorithm for PROFILE
  void sweepPruning(Store store, TaskView[] tn, IntVar[] opt) {

    utilizationProfile = new ArrayList<>();

    TaskView[] ts = filterOptionalTasks(tn, opt);
    if (ts == null) {
      return;
    }

    final int optMin = minStartOpt(tn, opt);

    // Initialize utilizationProfile for optional tasks
    int[] profilePointer = new int[1];
    if (existsOpt) {
      utilizationProfile.add(new Event(PROFILE, null, optMin, 0));
    }

    // Profile update callback for building utilizationProfile
    CumulativeBasic.ProfileUpdateCallback<Event> profileUpdateCallback =
        existsOpt
            ? (event, currentProfile) -> {
              Event ce = utilizationProfile.get(profilePointer[0]);
              int eventDate = event.date();
              int eventValue = event.value();
              if (ce.date() == eventDate) {
                ce.value += eventValue;
                if (ce.date() > 0
                    && profilePointer[0] > 0
                    && ce.value == utilizationProfile.get(profilePointer[0] - 1).value()) {
                  utilizationProfile.remove(profilePointer[0]--);
                }
              } else {
                utilizationProfile.add(
                    new Event(PROFILE, null, eventDate, ce.value() + eventValue));
                profilePointer[0]++;
              }
            }
            : null;

    // Post-process callback for pruneOpt
    Runnable postProcessCallback = existsOpt ? () -> pruneOpt(store, tn, opt) : null;

    CumulativeBasic.sweepPruningCore(
        store,
        ts,
        limit,
        debug,
        debugNarr,
        (type, t, date, value) -> new Event(type, t, date, value),
        eventComparator,
        profileUpdateCallback,
        postProcessCallback);
  }

  void pruneOpt(Store store, TaskView[] tn, IntVar[] opt) {

    for (int i = 0; i < tn.length; i++) {
      pruneTaskIfInfeasible(store, tn, opt, i);
    }
  }

  /**
   * Prunes opt[i] to 0 if the optional task i cannot be present (infeasible w.r.t. profile).
   *
   * @param store the store
   * @param tn task views
   * @param opt optional task variables
   * @param i task index
   */
  private void pruneTaskIfInfeasible(Store store, TaskView[] tn, IntVar[] opt, int i) {
    if (opt[i].singleton()) {
      return;
    }

    int limit = this.limit.max();
    int n = utilizationProfile.size();
    int dur = tn[i].dur().min();
    int res = tn[i].res().min();
    int sMin = tn[i].start().min();
    int sMax = tn[i].start().max();

    boolean ok = false;
    for (int j = 0; j < n; j++) {
      Event e = utilizationProfile.get(j);
      int t = e.date();
      int u = e.value();

      if (sMin + dur <= t) {
        ok = true;
        break;
      }
      if (u + res > limit && j + 1 < n) {
        sMin = utilizationProfile.get(j + 1).date();
        if (sMin > sMax) {
          opt[i].domain.in(store.level, opt[i], 0, 0);
          return;
        }
      }
    }
    if (sMax > utilizationProfile.get(n - 1).date()) {
      return;
    }

    if (!ok) {
      opt[i].domain.in(store.level, opt[i], 0, 0);
    }
  }

  private static class Event {
    final int type;
    final TaskView t;
    final int date;
    int value;

    Event(int type, TaskView t, int date, int value) {
      this.type = type;
      this.t = t;
      this.date = date;
      this.value = value;
    }

    int date() {
      return date;
    }

    int type() {
      return type;
    }

    int value() {
      return value;
    }

    TaskView task() {
      return t;
    }

    @Override
    public String toString() {
      String result = "(";
      result +=
          type == PROFILE ? "PROFILE, " : type == PRUNE_START ? "PRUNE_START, " : "PRUNE_END, ";
      result += t + ", " + date + ", " + value + ")";
      return result;
    }
  }
}
