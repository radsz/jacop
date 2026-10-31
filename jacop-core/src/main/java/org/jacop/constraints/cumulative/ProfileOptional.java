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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * ProfileOptional implements the cumulative profile and propagation for optional tasks.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ProfileOptional {

  // event type
  private static final int PROFILE = 0;
  private static final int PRUNE_START = 1;
  private static final int PRUNE_END = 2;

  /*
   * All tasks of the constraint
   */
  final boolean debugNarr = false;
  final boolean debug = false;

  /** It specifies the limit of the PROFILE of cumulative use of resources. */
  private final IntVar limit;

  private final TimetableSweep sweep = new TimetableSweep();
  List<Event> utilizationProfile;
  boolean existsOpt = true;

  /**
   * Checks the variables that tell whether the optional tasks are present: one 0/1 variable per
   * task.
   *
   * @param opt the variables telling whether the tasks are present.
   * @param tasks the number of tasks.
   * @param constraintName the name of the constraint, used in error messages.
   * @return a copy of opt.
   */
  static IntVar[] checkOptional(IntVar[] opt, int tasks, String constraintName) {
    if (opt == null) {
      throw new IllegalArgumentException(constraintName + ": opt is null");
    }
    if (opt.length != tasks) {
      throw new IllegalArgumentException(
          constraintName + ": opt has " + opt.length + " variables for " + tasks + " tasks");
    }
    for (IntVar o : opt) {
      if (o == null) {
        throw new IllegalArgumentException(constraintName + ": opt contains null");
      }
      if (o.min() < 0 || o.max() > 1) {
        throw new IllegalArgumentException(
            constraintName + ": variable " + o + " of opt must have a domain within 0..1");
      }
    }
    return Arrays.copyOf(opt, opt.length);
  }

  /**
   * It creates a PROFILE for optional tasks.
   *
   * @param limit the overall limit of resources which has to be used.
   */
  public ProfileOptional(IntVar limit) {
    this.limit = limit;
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
    TimetableSweep.ProfileListener profileUpdateCallback =
        existsOpt
            ? (eventDate, eventValue) -> {
              Event ce = utilizationProfile.get(profilePointer[0]);
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

    sweep.prune(store, ts, limit, debug, debugNarr, profileUpdateCallback, postProcessCallback);
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
    // a task that may have zero duration or zero resource use can be present without using the
    // resource
    if (opt[i].singleton() || tn[i].dur().min() == 0 || tn[i].res().min() == 0) {
      return;
    }

    int limitMax = this.limit.max();
    int n = utilizationProfile.size();
    int dur = tn[i].dur().min();
    int res = tn[i].res().min();
    int sMin = tn[i].start().min();
    int sMax = tn[i].start().max();

    // Segment j of the profile has usage value() from date() until the next date (the last one
    // is unbounded). Find the earliest start from sMin at which the task does not overload any
    // segment it overlaps.
    for (int j = 0; j < n; j++) {
      Event e = utilizationProfile.get(j);
      if (sMin + dur <= e.date()) {
        return;
      }
      boolean last = j + 1 == n;
      int next = last ? Integer.MAX_VALUE : utilizationProfile.get(j + 1).date();
      if (next > sMin && e.value() + res > limitMax) {
        if (last || next > sMax) {
          opt[i].domain.in(store.level, opt[i], 0, 0);
          return;
        }
        sMin = next;
      }
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
