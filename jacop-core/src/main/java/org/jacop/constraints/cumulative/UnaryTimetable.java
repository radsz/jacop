/*
 * UnaryTimetable.java
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

import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * The time-table rule of {@link CumulativeUnary} for tasks with constant durations and resource
 * uses. It prunes the same values as the sweep of {@link CumulativePrimary}, using that no two
 * tasks fit under the limit together: the compulsory parts of the tasks must be disjoint, and a
 * task cannot run over the compulsory part of another task.
 *
 * <p>The compulsory parts are sorted by their start, and each task removes from its start domain
 * the starts that overlap a block of compulsory parts of other tasks that follow each other without
 * a gap, one block at a time as the sweep does. The sweep sorts four events per task and visits
 * every task under pruning at each change of the profile; here a task visits only the blocks within
 * its window. This follows the time-tabling of Fahimi, Ouellet and Quimper, "Linear-time filtering
 * algorithms for the disjunctive constraint and a quadratic filtering algorithm for the cumulative
 * not-first not-last", Constraints 23(3), 2018, but it keeps the holes the sweep makes in the start
 * domains, where the paper changes only the earliest start.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
final class UnaryTimetable {

  private final IntVar[] start;
  private final int[] dur;
  private final int[] res;
  private final IntVar limit;

  // the tasks that use the resource (positive duration and resource use)
  private final int[] used;
  // the tasks of used in the order of their latest start, kept between calls
  private final long[] lstKeys;
  // the compulsory parts in the order of their start: task, start and end
  private final int[] partTask;
  private final int[] partStart;
  private final int[] partEnd;

  /**
   * Creates the rule.
   *
   * @param start the start variables of the tasks.
   * @param dur the durations of the tasks.
   * @param res the resource uses of the tasks.
   * @param limit the resource limit.
   */
  UnaryTimetable(IntVar[] start, int[] dur, int[] res, IntVar limit) {
    this.start = start;
    this.dur = dur;
    this.res = res;
    this.limit = limit;
    int n = 0;
    for (int i = 0; i < start.length; i++) {
      if (dur[i] > 0 && res[i] > 0) {
        n++;
      }
    }
    used = new int[n];
    n = 0;
    for (int i = 0; i < start.length; i++) {
      if (dur[i] > 0 && res[i] > 0) {
        used[n++] = i;
      }
    }
    lstKeys = new long[n];
    for (int m = 0; m < n; m++) {
      lstKeys[m] = used[m];
    }
    partTask = new int[n];
    partStart = new int[n];
    partEnd = new int[n];
  }

  /**
   * Prunes the starts of the tasks and the limit against the compulsory parts.
   *
   * @param store the store.
   * @return false if the resource is not unary for the current limit, and nothing was pruned.
   */
  boolean prune(Store store) {
    int limitMax = limit.max();
    for (int i : used) {
      if (res[i] > limitMax) {
        // a task that does not fit under the limit overloads the resource wherever it runs
        return false;
      }
    }
    int parts = sortParts();
    if (parts == 0) {
      return true;
    }
    int height = 0;
    for (int p = 0; p < parts; p++) {
      int r = res[partTask[p]];
      if (p > 0 && partStart[p] < partEnd[p - 1]) {
        if (r + res[partTask[p - 1]] <= limitMax) {
          return false;
        }
        // two compulsory parts overlap
        throw Store.failException;
      }
      height = Math.max(height, r);
    }
    if (height > limit.min()) {
      limit.domain.inMin(store.level, limit, height);
    }
    int first = partStart[0];
    int last = partEnd[parts - 1];
    for (int i : used) {
      IntVar s = start[i];
      if (!s.singleton()) {
        int est = s.min();
        int lct = s.max() + dur[i];
        if (est <= last && lct >= first) {
          pruneTask(store, i, est, lct, parts);
        }
      }
    }
    return true;
  }

  // sorts the tasks by latest start and keeps those with a compulsory part; returns their number
  private int sortParts() {
    int n = used.length;
    long[] k = lstKeys;
    for (int m = 0; m < n; m++) {
      int i = (int) k[m];
      k[m] = ((long) start[i].max() << 32) | i;
    }
    for (int a = 1; a < n; a++) {
      long x = k[a];
      int b = a - 1;
      while (b >= 0 && k[b] > x) {
        k[b + 1] = k[b];
        b--;
      }
      k[b + 1] = x;
    }
    int parts = 0;
    for (int m = 0; m < n; m++) {
      int i = (int) k[m];
      int lst = (int) (k[m] >> 32);
      int ect = start[i].min() + dur[i];
      if (lst < ect) {
        partTask[parts] = i;
        partStart[parts] = lst;
        partEnd[parts] = ect;
        parts++;
      }
    }
    return parts;
  }

  // removes the starts of task i that overlap the blocks of compulsory parts of the other tasks
  private void pruneTask(Store store, int i, int est, int lct, int parts) {
    // the first part that ends after est
    int lo = 0;
    int hi = parts;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (partEnd[mid] > est) {
        hi = mid;
      } else {
        lo = mid + 1;
      }
    }
    IntVar s = start[i];
    int d = dur[i];
    int p = lo;
    while (p < parts && partStart[p] < lct) {
      if (partTask[p] == i) {
        p++;
        continue;
      }
      int from = partStart[p];
      int to = partEnd[p];
      p++;
      // a block: parts of other tasks, each starting where the previous one ends
      while (p < parts && partStart[p] == to && partTask[p] != i) {
        to = partEnd[p];
        p++;
      }
      int excluded = from <= est ? est : from - d + 1;
      if (to <= lct) {
        s.domain.inComplement(store.level, s, excluded, to - 1);
      } else {
        s.domain.inMax(store.level, s, excluded - 1);
      }
    }
  }
}
