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

import java.util.Arrays;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * The time-table rule of {@link CumulativeUnary} for tasks with constant durations. It prunes the
 * same values as the sweep of {@link CumulativePrimary} for constant resource uses, and as the
 * sweep of {@link CumulativeBasic} for variable ones, using that no two tasks fit under the limit
 * together: the compulsory parts of the tasks that use the resource must be disjoint, a task that
 * uses the resource cannot run over the compulsory part of another task, and a task that may use
 * nothing uses nothing if its compulsory part overlaps that of another task.
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
  // the resource uses when they are variables, or null; a task then counts at its smallest use
  private final IntVar[] use;
  private final IntVar limit;
  private final int maxRes;

  // the tasks under pruning in the order of their latest start, kept between calls
  private final long[] lstKeys;
  private int keyCount;
  // marks the tasks under pruning and the tasks in lstKeys in one call
  private final int[] active;
  private final int[] keyed;
  private int stamp;
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
    this(start, dur, res, null, limit);
  }

  /**
   * Creates the rule for variable resource uses.
   *
   * @param start the start variables of the tasks.
   * @param dur the durations of the tasks.
   * @param use the resource use variables of the tasks.
   * @param limit the resource limit.
   */
  UnaryTimetable(IntVar[] start, int[] dur, IntVar[] use, IntVar limit) {
    this(start, dur, null, use, limit);
  }

  private UnaryTimetable(IntVar[] start, int[] dur, int[] res, IntVar[] use, IntVar limit) {
    this.start = start;
    this.dur = dur;
    this.res = res;
    this.use = use;
    this.limit = limit;
    int n = start.length;
    int max = 0;
    for (int i = 0; res != null && i < n; i++) {
      if (dur[i] > 0) {
        max = Math.max(max, res[i]);
      }
    }
    maxRes = max;
    lstKeys = new long[n];
    active = new int[n];
    keyed = new int[n];
    partTask = new int[n];
    partStart = new int[n];
    partEnd = new int[n];
  }

  /**
   * Prunes the starts of the tasks and the limit against the compulsory parts.
   *
   * @param store the store.
   * @param tasks the indices of the tasks that are pruned and make the profile; the other tasks are
   *     fixed tasks that end before all of them start.
   * @param count the number of these tasks.
   * @return false if the resource is not unary for the current limit, and nothing was pruned.
   */
  boolean prune(Store store, int[] tasks, int count) {
    int limitMax = limit.max();
    if (use != null) {
      fitUses(store, limitMax);
    } else if (maxRes > limitMax) {
      // a task that does not fit under the limit overloads the resource wherever it runs
      return false;
    }
    int parts = sortParts(tasks, count);
    if (parts == 0) {
      return true;
    }
    int height = 0;
    for (int p = 0; p < parts; p++) {
      int r = minUse(partTask[p]);
      if (p > 0 && partStart[p] < partEnd[p - 1]) {
        if (r + minUse(partTask[p - 1]) <= limitMax) {
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
    for (int m = 0; m < keyCount; m++) {
      int i = (int) lstKeys[m];
      IntVar s = start[i];
      int est = s.min();
      int lct = s.max() + dur[i];
      if (est > last || lct < first) {
        continue;
      }
      if (minUse(i) > 0) {
        if (!s.singleton()) {
          pruneTask(store, i, est, lct, parts);
        }
      } else if (use[i].max() > 0 && s.max() < est + dur[i]) {
        pruneUse(store, i, s.max(), est + dur[i], parts, limitMax);
      }
    }
    return true;
  }

  private int minUse(int i) {
    return use == null ? res[i] : use[i].min();
  }

  private int maxUse(int i) {
    return use == null ? res[i] : use[i].max();
  }

  // a task that runs uses at most the limit, and the limit is at least the smallest use of a task
  // with a compulsory part; this covers the fixed tasks left out of the pruning too, since their
  // uses may still change
  private void fitUses(Store store, int limitMax) {
    int most = 0;
    for (int i = 0; i < use.length; i++) {
      if (dur[i] > 0) {
        if (use[i].max() > limitMax) {
          use[i].domain.inMax(store.level, use[i], limitMax);
        }
        if (start[i].max() < start[i].min() + dur[i]) {
          most = Math.max(most, use[i].min());
        }
      }
    }
    if (most > limit.min()) {
      limit.domain.inMin(store.level, limit, most);
    }
  }

  // the first compulsory part that ends after date
  private int firstPartAfter(int date, int parts) {
    int lo = 0;
    int hi = parts;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (partEnd[mid] > date) {
        hi = mid;
      } else {
        lo = mid + 1;
      }
    }
    return lo;
  }

  // task i may use nothing; over the compulsory parts of other tasks its use leaves room for theirs
  private void pruneUse(Store store, int i, int lst, int ect, int parts, int limitMax) {
    int most = 0;
    for (int p = firstPartAfter(lst, parts); p < parts && partStart[p] < ect; p++) {
      most = Math.max(most, minUse(partTask[p]));
    }
    if (most > 0) {
      use[i].domain.inMax(store.level, use[i], limitMax - most);
    }
  }

  private void nextStamp() {
    if (stamp == Integer.MAX_VALUE) {
      Arrays.fill(active, 0);
      Arrays.fill(keyed, 0);
      stamp = 0;
    }
    stamp++;
  }

  // sorts the tasks under pruning by latest start, starting from the order of the previous call,
  // and keeps those with a compulsory part; returns their number
  private int sortParts(int[] tasks, int n) {
    nextStamp();
    for (int q = 0; q < n; q++) {
      active[tasks[q]] = stamp;
    }
    long[] k = lstKeys;
    int count = 0;
    for (int m = 0; m < keyCount; m++) {
      int i = (int) k[m];
      if (active[i] == stamp) {
        k[count++] = i;
        keyed[i] = stamp;
      }
    }
    for (int q = 0; q < n; q++) {
      int i = tasks[q];
      if (keyed[i] != stamp && dur[i] > 0 && maxUse(i) > 0) {
        k[count++] = i;
      }
    }
    keyCount = count;
    for (int m = 0; m < count; m++) {
      int i = (int) k[m];
      k[m] = ((long) start[i].max() << 32) | i;
    }
    for (int a = 1; a < count; a++) {
      long x = k[a];
      int b = a - 1;
      while (b >= 0 && k[b] > x) {
        k[b + 1] = k[b];
        b--;
      }
      k[b + 1] = x;
    }
    int parts = 0;
    for (int m = 0; m < count; m++) {
      int i = (int) k[m];
      int lst = (int) (k[m] >> 32);
      int ect = start[i].min() + dur[i];
      if (lst < ect && minUse(i) > 0) {
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
    IntVar s = start[i];
    int d = dur[i];
    int p = firstPartAfter(est, parts);
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
        if (use == null) {
          s.domain.inComplement(store.level, s, excluded, to - 1);
        } else {
          // as the sweep of CumulativeBasic, which leaves out the holes under lazy clause
          // generation
          TimetableSweep.removeStarts(store, s, excluded, to - 1);
        }
      } else {
        s.domain.inMax(store.level, s, excluded - 1);
      }
    }
  }
}
