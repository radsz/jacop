/*
 * UnaryExplanation.java
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
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explains the bounds the unary rules of {@link CumulativeUnary} give a start time by a set of
 * tasks that must all run before the task (for a lower bound; after it for an upper bound), as the
 * rules found them (Vilím, "Filtering algorithms for the unary resource constraint", 2008; Schutt,
 * "Improving scheduling by learning", 2011, chapter 5):
 *
 * <ul>
 *   <li>detectable precedences: each task k whose latest start is below the earliest end of task j
 *       runs before j;
 *   <li>edge finding: tasks Ω inside a window [c, b] that j, also starting from c, cannot end
 *       within, because c + p(Ω) + p(j) &gt; b, all run before j;
 *   <li>not-first: tasks Ω that end by b, with c + p(j) + p(Ω) &gt; b for the start c of j, cannot
 *       all run after j, so one of them runs before it.
 * </ul>
 *
 * The bound then follows from the earliest end of the tasks before j: a + p of those that start
 * from a, or for not-first the smallest earliest end among Ω. The time-table and energy
 * explanations of {@link CumulativeBasic} cannot derive detectable precedences at all, and give
 * edge finding one window per start value; the generic reason then cites every bound of the
 * resource.
 *
 * <p>Each bound is lifted to the weakest atom on the trail that keeps the rule's condition: the
 * tasks before j need only their earliest start a and a latest end that keeps the precedence, and j
 * only the start its condition needs. Upper bounds are explained in the reversed time line, where
 * they are lower bounds. Only tasks of constant duration take part, and only when every two of them
 * exceed the limit together, so that they cannot overlap.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class UnaryExplanation {

  private final TaskView[] tasks;
  private final IntVar limit;

  // the tasks in the time line of the explanation (reversed for an upper bound), just before the
  // explained entry: earliest start, latest end, duration
  private int[] est = new int[0];
  private int[] lct = new int[0];
  private int[] dur = new int[0];
  private boolean[] usable = new boolean[0];
  private int[] order = new int[0];
  private int[] ends = new int[0];
  private int[] window = new int[0];
  private int[] picked = new int[0];
  private int numPicked;
  // the tasks of the best explanation found so far, its kind and parameters
  private int[] best = new int[0];
  private int numBest;
  private int bestKind;
  private long bestA;
  private long bestC;
  private long bestB;
  private long bestV;

  private static final int DETECTABLE = 0;
  private static final int EDGE_FINDING = 1;
  private static final int NOT_FIRST = 2;

  UnaryExplanation(TaskView[] tasks, IntVar limit) {
    this.tasks = tasks.clone();
    this.limit = limit;
  }

  /**
   * Explains a bound of the start of one of the tasks.
   *
   * @param trail the trail
   * @param entry the entry of a lower or upper bound atom of a start time
   * @param out where the reason is added
   * @return false when no rule explains it; out may then hold entries to drop
   */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    boolean lower = trail.kind(entry) == AtomicTrail.GE;
    int n = tasks.length;
    int j = -1;
    for (int i = 0; i < n; i++) {
      if (tasks[i].start == y) {
        if (j >= 0) {
          return false;
        }
        j = i;
      }
    }
    if (j < 0 || !load(trail, entry, j, lower)) {
      return false;
    }
    int pj = dur[j];
    // the bound in the time line of the explanation: j starts at v or later
    long v = lower ? trail.value(entry) : -((long) trail.value(entry) + pj);
    numBest = Integer.MAX_VALUE;
    bestV = v;
    detectable(j, v);
    edgeFinding(j, v);
    notFirst(j, v);
    if (numBest == Integer.MAX_VALUE) {
      return false;
    }
    cite(trail, entry, j, lower, out);
    return true;
  }

  /**
   * Explains a failure of the resource by a task that a rule pushes past its latest start (or, in
   * the reversed time line, before its earliest start): the rule's reason and that bound.
   *
   * @param trail the trail
   * @param out where the reason is added
   * @return false when no rule explains a failure; out may then hold entries to drop
   */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    int position = trail.size();
    for (int j = 0; j < tasks.length; j++) {
      for (boolean lower : new boolean[] {true, false}) {
        if (!load(trail, position, j, lower)) {
          continue;
        }
        // j would start after its latest start in this time line
        long last = (long) lct[j] - dur[j];
        long v = last + 1;
        numBest = Integer.MAX_VALUE;
        bestV = v;
        detectable(j, v);
        edgeFinding(j, v);
        notFirst(j, v);
        if (numBest != Integer.MAX_VALUE) {
          cite(trail, position, j, lower, out);
          startAtMost(trail, position, j, lower, last, out);
          return true;
        }
      }
    }
    return false;
  }

  // reads the tasks just before the entry; false when j or the limit do not allow the rules
  private boolean load(AtomicTrail trail, int entry, int j, boolean lower) {
    int n = tasks.length;
    if (est.length < n) {
      est = new int[n];
      lct = new int[n];
      dur = new int[n];
      usable = new boolean[n];
      order = new int[n];
      ends = new int[n];
      window = new int[n];
      picked = new int[n];
      best = new int[n];
    }
    long limitMax = trail.maxBefore(limit, entry);
    long smallest = Long.MAX_VALUE;
    for (int i = 0; i < n; i++) {
      TaskView t = tasks[i];
      // the durations are constant
      int d = t.dur.min();
      int r = trail.minBefore(t.res, entry);
      usable[i] = d > 0 && r > 0;
      if (!usable[i]) {
        if (i == j) {
          return false;
        }
        continue;
      }
      smallest = Math.min(smallest, r);
      dur[i] = d;
      int s = trail.minBefore(t.start, entry);
      int e = trail.maxBefore(t.start, entry) + d;
      est[i] = lower ? s : -e;
      lct[i] = lower ? e : -s;
    }
    // any two tasks exceed the limit together, so no two of them overlap
    return 2 * smallest > limitMax;
  }

  // keeps the tasks picked as the best explanation when they are fewer
  private void keep(int kind, long a, long c, long b) {
    if (numPicked < numBest) {
      System.arraycopy(picked, 0, best, 0, numPicked);
      numBest = numPicked;
      bestKind = kind;
      bestA = a;
      bestC = c;
      bestB = b;
    }
  }

  /**
   * Detectable precedences: the tasks whose latest start is below the earliest end of j run before
   * it; among them, those starting from a with the largest durations until a + their durations
   * reaches v.
   */
  private void detectable(int j, long v) {
    long ectJ = (long) est[j] + dur[j];
    int m = 0;
    for (int k = 0; k < tasks.length; k++) {
      if (k != j && usable[k] && (long) lct[k] - dur[k] < ectJ) {
        order[m++] = k;
      }
    }
    pickBefore(m, v);
    if (numPicked > 0) {
      long c = Long.MIN_VALUE;
      for (int q = 0; q < numPicked; q++) {
        int k = picked[q];
        c = Math.max(c, (long) lct[k] - dur[k] - dur[j] + 1);
      }
      keep(DETECTABLE, pickedA, c, 0);
    }
  }

  private long pickedA;

  /**
   * Picks from order[0, m) the fewest tasks that start from some a with a + their durations at
   * least v: for each a, the largest durations first. numPicked is 0 when there are none.
   */
  private void pickBefore(int m, long v) {
    numPicked = 0;
    sortBy(order, m, est, true);
    // the largest a with enough duration from it, by a sweep from the latest start down
    long sum = 0;
    int from = -1;
    for (int q = 0; q < m; q++) {
      sum += dur[order[q]];
      if (q + 1 < m && est[order[q + 1]] == est[order[q]]) {
        continue;
      }
      if (est[order[q]] + sum >= v) {
        from = q;
        break;
      }
    }
    if (from < 0) {
      return;
    }
    long a = est[order[from]];
    int count = from + 1;
    // the largest durations first
    sortBy(order, count, dur, true);
    long need = v - a;
    long got = 0;
    for (int q = 0; q < count && got < need; q++) {
      picked[numPicked++] = order[q];
      got += dur[order[q]];
    }
    pickedA = a;
  }

  /**
   * Edge finding: for each window end b, the tasks that end by b and start from a, with a as low as
   * c + p(Ω) + p(j) &gt; b still holds for c = min(a, est(j)); the bound is the earliest end of Ω.
   */
  private void edgeFinding(int j, long v) {
    int n = tasks.length;
    int m = 0;
    for (int k = 0; k < n; k++) {
      if (k != j && usable[k]) {
        ends[m++] = k;
      }
    }
    // the tasks by decreasing earliest start, and the window ends in increasing order
    System.arraycopy(ends, 0, window, 0, m);
    sortBy(window, m, est, true);
    sortBy(ends, m, lct, false);
    for (int e = 0; e < m; e++) {
      if (e + 1 < m && lct[ends[e + 1]] == lct[ends[e]]) {
        continue;
      }
      long b = lct[ends[e]];
      int w = 0;
      for (int q = 0; q < m; q++) {
        if (lct[window[q]] <= b) {
          order[w++] = window[q];
        }
      }
      long p = 0;
      long ect = Long.MIN_VALUE;
      long ectA = 0;
      for (int q = 0; q < w; q++) {
        p += dur[order[q]];
        if (q + 1 < w && est[order[q + 1]] == est[order[q]]) {
          continue;
        }
        long a = est[order[q]];
        if (a + p > ect) {
          ect = a + p;
          ectA = a;
        }
        long c = b - p - dur[j] + 1;
        if (c <= Math.min(a, est[j]) && ect >= v && q + 1 < numBest) {
          numPicked = 0;
          for (int r = 0; r <= q; r++) {
            picked[numPicked++] = order[r];
          }
          keep(EDGE_FINDING, ectA, c, b);
          break;
        }
      }
    }
  }

  /**
   * Not-first: for each window end b, the tasks that end by b and whose earliest end reaches v
   * cannot all run after j when c + p(j) + p(Ω) &gt; b for c = est(j); one of them runs first.
   */
  private void notFirst(int j, long v) {
    int n = tasks.length;
    int m = 0;
    for (int k = 0; k < n; k++) {
      if (k != j && usable[k] && (long) est[k] + dur[k] >= v) {
        order[m++] = k;
      }
    }
    sortBy(order, m, lct, false);
    long p = 0;
    for (int q = 0; q < m; q++) {
      p += dur[order[q]];
      if (q + 1 < m && lct[order[q + 1]] == lct[order[q]]) {
        continue;
      }
      long b = lct[order[q]];
      long c = b - p - dur[j] + 1;
      if (c <= est[j]) {
        if (q + 1 < numBest) {
          numPicked = 0;
          for (int r = 0; r <= q; r++) {
            picked[numPicked++] = order[r];
          }
          keep(NOT_FIRST, 0, c, b);
        }
        return;
      }
    }
  }

  // adds the reason of the best explanation, its bounds mapped back from the reversed time line
  private void cite(AtomicTrail trail, int entry, int j, boolean lower, EntryList out) {
    int pj = dur[j];
    long cj = startAtLeast(trail, entry, j, lower, bestC, out);
    for (int q = 0; q < numBest; q++) {
      int k = best[q];
      switch (bestKind) {
        case DETECTABLE -> {
          startAtLeast(trail, entry, k, lower, bestA, out);
          startAtMost(trail, entry, k, lower, cj + pj - 1, out);
        }
        case EDGE_FINDING -> {
          startAtLeast(trail, entry, k, lower, est[k] >= bestA ? bestA : bestC, out);
          startAtMost(trail, entry, k, lower, bestB - dur[k], out);
        }
        default -> {
          startAtLeast(trail, entry, k, lower, bestV - dur[k], out);
          startAtMost(trail, entry, k, lower, bestB - dur[k], out);
        }
      }
      trail.addLowerBound(tasks[k].res, entry, out);
    }
    trail.addLowerBound(tasks[j].res, entry, out);
    trail.addUpperBound(limit, entry, out);
  }

  // cites start(i) >= x in the time line of the explanation; returns the start cited there
  private long startAtLeast(
      AtomicTrail trail, int entry, int i, boolean lower, long x, EntryList out) {
    IntVar s = tasks[i].start;
    if (lower) {
      return trail.addBoundReaching(s, entry, true, x, out);
    }
    // reversed: -(s + d) >= x, so s <= -x - d
    return -((long) trail.addBoundReaching(s, entry, false, -x - dur[i], out) + dur[i]);
  }

  // cites start(i) <= x in the time line of the explanation
  private void startAtMost(
      AtomicTrail trail, int entry, int i, boolean lower, long x, EntryList out) {
    IntVar s = tasks[i].start;
    if (lower) {
      trail.addBoundReaching(s, entry, false, x, out);
    } else {
      // reversed: -(s + d) <= x, so s >= -x - d
      trail.addBoundReaching(s, entry, true, -x - dur[i], out);
    }
  }

  // insertion sort of order[0, m) by key, descending or ascending
  private static void sortBy(int[] order, int m, int[] key, boolean descending) {
    for (int a = 1; a < m; a++) {
      int x = order[a];
      int b = a - 1;
      while (b >= 0 && (descending ? key[order[b]] < key[x] : key[order[b]] > key[x])) {
        order[b + 1] = order[b];
        b--;
      }
      order[b + 1] = x;
    }
  }
}
