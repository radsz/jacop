/*
 * UnaryReasoning.java
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
import org.jacop.core.Store;

/**
 * Filtering rules of the unary resource (disjunctive) constraint on one view (normal or reversed)
 * of the tasks, after Vilím, "O(n log n) Filtering Algorithms for Unary Resource Constraint",
 * CPAIOR 2004, and Vilím, Barták and Čepek, "Unary Resource Constraint with Optional Activities",
 * CP 2004: the overload check, detectable precedences, not-last and edge finding.
 *
 * <p>The overload check and detectable precedences run in linear time after sorting on the time
 * line of Fahimi, Ouellet and Quimper, "Linear-time filtering algorithms for the disjunctive
 * constraint and a quadratic filtering algorithm for the cumulative not-first not-last",
 * Constraints 23(3), 2018: a union-find over the intervals between the distinct earliest start
 * times, which schedules tasks preemptively from their earliest start. Not-last uses the Theta tree
 * and edge finding the Theta-Lambda tree.
 *
 * <p>It works on primitive arrays reused between calls, and keeps the task orders of the previous
 * call, which it re-sorts by insertion since bounds change little between calls. One instance
 * serves one view.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class UnaryReasoning {

  private static final int NONE = Integer.MIN_VALUE;

  // the empty value in the trees: far below any time, and adding durations to it, or one empty
  // value to another, still leaves it far below any time without overflow
  private static final long EMPTY = Long.MIN_VALUE / 4;

  // task data, indexed by the position of the task in the view array
  private int[] est = new int[0];
  private int[] lct = new int[0];
  private int[] lst = new int[0];
  private int[] ect = new int[0];
  private int[] dur = new int[0];
  private int[] negLct = new int[0];
  private int[] negEst = new int[0];
  private int[] update = new int[0];

  // orders kept between calls
  private int[] estOrder = new int[0];
  private int[] lctOrder = new int[0];
  private int[] lstOrder = new int[0];
  private int[] ectOrder = new int[0];
  private int[] decLctOrder = new int[0];
  private int ordered = -1;
  private long[] sortKeys = new long[0];

  // Theta-Lambda tree with leaves in est order; root at 1, leaves at size + rank
  private int size;
  private int[] leafOf = new int[0];
  private int[] taskOfLeaf = new int[0];
  private long[] treeP = new long[0];
  private long[] treeEct = new long[0];
  private long[] treePLambda = new long[0];
  private long[] treeEctLambda = new long[0];
  private int[] responsibleP = new int[0];
  private int[] responsibleEct = new int[0];

  // time line: point a stands for the interval [time[a], time[a + 1]) with cap[a] time units free;
  // next is a union-find whose root of a is the first point from a with free time
  private long[] time = new long[0];
  private long[] cap = new long[0];
  private int[] next = new int[0];
  private int[] pointOf = new int[0];
  private int lastPoint;

  // detectable precedences: the state of each task and the tasks postponed behind a blocking task
  private static final int WAITING = 0;
  private static final int FILTERED = 1;
  private static final int POSTPONED = 2;
  private int[] state = new int[0];
  private int[] postponed = new int[0];

  private void ensureCapacity(int n) {
    if (est.length >= n) {
      return;
    }
    est = new int[n];
    lct = new int[n];
    lst = new int[n];
    ect = new int[n];
    dur = new int[n];
    negLct = new int[n];
    negEst = new int[n];
    update = new int[n];
    estOrder = new int[n];
    lctOrder = new int[n];
    lstOrder = new int[n];
    ectOrder = new int[n];
    decLctOrder = new int[n];
    sortKeys = new long[n];
    ordered = -1;
    int s = 1;
    while (s < n) {
      s <<= 1;
    }
    leafOf = new int[n];
    taskOfLeaf = new int[2 * s];
    treeP = new long[2 * s];
    treeEct = new long[2 * s];
    treePLambda = new long[2 * s];
    treeEctLambda = new long[2 * s];
    responsibleP = new int[2 * s];
    responsibleEct = new int[2 * s];
    time = new long[n + 1];
    cap = new long[n + 1];
    next = new int[n + 1];
    pointOf = new int[n];
    state = new int[n];
    postponed = new int[n];
  }

  /**
   * Loads the bounds of the tasks of one view and sorts them.
   *
   * @param ts the tasks, with the field index equal to their position in ts.
   * @param n the number of tasks.
   */
  void load(TaskView[] ts, int n) {
    ensureCapacity(n);
    for (int i = 0; i < n; i++) {
      TaskView t = ts[i];
      est[i] = t.est();
      lct[i] = t.lct();
      dur[i] = t.dur.min();
      lst[i] = t.lst();
      ect[i] = t.ect();
    }
    sortAll(n);
  }

  private void sortAll(int n) {
    initOrders(n);
    sortBy(est, estOrder, n);
    sortBy(lct, lctOrder, n);
    sortBy(lst, lstOrder, n);
    sortBy(ect, ectOrder, n);
    sortDecLct(n);
  }

  private void initOrders(int n) {
    if (ordered != n) {
      for (int i = 0; i < n; i++) {
        estOrder[i] = i;
        lctOrder[i] = i;
        lstOrder[i] = i;
        ectOrder[i] = i;
        decLctOrder[i] = i;
      }
      ordered = n;
    }
  }

  // the order in which the edge finding of CumulativeUnary always visited the tasks
  private void sortDecLct(int n) {
    for (int i = 0; i < n; i++) {
      negLct[i] = -lct[i];
      negEst[i] = -est[i];
    }
    sortBy(negLct, negEst, decLctOrder, n);
  }

  /**
   * Loads the normal view of the tasks with one read of each bound of their variables; the same as
   * {@link #load(TaskView[], int)} for {@link TaskNormalView} tasks.
   *
   * @param ts the tasks in the normal view, with the field index equal to their position in ts.
   * @param n the number of tasks.
   */
  void loadNormal(TaskView[] ts, int n) {
    ensureCapacity(n);
    for (int i = 0; i < n; i++) {
      TaskView t = ts[i];
      int sMin = t.start.min();
      int sMax = t.start.max();
      int dMin = t.dur.min();
      est[i] = sMin;
      lst[i] = sMax;
      lct[i] = sMax + t.dur.max();
      ect[i] = sMin + dMin;
      dur[i] = dMin;
    }
    sortAll(n);
  }

  /**
   * Loads the reversed view of the tasks loaded in the normal view by another instance, without
   * reading the variables; the same as {@link #load(TaskView[], int)} for {@link TaskReversedView}
   * tasks.
   *
   * @param normal the instance holding the normal view.
   * @param n the number of tasks.
   */
  void loadReversed(UnaryReasoning normal, int n) {
    ensureCapacity(n);
    for (int i = 0; i < n; i++) {
      // the reversed task runs from -(sMax + dMax) to -sMin
      est[i] = -normal.lct[i];
      lct[i] = -normal.est[i];
      dur[i] = normal.dur[i];
      lst[i] = lct[i] - dur[i];
      ect[i] = est[i] + dur[i];
    }
    // the orders of the normal view backwards; tasks with equal keys come in the opposite order,
    // which changes no rule
    initOrders(n);
    reverse(normal.lctOrder, estOrder, n);
    reverse(normal.estOrder, lctOrder, n);
    reverse(normal.ectOrder, lstOrder, n);
    // with a variable duration the ect is not the opposite of the normal lst
    sortBy(ect, ectOrder, n);
    sortDecLct(n);
  }

  private static void reverse(int[] from, int[] to, int n) {
    for (int m = 0; m < n; m++) {
      to[m] = from[n - 1 - m];
    }
  }

  // insertion sort of order by (key, index), starting from the previous order
  private void sortBy(int[] key, int[] order, int n) {
    long[] k = sortKeys;
    for (int m = 0; m < n; m++) {
      int i = order[m];
      k[m] = ((long) key[i] << 32) | i;
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
    for (int m = 0; m < n; m++) {
      order[m] = (int) k[m];
    }
  }

  // insertion sort of order by (first, second, index), starting from the previous order
  private static void sortBy(int[] first, int[] second, int[] order, int n) {
    for (int k = 1; k < n; k++) {
      int i = order[k];
      int a = first[i];
      int b = second[i];
      int m = k - 1;
      while (m >= 0 && greater(first, second, order[m], a, b, i)) {
        order[m + 1] = order[m];
        m--;
      }
      order[m + 1] = i;
    }
  }

  private static boolean greater(int[] first, int[] second, int j, int a, int b, int i) {
    if (first[j] != a) {
      return first[j] > a;
    }
    if (second[j] != b) {
      return second[j] > b;
    }
    return j > i;
  }

  // places the tasks on the leaves of the tree in est order
  private void placeLeaves(int n) {
    size = 1;
    while (size < n) {
      size <<= 1;
    }
    for (int p = 0; p < n; p++) {
      int i = estOrder[p];
      leafOf[i] = size + p;
      taskOfLeaf[size + p] = i;
    }
  }

  // builds an empty Theta tree (all tasks outside Theta); not-last uses only the Theta values
  private void buildThetaTree(int n) {
    placeLeaves(n);
    for (int v = 1; v < 2 * size; v++) {
      treeP[v] = 0;
      treeEct[v] = EMPTY;
    }
  }

  // builds the Theta-Lambda tree with all tasks in Theta and none in Lambda, bottom up
  private void buildFullTree(int n) {
    placeLeaves(n);
    for (int v = size; v < 2 * size; v++) {
      treeP[v] = 0;
      treeEct[v] = EMPTY;
      treePLambda[v] = EMPTY;
      treeEctLambda[v] = EMPTY;
      responsibleP[v] = v;
      responsibleEct[v] = v;
    }
    for (int i = 0; i < n; i++) {
      int leaf = leafOf[i];
      treeP[leaf] = dur[i];
      treeEct[leaf] = ect[i];
    }
    for (int v = size - 1; v >= 1; v--) {
      combine(v);
    }
  }

  private void insertTheta(int i) {
    int leaf = leafOf[i];
    treeP[leaf] = dur[i];
    treeEct[leaf] = ect[i];
    for (int v = leaf >> 1; v >= 1; v >>= 1) {
      int l = 2 * v;
      int r = l + 1;
      treeP[v] = treeP[l] + treeP[r];
      treeEct[v] = Math.max(treeEct[l] + treeP[r], treeEct[r]);
    }
  }

  private void moveToLambda(int i) {
    int leaf = leafOf[i];
    treePLambda[leaf] = treeP[leaf];
    treeEctLambda[leaf] = treeEct[leaf];
    treeP[leaf] = 0;
    treeEct[leaf] = EMPTY;
    updatePath(leaf);
  }

  // the Theta values do not change, and the path stops at the first node whose Lambda values do not
  private void removeLambda(int leaf) {
    treePLambda[leaf] = EMPTY;
    treeEctLambda[leaf] = EMPTY;
    for (int v = leaf >> 1; v >= 1; v >>= 1) {
      if (!combineLambda(v)) {
        return;
      }
    }
  }

  private void updatePath(int leaf) {
    for (int v = leaf >> 1; v >= 1; v >>= 1) {
      combine(v);
    }
  }

  // the Theta and Lambda values of node v from its children
  private void combine(int v) {
    int l = 2 * v;
    int r = l + 1;
    treeP[v] = treeP[l] + treeP[r];
    treeEct[v] = Math.max(treeEct[l] + treeP[r], treeEct[r]);

    long viaLeft = treePLambda[l] + treeP[r];
    long viaRight = treePLambda[r] + treeP[l];
    if (viaLeft > viaRight) {
      treePLambda[v] = viaLeft;
      responsibleP[v] = responsibleP[l];
    } else {
      treePLambda[v] = viaRight;
      responsibleP[v] = responsibleP[r];
    }

    long a = treeEctLambda[l] + treeP[r];
    long b = treePLambda[r] + treeEct[l];
    if (a > b) {
      if (a > treeEctLambda[r]) {
        treeEctLambda[v] = a;
        responsibleEct[v] = responsibleEct[l];
      } else {
        treeEctLambda[v] = treeEctLambda[r];
        responsibleEct[v] = responsibleEct[r];
      }
    } else {
      if (b > treeEctLambda[r]) {
        treeEctLambda[v] = b;
        responsibleEct[v] = responsibleP[r];
      } else {
        treeEctLambda[v] = treeEctLambda[r];
        responsibleEct[v] = responsibleEct[r];
      }
    }
  }

  // the Lambda values of node v from its children; tells whether they changed
  private boolean combineLambda(int v) {
    int l = 2 * v;
    int r = l + 1;
    long pLambda;
    int pResponsible;
    long viaLeft = treePLambda[l] + treeP[r];
    long viaRight = treePLambda[r] + treeP[l];
    if (viaLeft > viaRight) {
      pLambda = viaLeft;
      pResponsible = responsibleP[l];
    } else {
      pLambda = viaRight;
      pResponsible = responsibleP[r];
    }

    long ectLambda;
    int ectResponsible;
    long a = treeEctLambda[l] + treeP[r];
    long b = treePLambda[r] + treeEct[l];
    if (a > b) {
      if (a > treeEctLambda[r]) {
        ectLambda = a;
        ectResponsible = responsibleEct[l];
      } else {
        ectLambda = treeEctLambda[r];
        ectResponsible = responsibleEct[r];
      }
    } else {
      if (b > treeEctLambda[r]) {
        ectLambda = b;
        ectResponsible = responsibleP[r];
      } else {
        ectLambda = treeEctLambda[r];
        ectResponsible = responsibleEct[r];
      }
    }
    if (pLambda == treePLambda[v]
        && pResponsible == responsibleP[v]
        && ectLambda == treeEctLambda[v]
        && ectResponsible == responsibleEct[v]) {
      return false;
    }
    treePLambda[v] = pLambda;
    responsibleP[v] = pResponsible;
    treeEctLambda[v] = ectLambda;
    responsibleEct[v] = ectResponsible;
    return true;
  }

  // ect of Theta without task i, read from the path of i without changing the tree
  private long ectWithout(int i) {
    int node = leafOf[i];
    if (treeEct[node] == EMPTY) {
      return treeEct[1];
    }
    long p = 0;
    long e = EMPTY;
    for (; node > 1; node >>= 1) {
      int sibling = node ^ 1;
      if ((node & 1) == 0) {
        // the path is the left child
        e = Math.max(e + treeP[sibling], treeEct[sibling]);
      } else {
        e = Math.max(treeEct[sibling] + p, e);
      }
      p += treeP[sibling];
    }
    return e;
  }

  // an empty time line over the distinct earliest start times of the tasks
  private void buildTimeline(int n) {
    int points = 0;
    long total = 0;
    for (int p = 0; p < n; p++) {
      int i = estOrder[p];
      total += dur[i];
      if (points == 0 || est[i] != time[points - 1]) {
        time[points++] = est[i];
      }
      pointOf[i] = points - 1;
    }
    // the last interval is long enough for all tasks
    time[points] = time[points - 1] + total;
    for (int a = 0; a < points; a++) {
      cap[a] = time[a + 1] - time[a];
      next[a] = a;
    }
    cap[points] = 0;
    next[points] = points;
    lastPoint = -1;
  }

  private int find(int a) {
    while (next[a] != a) {
      next[a] = next[next[a]];
      a = next[a];
    }
    return a;
  }

  // schedules task i preemptively from its earliest start in the free time of the time line
  private void schedule(int i) {
    int a = find(pointOf[i]);
    long rest = dur[i];
    while (rest > 0) {
      long used = Math.min(cap[a], rest);
      cap[a] -= used;
      rest -= used;
      if (a > lastPoint) {
        lastPoint = a;
      }
      if (cap[a] == 0) {
        next[a] = a + 1;
        a = find(a + 1);
      }
    }
  }

  // ect of the scheduled tasks: the end of the busy part of the last interval used
  private int timelineEct() {
    return lastPoint < 0 ? NONE : (int) (time[lastPoint + 1] - cap[lastPoint]);
  }

  /**
   * Fails if some set of tasks cannot be processed before the largest lct among them.
   *
   * @param n the number of loaded tasks.
   */
  void overload(int n) {
    buildTimeline(n);
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      schedule(i);
      if (timelineEct() > lct[i]) {
        throw Store.failException;
      }
    }
  }

  /**
   * Detectable precedences: a task starts after the tasks that must precede it.
   *
   * <p>Tasks are filtered in ect order with the tasks whose lst is below their ect on the time
   * line. A task that enters this set before its own turn has a compulsory part over the current
   * ect; it is the blocking task and stays off the time line until its turn. The tasks met
   * meanwhile must follow it, so they are filtered right after it, with the blocking task and the
   * tasks that precede it on the time line. Two blocking tasks, or a postponed task that must also
   * precede the blocking task, overload the resource. Each new bound is at least the one of the
   * Theta tree algorithm and follows from detectable precedences applied repeatedly.
   *
   * @param ts the tasks of the view, as loaded.
   * @param n the number of loaded tasks.
   * @param store the store.
   */
  void detectable(TaskView[] ts, int n, Store store) {
    buildTimeline(n);
    Arrays.fill(state, 0, n, WAITING);
    int blocking = -1;
    int nPostponed = 0;
    int indexQ = 0;
    for (int p = 0; p < n; p++) {
      int i = ectOrder[p];
      while (indexQ < n && ect[i] > lst[lstOrder[indexQ]]) {
        int k = lstOrder[indexQ];
        if (state[k] == FILTERED) {
          schedule(k);
        } else if (state[k] == POSTPONED || blocking != -1) {
          // k and the blocking task must each precede the other
          throw Store.failException;
        } else {
          blocking = k;
        }
        indexQ++;
      }
      if (blocking == -1 || blocking == i) {
        update[i] = Math.max(est[i], timelineEct());
        state[i] = FILTERED;
        if (blocking == i) {
          schedule(i);
          blocking = -1;
          int bound = timelineEct();
          for (int q = 0; q < nPostponed; q++) {
            int t = postponed[q];
            update[t] = Math.max(est[t], bound);
            state[t] = FILTERED;
          }
          nPostponed = 0;
        }
      } else {
        state[i] = POSTPONED;
        postponed[nPostponed++] = i;
      }
    }
    for (int i = 0; i < n; i++) {
      ts[i].updateDetectable(store.level, update[i]);
    }
  }

  /**
   * Not-last: a task that cannot be last among a set of tasks ends before the latest start of one
   * of them.
   *
   * @param ts the tasks of the view, as loaded.
   * @param n the number of loaded tasks.
   * @param store the store.
   */
  void notLast(TaskView[] ts, int n, Store store) {
    buildThetaTree(n);
    System.arraycopy(lct, 0, update, 0, n);
    int indexQ = 0;
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      boolean entered = false;
      while (indexQ < n && lct[i] > lst[lstOrder[indexQ]]) {
        if (treeEct[1] > lst[i] && ectWithout(i) > lst[i]) {
          update[i] = Math.min(lst[lstOrder[indexQ - 1]], update[i]);
        }
        insertTheta(lstOrder[indexQ]);
        indexQ++;
        entered = true;
      }
      if (entered && treeEct[1] > lst[i] && ectWithout(i) > lst[i]) {
        update[i] = Math.min(lst[lstOrder[indexQ - 1]], update[i]);
      }
    }
    for (int i = 0; i < n; i++) {
      ts[i].updateNotFirstNotLast(store.level, update[i]);
    }
  }

  /**
   * Edge finding: a task that must end after a set of tasks starts after all of them.
   *
   * @param ts the tasks of the view, as loaded.
   * @param n the number of loaded tasks.
   * @param store the store.
   */
  void edgeFind(TaskView[] ts, int n, Store store) {
    buildFullTree(n);
    int t = decLctOrder[0];
    for (int p = 0; p < n - 1; p++) {
      if (treeEct[1] > lct[t]) {
        throw Store.failException;
      }
      moveToLambda(t);
      t = decLctOrder[p + 1];
      while (treeEctLambda[1] > lct[t]) {
        int leaf = responsibleEct[1];
        ts[taskOfLeaf[leaf]].updateEdgeFind(store.level, (int) treeEct[1]);
        removeLambda(leaf);
      }
    }
  }
}
