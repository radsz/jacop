/*
 * UnaryReasoningReference.java
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

import org.jacop.core.Store;

/**
 * Filtering rules of the unary resource (disjunctive) constraint on one view (normal or reversed)
 * of the tasks, after Vilím, "O(n log n) Filtering Algorithms for Unary Resource Constraint",
 * CPAIOR 2004, and Vilím, Barták and Čepek, "Unary Resource Constraint with Optional Activities",
 * CP 2004: the overload check, detectable precedences, not-last and edge finding, all with the
 * Theta and Theta-Lambda trees.
 *
 * <p>This is {@link UnaryReasoning} as it was before the time line, kept as the reference for
 * {@link UnaryReasoningTest}, with not-last testing every task and bounding it by the largest lst
 * of the other tasks in Theta.
 *
 * <p>It works on primitive arrays reused between calls, and keeps the task orders of the previous
 * call, which it re-sorts by insertion since bounds change little between calls. One instance
 * serves one view.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class UnaryReasoningReference {

  private static final int NONE = Integer.MIN_VALUE;

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

  // Theta-Lambda tree with leaves in est order; root at 1, leaves at size + rank
  private int size;
  private int[] leafOf = new int[0];
  private int[] taskOfLeaf = new int[0];
  private int[] treeP = new int[0];
  private int[] treeEct = new int[0];
  private int[] treePLambda = new int[0];
  private int[] treeEctLambda = new int[0];
  private int[] responsibleP = new int[0];
  private int[] responsibleEct = new int[0];

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
    ordered = -1;
    int s = 1;
    while (s < n) {
      s <<= 1;
    }
    leafOf = new int[n];
    taskOfLeaf = new int[2 * s];
    treeP = new int[2 * s];
    treeEct = new int[2 * s];
    treePLambda = new int[2 * s];
    treeEctLambda = new int[2 * s];
    responsibleP = new int[2 * s];
    responsibleEct = new int[2 * s];
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
      negLct[i] = -lct[i];
      negEst[i] = -est[i];
    }
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
    sortBy(est, est, estOrder, n);
    sortBy(lct, lct, lctOrder, n);
    sortBy(lst, lst, lstOrder, n);
    sortBy(ect, ect, ectOrder, n);
    // the order in which the edge finding of CumulativeUnary always visited the tasks
    sortBy(negLct, negEst, decLctOrder, n);
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

  private static int plus(int x, int y) {
    return x == NONE || y == NONE ? NONE : x + y;
  }

  // builds an empty tree (all tasks outside Theta and Lambda) with leaves in est order
  private void buildTree(int n) {
    size = 1;
    while (size < n) {
      size <<= 1;
    }
    for (int v = 1; v < 2 * size; v++) {
      clear(v);
    }
    for (int p = 0; p < n; p++) {
      int i = estOrder[p];
      leafOf[i] = size + p;
      taskOfLeaf[size + p] = i;
    }
  }

  private void clear(int v) {
    treeP[v] = 0;
    treeEct[v] = NONE;
    treePLambda[v] = NONE;
    treeEctLambda[v] = NONE;
    responsibleP[v] = v;
    responsibleEct[v] = v;
  }

  private void insertTheta(int i) {
    int leaf = leafOf[i];
    treeP[leaf] = dur[i];
    treeEct[leaf] = ect[i];
    updatePath(leaf);
  }

  private void removeTheta(int i) {
    int leaf = leafOf[i];
    treeP[leaf] = 0;
    treeEct[leaf] = NONE;
    updatePath(leaf);
  }

  private void moveToLambda(int i) {
    int leaf = leafOf[i];
    treePLambda[leaf] = treeP[leaf];
    treeEctLambda[leaf] = treeEct[leaf];
    treeP[leaf] = 0;
    treeEct[leaf] = NONE;
    updatePath(leaf);
  }

  private void removeLambda(int leaf) {
    treePLambda[leaf] = NONE;
    treeEctLambda[leaf] = NONE;
    updatePath(leaf);
  }

  private void updatePath(int leaf) {
    for (int v = leaf >> 1; v >= 1; v >>= 1) {
      int l = 2 * v;
      int r = l + 1;
      treeP[v] = treeP[l] + treeP[r];
      treeEct[v] = Math.max(plus(treeEct[l], treeP[r]), treeEct[r]);

      int viaLeft = plus(treePLambda[l], treeP[r]);
      int viaRight = plus(treePLambda[r], treeP[l]);
      if (viaLeft > viaRight) {
        treePLambda[v] = viaLeft;
        responsibleP[v] = responsibleP[l];
      } else {
        treePLambda[v] = viaRight;
        responsibleP[v] = responsibleP[r];
      }

      int a = plus(treeEctLambda[l], treeP[r]);
      int b = plus(treePLambda[r], treeEct[l]);
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
  }

  // ect of Theta without task i
  private int ectWithout(int i) {
    int leaf = leafOf[i];
    if (treeEct[leaf] == NONE) {
      return treeEct[1];
    }
    removeTheta(i);
    int result = treeEct[1];
    insertTheta(i);
    return result;
  }

  /**
   * Fails if some set of tasks cannot be processed before the largest lct among them.
   *
   * @param n the number of loaded tasks.
   */
  void overload(int n) {
    buildTree(n);
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      insertTheta(i);
      if (treeEct[1] > lct[i]) {
        throw Store.failException;
      }
    }
  }

  /**
   * Detectable precedences: a task starts after the tasks that must precede it.
   *
   * @param ts the tasks of the view, as loaded.
   * @param n the number of loaded tasks.
   * @param store the store.
   */
  void detectable(TaskView[] ts, int n, Store store) {
    buildTree(n);
    int indexQ = 0;
    for (int p = 0; p < n; p++) {
      int i = ectOrder[p];
      while (indexQ < n && ect[i] > lst[lstOrder[indexQ]]) {
        insertTheta(lstOrder[indexQ]);
        indexQ++;
      }
      update[i] = Math.max(est[i], ectWithout(i));
    }
    for (int i = 0; i < n; i++) {
      ts[i].updateDetectable(store.level, update[i]);
    }
  }

  // the largest lst in Theta without task i: Theta holds the first indexQ tasks in lst order
  private int lastLstWithout(int i, int indexQ) {
    int j = lstOrder[indexQ - 1];
    return j != i ? lst[j] : lst[lstOrder[indexQ - 2]];
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
    buildTree(n);
    System.arraycopy(lct, 0, update, 0, n);
    int indexQ = 0;
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      while (indexQ < n && lct[i] > lst[lstOrder[indexQ]]) {
        if (ectWithout(i) > lst[i]) {
          update[i] = Math.min(lastLstWithout(i, indexQ), update[i]);
        }
        insertTheta(lstOrder[indexQ]);
        indexQ++;
      }
      if (indexQ > 0 && ectWithout(i) > lst[i]) {
        update[i] = Math.min(lastLstWithout(i, indexQ), update[i]);
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
    buildTree(n);
    for (int i = 0; i < n; i++) {
      insertTheta(i);
    }
    int t = decLctOrder[0];
    for (int p = 0; p < n - 1; p++) {
      if (treeEct[1] > lct[t]) {
        throw Store.failException;
      }
      moveToLambda(t);
      t = decLctOrder[p + 1];
      while (treeEctLambda[1] > lct[t]) {
        int leaf = responsibleEct[1];
        ts[taskOfLeaf[leaf]].updateEdgeFind(store.level, treeEct[1]);
        removeLambda(leaf);
      }
    }
  }
}
