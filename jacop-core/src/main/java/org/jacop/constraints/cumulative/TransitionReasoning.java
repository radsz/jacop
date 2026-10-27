/*
 * TransitionReasoning.java
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
 * Filtering rules of the unary resource with sequence-dependent transition times on one view
 * (normal or reversed) of the tasks, after Dejemeppe, Van Cauwelaert and Schaus, "The Unary
 * Resource with Transition Times", CP 2015, and Van Cauwelaert, Dejemeppe and Schaus, "An Efficient
 * Filtering Algorithm for the Unary Resource Constraint with Transition Times and Optional
 * Activities", Journal of Scheduling 23, 2020: the overload check, detectable precedences, not-last
 * and edge finding on Theta and Theta-Lambda trees whose earliest completion times count a lower
 * bound of the transitions between the families of their tasks.
 *
 * <p>A node of the tree keeps the processing time, the earliest completion time and the set of
 * families of its tasks. The earliest completion time of a node is the larger of the one of its
 * right child and the one of its left child plus the processing time of the right child plus {@code
 * tt(m + 1)}, where m counts the families of the right child that the left child does not have and
 * {@code tt(k)} is a lower bound of the total transition time of any k distinct families (see
 * {@link UnaryTransition}). A task that must follow a set of tasks also starts at least the
 * smallest transition into its family after their completion.
 *
 * <p>One instance serves one view; the reversed view has the transposed transition matrix.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class TransitionReasoning {

  // the empty value in the trees: far below any time, and adding times to it still leaves it far
  // below any time without overflow
  static final long EMPTY = Long.MIN_VALUE / 4;

  // the lower bounds tt(k) and the transitions of this view
  private final long[] ttk;
  // smallest transition into (out of) a family from (to) another family, and within a family
  private final long[] minIn;
  private final long[] minOut;
  private final long[] within;
  private final int words;

  // task data, indexed by the position of the task, loaded by the constraint: the family, the
  // bounds, and whether the task is optional (gray) for the rules on optional tasks
  final int[] fam;
  final boolean[] gray;
  final int[] est;
  final int[] lct;
  final int[] lst;
  final int[] ect;
  final int[] dur;
  // new bounds computed by a rule: est for detectable precedences and edge finding, lct for
  // not-last
  final long[] update;
  // optional tasks found absent by the rules on optional tasks
  final boolean[] absent;

  // the number of loaded tasks
  private int n;
  private final int[] estOrder;
  private final int[] lctOrder;
  private final int[] lstOrder;
  private final int[] ectOrder;
  private final long[] sortKeys;

  // the tree, root at 1, leaves at size + position in est order
  private final int size;
  private final int[] leafOf;
  private final long[] treeP;
  private final long[] treeEct;
  private final long[] treeFam;
  private final long[] treePLambda;
  private final long[] treeEctLambda;
  private final int[] responsibleP;
  private final int[] responsibleEct;
  private final boolean[] inTheta;
  // tasks of each family in Theta
  private final int[] famCount;

  /**
   * It creates the rules of one view.
   *
   * @param capacity the largest number of tasks.
   * @param transitions the transition times between families in this view.
   * @param ttk the lower bounds tt(k), for k from 0 to the number of families plus one.
   */
  TransitionReasoning(int capacity, int[][] transitions, long[] ttk) {
    this.ttk = ttk;
    this.n = capacity;
    int families = transitions.length;
    this.words = Math.max(1, (families + 63) >>> 6);
    minIn = new long[families];
    minOut = new long[families];
    within = new long[families];
    for (int f = 0; f < families; f++) {
      long in = Long.MAX_VALUE / 4;
      long out = Long.MAX_VALUE / 4;
      for (int g = 0; g < families; g++) {
        if (g != f) {
          in = Math.min(in, transitions[g][f]);
          out = Math.min(out, transitions[f][g]);
        }
      }
      minIn[f] = in;
      minOut[f] = out;
      within[f] = transitions[f][f];
    }
    fam = new int[n];
    gray = new boolean[n];
    absent = new boolean[n];
    est = new int[n];
    lct = new int[n];
    lst = new int[n];
    ect = new int[n];
    dur = new int[n];
    update = new long[n];
    estOrder = new int[n];
    lctOrder = new int[n];
    lstOrder = new int[n];
    ectOrder = new int[n];
    sortKeys = new long[n];
    int s = 1;
    while (s < n) {
      s <<= 1;
    }
    size = s;
    leafOf = new int[n];
    treeP = new long[2 * s];
    treeEct = new long[2 * s];
    treeFam = new long[2 * s * words];
    treePLambda = new long[2 * s];
    treeEctLambda = new long[2 * s];
    responsibleP = new int[2 * s];
    responsibleEct = new int[2 * s];
    inTheta = new boolean[n];
    famCount = new int[families];
  }

  /**
   * Sorts the loaded tasks; called after the task data was loaded.
   *
   * @param count the number of loaded tasks, at positions 0 to count - 1.
   */
  void sort(int count) {
    n = count;
    sortBy(est, estOrder);
    sortBy(lct, lctOrder);
    sortBy(lst, lstOrder);
    sortBy(ect, ectOrder);
    for (int p = 0; p < n; p++) {
      leafOf[estOrder[p]] = size + p;
    }
  }

  private void sortBy(int[] key, int[] order) {
    for (int i = 0; i < n; i++) {
      sortKeys[i] = ((long) key[i] << 32) | i;
    }
    Arrays.sort(sortKeys, 0, n);
    for (int m = 0; m < n; m++) {
      order[m] = (int) sortKeys[m];
    }
  }

  // ---- the tree ----

  private void clearTree() {
    Arrays.fill(treeP, 0);
    Arrays.fill(treeEct, EMPTY);
    Arrays.fill(treeFam, 0);
    Arrays.fill(treePLambda, EMPTY);
    Arrays.fill(treeEctLambda, EMPTY);
    Arrays.fill(responsibleP, -1);
    Arrays.fill(responsibleEct, -1);
    Arrays.fill(inTheta, false);
    Arrays.fill(famCount, 0);
  }

  // puts task i in Theta at its leaf, without updating the path
  private void setTheta(int i) {
    int leaf = leafOf[i];
    treeP[leaf] = dur[i];
    treeEct[leaf] = ect[i];
    int base = leaf * words;
    Arrays.fill(treeFam, base, base + words, 0);
    treeFam[base + (fam[i] >>> 6)] = 1L << (fam[i] & 63);
    treePLambda[leaf] = EMPTY;
    treeEctLambda[leaf] = EMPTY;
    responsibleP[leaf] = -1;
    responsibleEct[leaf] = -1;
    inTheta[i] = true;
    famCount[fam[i]]++;
  }

  // empties the leaf of task i, without updating the path
  private void setEmpty(int i) {
    int leaf = leafOf[i];
    treeP[leaf] = 0;
    treeEct[leaf] = EMPTY;
    int base = leaf * words;
    Arrays.fill(treeFam, base, base + words, 0);
    treePLambda[leaf] = EMPTY;
    treeEctLambda[leaf] = EMPTY;
    responsibleP[leaf] = -1;
    responsibleEct[leaf] = -1;
    if (inTheta[i]) {
      inTheta[i] = false;
      famCount[fam[i]]--;
    }
  }

  // moves task i from Theta to Lambda, without updating the path
  private void setLambda(int i) {
    setEmpty(i);
    int leaf = leafOf[i];
    treePLambda[leaf] = dur[i];
    treeEctLambda[leaf] = ect[i];
    responsibleP[leaf] = i;
    responsibleEct[leaf] = i;
  }

  private void insertTheta(int i) {
    setTheta(i);
    updatePath(leafOf[i], false);
  }

  private void removeTheta(int i) {
    setEmpty(i);
    updatePath(leafOf[i], false);
  }

  private void updatePath(int leaf, boolean lambda) {
    for (int v = leaf >> 1; v >= 1; v >>= 1) {
      combine(v, lambda);
    }
  }

  private long tt(int k) {
    return ttk[k];
  }

  // the Theta (and Lambda) values of node v from its children
  private void combine(int v, boolean lambda) {
    int l = 2 * v;
    int r = l + 1;
    int bv = v * words;
    int bl = l * words;
    int br = r * words;
    int newInRight = 0;
    for (int w = 0; w < words; w++) {
      long fl = treeFam[bl + w];
      long fr = treeFam[br + w];
      treeFam[bv + w] = fl | fr;
      newInRight += Long.bitCount(fr & ~fl);
    }
    treeP[v] = treeP[l] + treeP[r];
    treeEct[v] = Math.max(treeEct[r], treeEct[l] + treeP[r] + tt(newInRight + 1));
    if (!lambda) {
      return;
    }

    long viaLeft = treePLambda[l] + treeP[r];
    long viaRight = treePLambda[r] + treeP[l];
    if (viaLeft > viaRight) {
      treePLambda[v] = viaLeft;
      responsibleP[v] = responsibleP[l];
    } else {
      treePLambda[v] = viaRight;
      responsibleP[v] = responsibleP[r];
    }

    // the gray task on the left: the families new on the right exclude its family
    int grayL = responsibleEct[l];
    int newA = newInRight;
    if (grayL >= 0 && has(br, fam[grayL]) && !has(bl, fam[grayL])) {
      newA--;
    }
    long a = treeEctLambda[l] + treeP[r] + tt(newA + 1);
    // the gray task on the right: its family may be new
    int grayR = responsibleP[r];
    int newB = newInRight;
    if (grayR >= 0 && !has(br, fam[grayR]) && !has(bl, fam[grayR])) {
      newB++;
    }
    long b = treeEct[l] + treePLambda[r] + tt(newB + 1);
    long c = treeEctLambda[r];
    if (a >= b && a >= c) {
      treeEctLambda[v] = a;
      responsibleEct[v] = grayL;
    } else if (b >= c) {
      treeEctLambda[v] = b;
      responsibleEct[v] = grayR;
    } else {
      treeEctLambda[v] = c;
      responsibleEct[v] = responsibleEct[r];
    }
  }

  private boolean has(int base, int f) {
    return (treeFam[base + (f >>> 6)] & (1L << (f & 63))) != 0;
  }

  // the smallest transition into task i from a task of Theta, which does not contain i
  private long transitionIn(int i) {
    int f = fam[i];
    return famCount[f] > 0 ? Math.min(minIn[f], within[f]) : minIn[f];
  }

  // the smallest transition from task i to a task of Theta, which does not contain i
  private long transitionOut(int i) {
    int f = fam[i];
    return famCount[f] > 0 ? Math.min(minOut[f], within[f]) : minOut[f];
  }

  // ---- the rules ----

  /** Fails if some set of tasks cannot be processed with its transitions before its largest lct. */
  void overload() {
    clearTree();
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      insertTheta(i);
      if (treeEct[1] > lct[i]) {
        throw Store.failException;
      }
    }
  }

  /**
   * Detectable precedences: a task starts after the tasks whose latest start is below its earliest
   * completion, and after a transition from one of them. The new earliest starts are in update.
   */
  void detectable() {
    clearTree();
    for (int i = 0; i < n; i++) {
      update[i] = est[i];
    }
    int q = 0;
    for (int p = 0; p < n; p++) {
      int i = ectOrder[p];
      while (q < n && ect[i] > lst[lstOrder[q]]) {
        insertTheta(lstOrder[q]);
        q++;
      }
      boolean own = inTheta[i];
      if (own) {
        removeTheta(i);
      }
      if (treeEct[1] > EMPTY / 2) {
        update[i] = Math.max(update[i], treeEct[1] + transitionIn(i));
      }
      if (own) {
        insertTheta(i);
      }
    }
  }

  /**
   * Not-last: a task that cannot be last among a set of tasks ends before the latest start of one
   * of them, by a transition to it. The new latest completions are in update.
   */
  void notLast() {
    clearTree();
    for (int i = 0; i < n; i++) {
      update[i] = lct[i];
    }
    int q = 0;
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      while (q < n && lct[i] > lst[lstOrder[q]]) {
        insertTheta(lstOrder[q]);
        q++;
      }
      if (q == 0) {
        continue;
      }
      boolean own = inTheta[i];
      if (own) {
        removeTheta(i);
      }
      if (treeEct[1] > lst[i]) {
        update[i] = Math.min(update[i], lst[lstOrder[q - 1]] - transitionOut(i));
      }
      if (own) {
        insertTheta(i);
      }
    }
  }

  /**
   * The overload check with optional tasks (Vilím, Barták and Čepek, CP 2004, with transitions):
   * the tasks enter by lct, mandatory ones in Theta and optional ones in Lambda; an optional task
   * whose presence would overload the tasks up to the current lct is absent. The absent tasks are
   * marked in absent.
   */
  void optionalOverload() {
    clearTree();
    Arrays.fill(absent, 0, n, false);
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      if (gray[i]) {
        setLambda(i);
      } else {
        setTheta(i);
      }
      updatePath(leafOf[i], true);
      if (treeEct[1] > lct[i]) {
        throw Store.failException;
      }
      while (treeEctLambda[1] > lct[i]) {
        int r = responsibleEct[1];
        if (r < 0) {
          break;
        }
        absent[r] = true;
        setEmpty(r);
        updatePath(leafOf[r], true);
      }
    }
  }

  /**
   * Edge finding: a task that must end after a set of tasks starts after all of them, by a
   * transition from one of them. The new earliest starts are in update.
   */
  void edgeFind() {
    clearTree();
    Arrays.fill(absent, 0, n, false);
    for (int i = 0; i < n; i++) {
      update[i] = est[i];
      if (gray[i]) {
        setLambda(i);
      } else {
        setTheta(i);
      }
    }
    for (int v = size - 1; v >= 1; v--) {
      combine(v, true);
    }
    // tasks by decreasing lct, then decreasing est
    int[] order = lctOrder;
    // the mandatory tasks by decreasing lct leave Theta one by one; before each leaves, the tasks
    // of Lambda that must follow Theta are found
    for (int p = n - 1; p >= 0; p--) {
      int t = order[p];
      if (gray[t]) {
        continue;
      }
      if (treeEct[1] > lct[t]) {
        throw Store.failException;
      }
      while (treeEctLambda[1] > lct[t]) {
        int r = responsibleEct[1];
        if (r < 0) {
          break;
        }
        long bound = treeEct[1] + transitionIn(r);
        if (!gray[r]) {
          update[r] = Math.max(update[r], bound);
        } else if (bound > lst[r]) {
          // if present, the optional task would start after its latest start
          absent[r] = true;
        }
        setEmpty(r);
        updatePath(leafOf[r], true);
      }
      setLambda(t);
      updatePath(leafOf[t], true);
    }
  }
}
