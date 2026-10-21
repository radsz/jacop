/*
 * EnergyReasoning.java
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
 * Energy based filtering rules for the cumulative constraint that work on one view (normal or
 * reversed) of the tasks and only adjust earliest start times; the reversed view gives the latest
 * completion times.
 *
 * <p>It implements
 *
 * <ul>
 *   <li>the O(n log n) overload check of Wolf and Schrader, "O(n log n) Overload Checking for the
 *       Cumulative Constraint and Its Application", INAP 2005;
 *   <li>time-table edge finding of Vilím, "Timetable Edge Finding Filtering Algorithm for Discrete
 *       Cumulative Resources", CPAIOR 2011, in the O(n^2) form of Schutt, Feydy and Stuckey,
 *       "Explaining Time-Table-Edge-Finding Propagation for the Cumulative Resource Constraint",
 *       CPAIOR 2013;
 *   <li>time-table disjunctive reasoning of Gay, Hartert and Schaus, "Time-Table Disjunctive
 *       Reasoning for the Cumulative Constraint", CPAIOR 2015;
 *   <li>the overload check with optional tasks of Vilím, Barták and Čepek, "Extension of O(n log n)
 *       Filtering Algorithms for the Unary Resource Constraint to Optional Activities", Constraints
 *       2005, applied to the cumulative energy envelope.
 * </ul>
 *
 * <p>All rules use the minimal duration and the minimal resource use of each task, so they are
 * sound for variable durations and resources. The arrays are reused between calls.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class EnergyReasoning {

  // task data of the current view, indexed by the position in the task array
  private int[] est = new int[0];
  private int[] lct = new int[0];
  private int[] lst = new int[0];
  private int[] ect = new int[0];
  private int[] dur = new int[0];
  private int[] res = new int[0];
  private int[] update = new int[0];
  private long[] energyBeforeEst = new long[0];

  // tasks sorted by est and by lct
  private int[] estOrder = new int[0];
  private int[] lctOrder = new int[0];
  private long[] keys = new long[0];

  // compulsory part profile: height profileHeight[k] on [profileTime[k], profileTime[k + 1])
  private int[] profileTime = new int[0];
  private int[] profileHeight = new int[0];
  // energy of the profile before profileTime[k]
  private long[] profileEnergy = new long[0];
  private int profileSize;
  private long[] events = new long[0];

  // theta-lambda tree over tasks sorted by est
  private long[] treeEnergy = new long[0];
  private long[] treeEnvelope = new long[0];
  private long[] treeEnergyLambda = new long[0];
  private long[] treeEnvelopeLambda = new long[0];
  private int[] responsibleEnergy = new int[0];
  private int[] responsibleEnvelope = new int[0];
  private int[] leafOf = new int[0];
  private int[] taskOfLeaf = new int[0];
  private int leaves;

  private void ensureCapacity(int n) {
    if (est.length >= n) {
      return;
    }
    est = new int[n];
    lct = new int[n];
    lst = new int[n];
    ect = new int[n];
    dur = new int[n];
    res = new int[n];
    update = new int[n];
    energyBeforeEst = new long[n];
    estOrder = new int[n];
    lctOrder = new int[n];
    keys = new long[n];
    profileTime = new int[2 * n + 1];
    profileHeight = new int[2 * n + 1];
    profileEnergy = new long[2 * n + 1];
    events = new long[2 * n];
    int size = 1;
    while (size < n) {
      size <<= 1;
    }
    treeEnergy = new long[2 * size];
    treeEnvelope = new long[2 * size];
    treeEnergyLambda = new long[2 * size];
    treeEnvelopeLambda = new long[2 * size];
    responsibleEnergy = new int[2 * size];
    responsibleEnvelope = new int[2 * size];
    leafOf = new int[n];
    taskOfLeaf = new int[size];
  }

  /**
   * Loads the bounds of the tasks of one view.
   *
   * @param ts the tasks; all must have positive minimal duration and resource use.
   * @param n the number of tasks used from ts.
   */
  void load(TaskView[] ts, int n) {
    load(ts, n, false);
  }

  /**
   * Loads the bounds of the tasks of one view.
   *
   * @param ts the tasks; all must have positive minimal duration and resource use.
   * @param n the number of tasks used from ts.
   * @param unit true if every task uses one unit of the resource, as on a unary resource whose
   *     tasks pairwise cannot overlap.
   */
  void load(TaskView[] ts, int n, boolean unit) {
    ensureCapacity(n);
    for (int i = 0; i < n; i++) {
      TaskView t = ts[i];
      est[i] = t.est();
      lct[i] = t.lct();
      lst[i] = t.lst();
      ect[i] = t.ect();
      dur[i] = t.dur.min();
      res[i] = unit ? 1 : t.res.min();
    }
    sortBy(est, estOrder, n);
    sortBy(lct, lctOrder, n);
  }

  private void sortBy(int[] value, int[] order, int n) {
    for (int i = 0; i < n; i++) {
      keys[i] = ((long) value[i] << 32) | i;
    }
    Arrays.sort(keys, 0, n);
    for (int i = 0; i < n; i++) {
      order[i] = (int) keys[i];
    }
  }

  /**
   * Builds the compulsory part profile of the loaded tasks; tasks for which present[i] is false do
   * not contribute.
   */
  private void buildProfile(int n, boolean[] present) {
    int m = 0;
    for (int i = 0; i < n; i++) {
      if (lst[i] < ect[i] && (present == null || present[i])) {
        // low bits: 0 ends a compulsory part, 1 starts one; the index is not needed
        events[m++] = ((long) lst[i] << 32) | 1L;
        events[m++] = ((long) ect[i] << 32);
        events[m - 2] |= (long) i << 1;
        events[m - 1] |= (long) i << 1;
      }
    }
    Arrays.sort(events, 0, m);
    int k = 0;
    int height = 0;
    long energy = 0;
    for (int e = 0; e < m; e++) {
      int time = (int) (events[e] >> 32);
      int i = (int) (events[e] & 0xFFFFFFFFL) >>> 1;
      if (k > 0 && profileTime[k - 1] == time) {
        k--;
      } else if (k > 0) {
        energy += (long) profileHeight[k - 1] * (time - profileTime[k - 1]);
      }
      height += (events[e] & 1L) == 1L ? res[i] : -res[i];
      profileTime[k] = time;
      profileHeight[k] = height;
      profileEnergy[k] = energy;
      k++;
    }
    profileSize = k;
  }

  // the index of the last profile segment starting at or before t, -1 if none
  private int segment(int t) {
    int low = 0;
    int high = profileSize - 1;
    int found = -1;
    while (low <= high) {
      int mid = (low + high) >>> 1;
      if (profileTime[mid] <= t) {
        found = mid;
        low = mid + 1;
      } else {
        high = mid - 1;
      }
    }
    return found;
  }

  private int height(int t) {
    int k = segment(t);
    return k < 0 ? 0 : profileHeight[k];
  }

  // minimal profile height over the time points a..b (inclusive)
  private int minHeight(int a, int b) {
    int k = segment(a);
    int min = k < 0 ? 0 : profileHeight[k];
    for (k++; k < profileSize && profileTime[k] <= b; k++) {
      min = Math.min(min, profileHeight[k]);
    }
    return min;
  }

  // energy of the profile before time t
  private long profileEnergyBefore(int t) {
    int k = segment(t);
    return k < 0 ? 0 : profileEnergy[k] + (long) profileHeight[k] * (t - profileTime[k]);
  }

  /**
   * Checks that no set of tasks {j : a &lt;= est_j, lct_j &lt;= b} needs more energy than the
   * capacity provides in [a, b), in O(n log n).
   *
   * @param capacity the maximal capacity.
   * @param n the number of loaded tasks.
   */
  void overload(long capacity, int n) {
    buildTree(n);
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      insertTheta(i, capacity);
      if (treeEnvelope[1] > capacity * lct[i]) {
        throw Store.failException;
      }
    }
  }

  /**
   * Overload check with optional tasks. Present tasks are in Theta, optional ones in Lambda. An
   * optional task whose addition to the present tasks overloads the resource is made absent.
   *
   * @param capacity the maximal capacity.
   * @param n the number of loaded tasks.
   * @param present whether each task is present (true) or optional (false).
   * @param opt the presence variables, indexed as the loaded tasks.
   * @param store the store.
   */
  void overloadOptional(long capacity, int n, boolean[] present, IntVar[] opt, Store store) {
    buildTree(n);
    for (int p = 0; p < n; p++) {
      int i = lctOrder[p];
      long bound = capacity * lct[i];
      if (present[i]) {
        insertTheta(i, capacity);
        if (treeEnvelope[1] > bound) {
          throw Store.failException;
        }
      } else {
        insertLambda(i, capacity);
      }
      while (treeEnvelopeLambda[1] > bound) {
        int leaf = responsibleEnvelope[1];
        if (leaf < 0) {
          break;
        }
        int j = taskOfLeaf[leaf - treeEnergy.length / 2];
        opt[j].domain.in(store.level, opt[j], 0, 0);
        removeLambda(j);
      }
    }
  }

  /**
   * Edge finding with optional tasks on a unary resource (loaded with unit resource use and
   * capacity 1). Present tasks are processed in non-increasing lct; when the present tasks with lct
   * up to the current one plus an optional task o cannot end by that lct, o has to end after all of
   * them, so it starts after their earliest completion time. If that is after its latest start, or
   * o itself must end by that lct, o is made absent.
   *
   * @param n the number of loaded tasks.
   * @param present whether each task is present (true) or optional (false).
   * @param opt the presence variables, indexed as the loaded tasks.
   * @param store the store.
   */
  void unaryEdgeFindOptional(int n, boolean[] present, IntVar[] opt, Store store) {
    buildTree(n);
    for (int i = 0; i < n; i++) {
      if (present[i]) {
        insertTheta(i, 1);
      } else {
        insertLambda(i, 1);
      }
    }
    for (int p = n - 1; p >= 0; p--) {
      int j = lctOrder[p];
      if (!present[j]) {
        continue;
      }
      long bound = lct[j];
      if (treeEnvelope[1] > bound) {
        throw Store.failException;
      }
      while (treeEnvelopeLambda[1] > bound) {
        int leaf = responsibleEnvelope[1];
        if (leaf < 0) {
          break;
        }
        int i = taskOfLeaf[leaf - treeEnergy.length / 2];
        if (!present[i] && (lct[i] <= bound || treeEnvelope[1] > lst[i])) {
          opt[i].domain.in(store.level, opt[i], 0, 0);
        }
        removeLambda(i);
      }
      insertLambda(j, 1);
    }
  }

  private void buildTree(int n) {
    leaves = treeEnergy.length / 2;
    Arrays.fill(treeEnergy, 0L);
    Arrays.fill(treeEnvelope, Long.MIN_VALUE);
    Arrays.fill(treeEnergyLambda, 0L);
    Arrays.fill(treeEnvelopeLambda, Long.MIN_VALUE);
    Arrays.fill(responsibleEnergy, -1);
    Arrays.fill(responsibleEnvelope, -1);
    for (int p = 0; p < n; p++) {
      leafOf[estOrder[p]] = leaves + p;
      taskOfLeaf[p] = estOrder[p];
    }
  }

  private void insertTheta(int i, long capacity) {
    int leaf = leafOf[i];
    long e = (long) dur[i] * res[i];
    treeEnergy[leaf] = e;
    treeEnvelope[leaf] = capacity * est[i] + e;
    treeEnergyLambda[leaf] = e;
    treeEnvelopeLambda[leaf] = capacity * est[i] + e;
    responsibleEnergy[leaf] = -1;
    responsibleEnvelope[leaf] = -1;
    updatePath(leaf);
  }

  private void insertLambda(int i, long capacity) {
    int leaf = leafOf[i];
    long e = (long) dur[i] * res[i];
    treeEnergy[leaf] = 0L;
    treeEnvelope[leaf] = Long.MIN_VALUE;
    treeEnergyLambda[leaf] = e;
    treeEnvelopeLambda[leaf] = capacity * est[i] + e;
    responsibleEnergy[leaf] = leaf;
    responsibleEnvelope[leaf] = leaf;
    updatePath(leaf);
  }

  private void removeLambda(int i) {
    int leaf = leafOf[i];
    treeEnergyLambda[leaf] = 0L;
    treeEnvelopeLambda[leaf] = Long.MIN_VALUE;
    responsibleEnergy[leaf] = -1;
    responsibleEnvelope[leaf] = -1;
    updatePath(leaf);
  }

  private static long plus(long x, long y) {
    return x == Long.MIN_VALUE ? Long.MIN_VALUE : x + y;
  }

  private void updatePath(int leaf) {
    for (int v = leaf >> 1; v >= 1; v >>= 1) {
      int l = 2 * v;
      int r = l + 1;
      treeEnergy[v] = treeEnergy[l] + treeEnergy[r];
      treeEnvelope[v] = Math.max(plus(treeEnvelope[l], treeEnergy[r]), treeEnvelope[r]);

      // energy with at most one lambda task
      long viaLeft = treeEnergyLambda[l] + treeEnergy[r];
      long viaRight = treeEnergy[l] + treeEnergyLambda[r];
      if (viaLeft >= viaRight) {
        treeEnergyLambda[v] = viaLeft;
        responsibleEnergy[v] = responsibleEnergy[l];
      } else {
        treeEnergyLambda[v] = viaRight;
        responsibleEnergy[v] = responsibleEnergy[r];
      }

      // envelope with at most one lambda task
      long a = plus(treeEnvelopeLambda[l], treeEnergy[r]);
      long b = plus(treeEnvelope[l], treeEnergyLambda[r]);
      long c = treeEnvelopeLambda[r];
      if (a >= b && a >= c) {
        treeEnvelopeLambda[v] = a;
        responsibleEnvelope[v] = responsibleEnvelope[l];
      } else if (b >= c) {
        treeEnvelopeLambda[v] = b;
        responsibleEnvelope[v] = responsibleEnergy[r];
      } else {
        treeEnvelopeLambda[v] = c;
        responsibleEnvelope[v] = responsibleEnvelope[r];
      }
    }
  }

  /**
   * Time-table edge finding. For every window [a, b) with a an est and b an lct, the energy of the
   * compulsory parts in the window plus the free energy of the tasks inside the window must fit
   * into the capacity (otherwise it fails), and the task outside the window that needs most energy
   * in it when started at its est is pushed so that it fits.
   *
   * @param ts the tasks of the view, as loaded.
   * @param n the number of loaded tasks.
   * @param capacity the maximal capacity.
   * @param store the store.
   */
  void timeTableEdgeFind(TaskView[] ts, int n, long capacity, Store store) {
    buildProfile(n, null);
    for (int i = 0; i < n; i++) {
      update[i] = est[i];
      energyBeforeEst[i] = profileEnergyBefore(est[i]);
    }

    for (int q = n - 1; q >= 0; q--) {
      int b = lct[lctOrder[q]];
      if (q < n - 1 && lct[lctOrder[q + 1]] == b) {
        continue;
      }
      long energyBeforeB = profileEnergyBefore(b);
      long freeEnergy = 0;
      int best = -1;
      long bestEnergy = 0;
      for (int p = n - 1; p >= 0; p--) {
        int j = estOrder[p];
        int freeDuration = dur[j] - Math.max(0, ect[j] - lst[j]);
        if (lct[j] <= b) {
          freeEnergy += (long) res[j] * freeDuration;
        } else if (est[j] < b) {
          long needed = (long) res[j] * Math.min(freeDuration, b - est[j]);
          if (needed > bestEnergy) {
            bestEnergy = needed;
            best = j;
          }
        }
        int a = est[j];
        if (a >= b || (p > 0 && est[estOrder[p - 1]] == a)) {
          continue;
        }
        long available = capacity * (b - a) - freeEnergy - (energyBeforeB - energyBeforeEst[j]);
        if (available < 0) {
          throw Store.failException;
        }
        if (best >= 0 && bestEnergy > available) {
          int coreInWindow = Math.max(0, Math.min(ect[best], b) - Math.max(lst[best], a));
          long newEst = b - coreInWindow - available / res[best];
          if (newEst > update[best]) {
            update[best] = (int) newEst;
          }
        }
      }
    }

    for (int i = 0; i < n; i++) {
      if (update[i] > est[i]) {
        ts[i].updateEdgeFind(store.level, update[i]);
      }
    }
  }

  /**
   * Time-table disjunctive reasoning. A pusher task i must overlap some time point of a set M_i
   * (its minimum overlapping interval, or two of its points). If a pushed task j covers M_i when it
   * starts at any time up to min(M_i) and the profile on M_i leaves no room for both, j starts
   * after min(M_i).
   *
   * @param ts the tasks of the view, as loaded.
   * @param n the number of loaded tasks.
   * @param capacity the maximal capacity.
   * @param store the store.
   */
  void timeTableDisjunctive(TaskView[] ts, int n, long capacity, Store store) {
    buildProfile(n, null);
    int maxRes = 0;
    for (int i = 0; i < n; i++) {
      update[i] = est[i];
      maxRes = Math.max(maxRes, res[i]);
    }

    for (int i = 0; i < n; i++) {
      // points that every placement of i overlaps: [from, to] or only {from, to}
      int from;
      int to;
      long load;
      if (lst[i] < ect[i]) {
        if (est[i] == lst[i]) {
          continue;
        }
        from = lst[i] - 1;
        to = ect[i];
        load = Math.min(height(from), height(to));
      } else {
        from = ect[i] - 1;
        to = lst[i];
        load = lst[i] - ect[i] < dur[i] ? Math.min(height(from), height(to)) : minHeight(from, to);
      }
      long gap = capacity - res[i] - load;
      if (gap >= maxRes) {
        continue;
      }
      for (int j = 0; j < n; j++) {
        if (j == i || res[j] <= gap || update[j] > from) {
          continue;
        }
        int freeEnd = est[j] + dur[j] - Math.max(0, ect[j] - lst[j]);
        if (est[j] <= from && to < freeEnd) {
          update[j] = from + 1;
        }
      }
    }

    for (int i = 0; i < n; i++) {
      if (update[i] > est[i]) {
        ts[i].updateEdgeFind(store.level, update[i]);
      }
    }
  }
}
