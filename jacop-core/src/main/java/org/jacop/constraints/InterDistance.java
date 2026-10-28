/*
 * InterDistance.java
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * InterDistance constraint: |x[i] - x[j]| &gt;= p for every pair i &lt; j. It models n tasks of the
 * same length p on one machine, x[i] being the start of task i; with p = 1 it is alldifferent.
 *
 * <p>The propagator is bounds(Z) consistent. It implements the algorithm of C.-G. Quimper, A.
 * L&oacute;pez-Ortiz and G. Pesant, "A quadratic propagator for the inter-distance constraint",
 * AAAI 2006, which improves the cubic one of K. Artiouchine and P. Baptiste, "Inter-distance
 * constraint: an extension of the all-different constraint for scheduling equal length jobs", CP
 * 2005. A pass computes the forbidden regions of M. R. Garey, D. S. Johnson, B. B. Simons and R. E.
 * Tarjan (start times no task can take in a feasible schedule), then, for every deadline, the chain
 * of non-dominated release times and its internal adjustment intervals (valid for every task) and
 * external ones (valid for the tasks outside the set, those with a later deadline). A minimum moves
 * to the first value from it outside the forbidden regions, the internal intervals and the external
 * intervals of earlier deadlines. Maximums are pruned on the mirrored problem. The number of
 * intervals is O(n^2) and a pass costs O(n^2 log n).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class InterDistance extends Constraint implements SatisfiedPresent, Copyable<InterDistance> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final long INF = Long.MAX_VALUE / 4;

  /** The start times. */
  final IntVar[] x;

  /** The minimal distance between any two start times, the length of every task. */
  final int p;

  final int n;

  /** True when a variable occurs twice, which fails for p &gt; 0. */
  private final boolean repeated;

  // the task bounds of one pass: release r (the earliest start) and deadline d (latest end)
  private final long[] r;
  private final long[] d;
  private final long[] newLo;

  // tasks sorted by release and by deadline, kept between calls so insertion sort is cheap
  private final int[] byRelease;
  private final int[] byDeadline;

  // the tasks that are not fixed: original index, release, deadline, orders; compact index or -1
  private final int[] task;
  private final long[] tr;
  private final long[] td;
  private final int[] tByRelease;
  private final int[] tByDeadline;
  private final int[] compact;
  private int nt;

  // distinct releases and deadlines; the index of the release and the deadline of every task
  private final long[] rel;
  private final long[] dl;
  private final int[] relOf;
  private final int[] dlOf;
  private int nr;
  private int nd;

  // the first position in byRelease of every distinct release, tasks with deadline at most dl[k]
  private final int[] relFirst;
  private final int[] dlCount;

  // forbidden regions fa[k]..fb[k], increasing and not touching
  private long[] fa;
  private long[] fb;
  private int nf;

  // ect[k][q]: earliest end of q tasks from release rel[k]; lst[k][q]: latest start of q tasks
  // ending by deadline dl[k]
  private long[][] ect;
  private long[][] lst;

  // the chain of one deadline: releases and the number of tasks from each
  private final int[] chainRel;
  private final int[] chainCount;

  // the adjustment intervals: internal ones first, then the external ones by deadline
  private long[] ia = new long[16];
  private long[] ib = new long[16];
  private int ni;
  private int[] externalStart;

  // the coordinates of the interval ends and the releases, and the union-find over their segments
  private long[] coords = new long[16];
  private int[] skip = new int[16];
  private int nc;

  /**
   * It constructs inter_distance(x, p): |x[i] - x[j]| &gt;= p for i != j.
   *
   * @param x the start times.
   * @param p the minimal distance between two start times, at least 0.
   */
  public InterDistance(IntVar[] x, int p) {

    checkInputForNullness("x", x);
    if (p < 0) {
      throw new IllegalArgumentException(
          "InterDistance: the distance must be at least 0, not " + p);
    }

    this.numberId = idNumber.incrementAndGet();
    this.n = x.length;
    this.x = Arrays.copyOf(x, n);
    this.p = p;
    this.repeated = new HashSet<>(Arrays.asList(x)).size() < n;

    r = new long[n];
    d = new long[n];
    newLo = new long[n];
    byRelease = new int[n];
    byDeadline = new int[n];
    for (int i = 0; i < n; i++) {
      byRelease[i] = i;
      byDeadline[i] = i;
    }
    task = new int[n];
    tr = new long[n];
    td = new long[n];
    tByRelease = new int[n];
    tByDeadline = new int[n];
    compact = new int[n];
    rel = new long[n];
    dl = new long[n];
    relOf = new int[n];
    dlOf = new int[n];
    relFirst = new int[n];
    dlCount = new int[n];
    fa = new long[2 * n + 1];
    fb = new long[2 * n + 1];
    chainRel = new int[n];
    chainCount = new int[n];
    externalStart = new int[n + 1];

    this.queueIndex = 2;

    setScope(this.x);
  }

  /**
   * It constructs inter_distance(x, p): |x[i] - x[j]| &gt;= p for i != j.
   *
   * @param x the start times.
   * @param p the minimal distance between two start times, at least 0.
   */
  public InterDistance(List<? extends IntVar> x, int p) {
    this(x.toArray(new IntVar[0]), p);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {
    if (p == 0 || n < 2) {
      return;
    }
    if (repeated) {
      throw Store.failException;
    }
    if (ect == null) {
      ect = new long[n][n + 1];
      lst = new long[n][n + 2];
    }
    // one pass makes every bound supported in the box it read; a bound that moves onto a hole
    // changes the box, so passes repeat until the bounds stay where the pass put them
    boolean again;
    do {
      again = false;
      for (int i = 0; i < n; i++) {
        r[i] = x[i].min();
        d[i] = (long) x[i].max() + p;
      }
      if (!lower()) {
        throw Store.failException;
      }
      for (int i = 0; i < n; i++) {
        if (newLo[i] > x[i].max()) {
          throw Store.failException;
        }
        x[i].domain.inMin(store.level, x[i], (int) newLo[i]);
        again |= x[i].min() != newLo[i];
      }
      // the mirrored problem: x' = -x - p
      for (int i = 0; i < n; i++) {
        r[i] = -(long) x[i].max() - p;
        d[i] = -(long) x[i].min();
      }
      if (!lower()) {
        throw Store.failException;
      }
      for (int i = 0; i < n; i++) {
        long hi = -newLo[i] - p;
        if (hi < x[i].min()) {
          throw Store.failException;
        }
        x[i].domain.inMax(store.level, x[i], (int) hi);
        again |= x[i].max() != hi;
      }
    } while (again);
    removeCompulsoryParts(store);
  }

  /**
   * A task whose start interval lo..hi is shorter than 2p - 1 makes hi - p + 1..lo + p - 1
   * unavailable to every other task, as the pairwise distance constraints do. The bounds are
   * supported, so this only makes holes.
   */
  private void removeCompulsoryParts(Store store) {
    for (int i = 0; i < n; i++) {
      long a = (long) x[i].max() - p + 1;
      long b = (long) x[i].min() + p - 1;
      if (a > b) {
        continue;
      }
      for (int j = 0; j < n; j++) {
        if (j != i && x[j].max() >= a && x[j].min() <= b) {
          x[j].domain.inComplement(
              store.level, x[j], (int) Math.max(a, x[j].min()), (int) Math.min(b, x[j].max()));
        }
      }
    }
  }

  /**
   * The smallest supported release of every task, in newLo; false when no schedule exists. A fixed
   * task at v is taken out: it makes v - p + 1..v + p - 1 a forbidden region for the others.
   *
   * @return false if the tasks cannot be scheduled.
   */
  private boolean lower() {
    insertionSort(byRelease, r);
    insertionSort(byDeadline, d);
    nf = 0;
    nt = 0;
    long last = -INF;
    for (int k = 0; k < n; k++) {
      int i = byRelease[k];
      newLo[i] = r[i];
      if (d[i] - p == r[i]) {
        if (r[i] - last < p) {
          return false;
        }
        last = r[i];
        insertForbidden(r[i] - p + 1, r[i] + p - 1);
        compact[i] = -1;
      } else {
        compact[i] = nt;
        task[nt] = i;
        tr[nt] = r[i];
        td[nt] = d[i];
        tByRelease[nt] = nt;
        nt++;
      }
    }
    if (nt == 0) {
      return true;
    }
    for (int k = 0, j = 0; k < n; k++) {
      int c = compact[byDeadline[k]];
      if (c >= 0) {
        tByDeadline[j++] = c;
      }
    }
    distinctValues();
    if (!forbiddenRegions()) {
      return false;
    }
    tables();
    intervals();
    adjust();
    return true;
  }

  private void distinctValues() {
    nr = 0;
    for (int k = 0; k < nt; k++) {
      int i = tByRelease[k];
      if (nr == 0 || rel[nr - 1] != tr[i]) {
        rel[nr] = tr[i];
        relFirst[nr] = k;
        nr++;
      }
      relOf[i] = nr - 1;
    }
    nd = 0;
    for (int k = 0; k < nt; k++) {
      int i = tByDeadline[k];
      if (nd == 0 || dl[nd - 1] != td[i]) {
        dl[nd] = td[i];
        nd++;
      }
      dlOf[i] = nd - 1;
      dlCount[nd - 1] = k + 1;
    }
  }

  private static void insertionSort(int[] order, long[] key) {
    for (int k = 1; k < order.length; k++) {
      int i = order[k];
      long v = key[i];
      int j = k - 1;
      while (j >= 0 && key[order[j]] > v) {
        order[j + 1] = order[j];
        j--;
      }
      order[j + 1] = i;
    }
  }

  /** It adds a..b to the forbidden regions, merging it with the regions it touches. */
  private void insertForbidden(long a, long b) {
    int k = 0;
    while (k < nf && fb[k] < a - 1) {
      k++;
    }
    int j = k;
    while (j < nf && fa[j] <= b + 1) {
      a = Math.min(a, fa[j]);
      b = Math.max(b, fb[j]);
      j++;
    }
    // regions k..j-1 are replaced by one
    int shift = 1 - (j - k);
    if (shift != 0) {
      System.arraycopy(fa, j, fa, j + shift, nf - j);
      System.arraycopy(fb, j, fb, j + shift, nf - j);
      nf += shift;
    }
    fa[k] = a;
    fb[k] = b;
  }

  /**
   * The forbidden regions of Garey, Johnson, Simons and Tarjan. For every release r, from the
   * largest, the tasks released at r or later are scheduled as late as possible avoiding the
   * regions found so far; if the first of them starts at c &lt; r + p, no task can start after the
   * latest free start up to c - p and before r.
   *
   * @return false if some release cannot fit its tasks.
   */
  private boolean forbiddenRegions() {
    for (int k = nr - 1; k >= 0; k--) {
      long release = rel[k];
      long t = INF;
      int f = nf - 1;
      for (int j = nt - 1; j >= 0; j--) {
        int i = tByDeadline[j];
        if (tr[i] >= release) {
          t = Math.min(t, td[i]) - p;
          while (f >= 0 && fa[f] > t) {
            f--;
          }
          if (f >= 0 && fb[f] >= t) {
            t = fa[f] - 1;
            f--;
          }
        }
      }
      if (t < release) {
        return false;
      }
      if (t < release + p) {
        long s = t - p;
        while (f >= 0 && fa[f] > s) {
          f--;
        }
        if (f >= 0 && fb[f] >= s) {
          s = fa[f] - 1;
        }
        if (s + 1 <= release - 1) {
          insertForbidden(s + 1, release - 1);
        }
      }
    }
    return true;
  }

  /** The earliest ends from every release and the latest starts before every deadline. */
  private void tables() {
    for (int k = 0; k < nr; k++) {
      long[] row = ect[k];
      long t = rel[k];
      row[0] = t;
      int f = 0;
      for (int q = 1, m = nt - relFirst[k]; q <= m; q++) {
        while (f < nf && fb[f] < t) {
          f++;
        }
        if (f < nf && fa[f] <= t) {
          t = fb[f] + 1;
          f++;
        }
        t += p;
        row[q] = t;
      }
    }
    for (int k = 0; k < nd; k++) {
      long[] row = lst[k];
      long t = dl[k];
      row[0] = t;
      int f = nf - 1;
      for (int q = 1, m = dlCount[k] + 1; q <= m; q++) {
        t -= p;
        while (f >= 0 && fa[f] > t) {
          f--;
        }
        if (f >= 0 && fb[f] >= t) {
          t = fa[f] - 1;
          f--;
        }
        row[q] = t;
      }
    }
  }

  /**
   * The adjustment intervals. For a deadline, the chain of releases goes up the releases of the
   * tasks with that deadline or an earlier one; a release dominates the one it follows on the
   * smaller numbers of tasks once the extra tasks of the earlier release can end by it, and it is
   * dominated otherwise (Quimper et al., lemmas 9 and 10). The internal interval of a release r and
   * q tasks after a task is lst(d, q + 1) + 1 .. ect(r, m - q) - 1, with m the number of tasks in
   * [r, d]; the external interval, for a task outside them, starts at lst(d, q + 2) + 1. Intervals
   * below every release cannot move a release and are left out.
   */
  private void intervals() {
    ni = 0;
    for (int f = 0; f < nf; f++) {
      addInterval(fa[f], fb[f]);
    }
    for (int k = 0; k < nd; k++) {
      int len = chain(k);
      for (int c = 0; c < len; c++) {
        long[] e = ect[chainRel[c]];
        int m = chainCount[c];
        int qFrom = c + 1 < len ? chainCount[c + 1] : 0;
        for (int q = qFrom; q < m; q++) {
          addInterval(lst[k][q + 1] + 1, e[m - q] - 1);
        }
      }
    }
    for (int k = 0; k < nd; k++) {
      externalStart[k] = ni;
      int len = chain(k);
      for (int c = 0; c < len; c++) {
        long[] e = ect[chainRel[c]];
        int m = chainCount[c];
        int qFrom = c + 1 < len ? chainCount[c + 1] : 0;
        for (int q = qFrom; q < m; q++) {
          addInterval(lst[k][q + 2] + 1, e[m - q] - 1);
        }
      }
    }
    externalStart[nd] = ni;
  }

  /**
   * The chain of non-dominated releases for deadline dl[k], in chainRel and chainCount.
   *
   * @param k the index of the deadline.
   * @return the length of the chain.
   */
  private int chain(int k) {
    int total = dlCount[k];
    int len = 0;
    int seen = 0;
    long last = INF;
    for (int j = 0; j < nt && seen < total; j++) {
      int i = tByRelease[j];
      if (dlOf[i] > k) {
        continue;
      }
      if (tr[i] != last) {
        last = tr[i];
        int count = total - seen;
        if (len == 0) {
          chainRel[len] = relOf[i];
          chainCount[len] = count;
          len++;
        } else {
          int l = len - 1;
          if (ect[chainRel[l]][chainCount[l] - count] <= tr[i]) {
            chainRel[len] = relOf[i];
            chainCount[len] = count;
            len++;
          }
        }
      }
      seen++;
    }
    return len;
  }

  private void addInterval(long a, long b) {
    if (a > b || b < rel[0]) {
      return;
    }
    if (ni == ia.length) {
      ia = Arrays.copyOf(ia, 2 * ni);
      ib = Arrays.copyOf(ib, 2 * ni);
    }
    ia[ni] = a;
    ib[ni] = b;
    ni++;
  }

  /**
   * The new releases: tasks by increasing deadline, each after the internal intervals and the
   * external intervals of the earlier deadlines.
   */
  private void adjust() {
    int need = 2 * ni + nt;
    if (coords.length < need) {
      coords = new long[need];
      skip = new int[need + 1];
    }
    nc = 0;
    for (int k = 0; k < ni; k++) {
      coords[nc++] = ia[k];
      coords[nc++] = ib[k] + 1;
    }
    for (int i = 0; i < nt; i++) {
      coords[nc++] = tr[i];
    }
    Arrays.sort(coords, 0, nc);
    int u = 0;
    for (int k = 0; k < nc; k++) {
      if (u == 0 || coords[u - 1] != coords[k]) {
        coords[u++] = coords[k];
      }
    }
    nc = u;
    for (int k = 0; k <= nc; k++) {
      skip[k] = k;
    }
    cover(0, externalStart[0]);
    int j = 0;
    for (int k = 0; k < nd; k++) {
      while (j < nt && dlOf[tByDeadline[j]] == k) {
        int i = tByDeadline[j];
        newLo[task[i]] = coords[find(index(tr[i]))];
        j++;
      }
      cover(externalStart[k], externalStart[k + 1]);
    }
  }

  /** It marks the segments of intervals from..to-1 as covered. */
  private void cover(int from, int to) {
    for (int k = from; k < to; k++) {
      int end = index(ib[k] + 1);
      for (int s = find(index(ia[k])); s < end; s = find(s + 1)) {
        skip[s] = s + 1;
      }
    }
  }

  private int index(long v) {
    return Arrays.binarySearch(coords, 0, nc, v);
  }

  /** The first segment from k on that is not covered, with path halving. */
  private int find(int k) {
    while (skip[k] != k) {
      skip[k] = skip[skip[k]];
      k = skip[k];
    }
    return k;
  }

  @Override
  public boolean satisfied() {
    for (int i = 0; i < n; i++) {
      if (!x[i].singleton()) {
        return false;
      }
    }
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (Math.abs((long) x[i].value() - x[j].value()) < p) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : InterDistance([");
    for (int i = 0; i < n; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(x[i]);
    }
    result.append("], ").append(p).append(")");
    return result.toString();
  }

  @Override
  public InterDistance copy(VarMap map) {
    return new InterDistance(map.get(x), p);
  }
}
