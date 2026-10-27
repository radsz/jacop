/*
 * UnaryTransitionExplanation.java
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
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of {@link UnaryTransition} for lazy clause generation. An explanation is found again
 * from the bounds just before the explained atom, in the style of Vilím's explanations of the unary
 * resource and of Schutt, Feydy, Stuckey and Wallace's explanations of the cumulative resource: it
 * looks for the tasks that must precede a task and for a set of them whose energy and transitions
 * push the task's start to the bound, and gives the bounds it used.
 *
 * <p>A bound of a start is explained on the normal view (an earliest start) or on the reversed
 * view, where time runs backwards and a latest completion is an earliest start. Task i starts after
 * a set P of tasks when
 *
 * <ul>
 *   <li>each j of P is one that i cannot precede: ect(i) + t(i, j) &gt; lst(j) (the pairs and
 *       detectable precedences); or
 *   <li>the tasks whose lct is at most some L, with i, cannot all end by L (edge finding): a cut S
 *       of them by est has est(S) + p(S) + tt(|F(S)|) &gt; L, so i ends after every task j whose
 *       lst is at most L, since j starting after i would make S end by L.
 * </ul>
 *
 * <p>The start of i is then at least ect(j) + t(j, i) for one j of P, or est(C) + p(C) +
 * max(tt(|F(C)|) + min t(C, i), tt(|F(C) + f(i)|)) for a cut C of P by est, with tt(k) the lower
 * bound of the transitions among k families of {@link UnaryTransition}. A task that cannot be first
 * among a set S (not-first, the reversed not-last) starts at least min ect(j) + t(j, i) over S:
 * ect(i) + p(S) + max(tt(|F(S)|) + min t(i, S), tt(|F(S) + f(i)|)) &gt; lct(S).
 *
 * <p>Each of these bounds is at least the one the propagator computed on its trees, whose earliest
 * completion times are below the cut bounds by the superadditivity of tt, so every pruning of the
 * rules has an explanation; the search is quadratic in the number of tasks. A removed optional task
 * is one whose start would have no value left, or which would overload a set of tasks; a failure is
 * an overload or a task whose start has no value left.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class UnaryTransitionExplanation {

  // the atoms of a task in a reason
  private static final int S_LO = 1;
  private static final int S_HI = 2;
  private static final int D_LO = 4;
  private static final int D_HI = 8;
  private static final int PRESENT = 16;

  // the bounds of a task in a view, and the atoms each one rests on in the normal view (est = min
  // s, ect = min s + min d, lst = max s, lct = max s + max d) and in the reversed view (est = -(max
  // s + max d), ect = -max s, lst = -(min s + min d), lct = -min s)
  private static final int EST = 0;
  private static final int ECT = 1;
  private static final int LST = 2;
  private static final int LCT = 3;
  private static final int DUR = 4;
  private static final int[][] ATOMS = {
    {S_LO, S_LO | D_LO, S_HI, S_HI | D_HI, D_LO},
    {S_HI | D_HI, S_HI, S_LO | D_LO, S_LO, D_LO}
  };

  // steps of one explanation before it is left to the generic reason
  private static final int WORK_BUDGET = 1 << 22;
  // values checked one by one for holes of a domain
  private static final int HOLE_BUDGET = 4096;

  private static final long INF = Long.MAX_VALUE / 4;

  private final UnaryTransition c;
  private final int n;
  private final int[] fam;
  private final long[] ttk;

  // the bounds just before the explained position
  private final int[] sMin;
  private final int[] sMax;
  private final int[] dMin;
  private final int[] dMax;
  private final boolean[] present;

  // the current view: 0 normal, 1 reversed; the tasks in it by decreasing est and increasing lct
  private int view;
  private final long[] est;
  private final long[] ect;
  private final long[] lst;
  private final long[] lct;
  private final long[] dur;
  private final int[] byEst;
  private final int[] byLct;
  private int count;

  // the atoms of each task in the reason, and the ranges of values whose removal it uses
  private final int[] atoms;
  private final IntVar[] holeVar = new IntVar[2];
  private final int[] holeFrom = new int[2];
  private final int[] holeTo = new int[2];
  private int holes;

  // scratch
  private final boolean[] pred;
  private final int[] list;
  private final int[] famMark;
  private int famStamp;
  private int work;
  private final EntryList scratch = new EntryList();

  UnaryTransitionExplanation(UnaryTransition c, int[] fam, long[] ttk) {
    this.c = c;
    this.n = c.starts.length;
    this.fam = fam;
    this.ttk = ttk;
    sMin = new int[n];
    sMax = new int[n];
    dMin = new int[n];
    dMax = new int[n];
    present = new boolean[n];
    est = new long[n];
    ect = new long[n];
    lst = new long[n];
    lct = new long[n];
    dur = new long[n];
    byEst = new int[n];
    byLct = new int[n];
    atoms = new int[n];
    pred = new boolean[n];
    list = new int[n];
    famMark = new int[ttk.length];
  }

  /**
   * Explains a bound of a start, a bound of a duration or the absence of an optional task.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param out where the reason entries are added
   * @return false when no reason was found
   */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return false;
    }
    IntVar y = trail.variable(entry);
    int role = -1;
    int i = -1;
    int found = 0;
    for (int k = 0; k < n; k++) {
      if (c.starts[k] == y) {
        role = 0;
        i = k;
        found++;
      }
      if (c.durations[k] == y) {
        role = 1;
        i = k;
        found++;
      }
      if (c.optional != null && c.optional[k] == y) {
        role = 2;
        i = k;
        found++;
      }
    }
    if (found != 1) {
      return false;
    }
    start(trail, entry);
    int v = trail.value(entry);
    boolean ok;
    if (role == 0) {
      ok =
          present[i]
              && (kind == AtomicTrail.GE
                  ? startAbove(trail, entry, i, v)
                  : startBelow(trail, entry, i, v));
      atoms[i] |= PRESENT;
    } else if (role == 1) {
      ok = kind == AtomicTrail.LE && present[i] && durationBelow(trail, entry, i, v);
      atoms[i] |= PRESENT;
    } else {
      ok = kind == AtomicTrail.LE && v <= 0 && !present[i] && absent(i);
    }
    if (!ok) {
      return false;
    }
    addAtoms(trail, entry, out);
    return true;
  }

  /**
   * Explains a failure: a set of present tasks that overloads, or a present task whose start has no
   * value left.
   *
   * @param trail the trail
   * @param out where the reason entries are added
   * @return false when no reason was found
   */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    int position = trail.size();
    start(trail, position);
    boolean ok = overload();
    for (int i = 0; i < n && !ok; i++) {
      if (present[i]) {
        ok = absent(i);
        if (ok) {
          atoms[i] |= PRESENT;
        }
      }
    }
    if (!ok) {
      return false;
    }
    addAtoms(trail, position, out);
    return true;
  }

  // ---- what is explained ----

  // [s_i >= v]: the values from the computed bound to v were already out of the domain
  private boolean startAbove(AtomicTrail trail, int entry, int i, int v) {
    IntVar s = c.starts[i];
    int u = v;
    for (int b = 0; b < HOLE_BUDGET && u - 1 > sMin[i] && excluded(trail, s, u - 1, entry); b++) {
      u--;
    }
    setView(0, i);
    if (!lowerBound(i, u)) {
      return false;
    }
    hole(s, u, v - 1);
    return true;
  }

  // [s_i <= v], on the reversed view: -(s_i + d_i) >= -(u + min d_i)
  private boolean startBelow(AtomicTrail trail, int entry, int i, int v) {
    IntVar s = c.starts[i];
    int u = v;
    for (int b = 0; b < HOLE_BUDGET && u + 1 < sMax[i] && excluded(trail, s, u + 1, entry); b++) {
      u++;
    }
    setView(1, i);
    if (!lowerBound(i, -(long) u - dMin[i])) {
      return false;
    }
    atoms[i] |= D_LO;
    hole(s, v + 1, u);
    return true;
  }

  // [d_i <= v]: a task j that i precedes starts by max s_j, at least the transition after i ends
  private boolean durationBelow(AtomicTrail trail, int entry, int i, int v) {
    IntVar d = c.durations[i];
    int u = v;
    for (int b = 0; b < HOLE_BUDGET && u + 1 < dMax[i] && excluded(trail, d, u + 1, entry); b++) {
      u++;
    }
    for (int j = 0; j < n; j++) {
      if (j != i
          && present[j]
          && (long) sMin[j] + dMin[j] + c.transition(j, i) > sMax[i]
          && (long) sMax[j] - sMin[i] - c.transition(i, j) <= u) {
        atoms[i] |= S_LO | S_HI;
        atoms[j] |= S_LO | D_LO | S_HI | PRESENT;
        hole(d, v + 1, u);
        return true;
      }
    }
    return false;
  }

  // task i, taken as present, has no start left or overloads a set of present tasks
  private boolean absent(int i) {
    setView(0, i);
    if (lowerBound(i, (long) sMax[i] + 1)) {
      atoms[i] |= S_HI;
      return true;
    }
    if (overloadWith(i)) {
      return true;
    }
    setView(1, i);
    if (lowerBound(i, -((long) sMin[i] + dMin[i]) + 1)) {
      atoms[i] |= S_LO | D_LO;
      return true;
    }
    return false;
  }

  // ---- the rules ----

  /**
   * Finds why task i, taken as present, cannot start before target in the current view, and marks
   * the bounds the reason rests on.
   */
  private boolean lowerBound(int i, long target) {
    if (est[i] >= target) {
      mark(i, EST);
      return true;
    }
    // the tasks i cannot precede
    for (int k = 0; k < count; k++) {
      int j = byEst[k];
      pred[j] = j != i && ect[i] + t(i, j) > lst[j];
      if (pred[j] && ect[j] + t(j, i) >= target) {
        mark(i, ECT);
        mark(j, LST);
        mark(j, ECT);
        return true;
      }
    }
    if (!spend(count)) {
      return false;
    }
    if (cut(i, target, Long.MIN_VALUE) != 0 || notFirst(i, target)) {
      return true;
    }
    // edge finding, over the lct of the other tasks
    for (int k = 0; k < count; k++) {
      int j = byLct[k];
      if (j == i || k + 1 < count && lct[byLct[k + 1]] == lct[j] && byLct[k + 1] != i) {
        continue;
      }
      if (!spend(3 * count)) {
        return false;
      }
      long limit = lct[j];
      int at = detect(i, limit, true);
      if (at < 0) {
        continue;
      }
      int result = cut(i, target, limit);
      if (result != 0) {
        if (result == 2) {
          markDetection(i, limit, at, true);
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Finds a task or a cut by est of the tasks that i cannot precede, or whose lst is at most limit
   * (after an edge-finding detection at limit), that ends with its transition to i at target or
   * later. Returns 0 when there is none, 1 when it uses only the pairs, 2 when it uses the
   * detection too.
   */
  private int cut(int i, long target, long limit) {
    famStamp++;
    int families = 0;
    boolean famI = false;
    long p = 0;
    long minIn = INF;
    for (int k = 0; k < count; k++) {
      int j = byEst[k];
      if (j == i || !pred[j] && lst[j] > limit) {
        continue;
      }
      if (ect[j] + t(j, i) >= target) {
        mark(j, ECT);
        return justify(i, j);
      }
      p += dur[j];
      if (famMark[fam[j]] != famStamp) {
        famMark[fam[j]] = famStamp;
        families++;
        famI |= fam[j] == fam[i];
      }
      minIn = Math.min(minIn, t(j, i));
      long chain = Math.max(tt(families) + minIn, tt(families + (famI ? 0 : 1)));
      if (est[j] + p + chain >= target) {
        int result = 1;
        for (int m = 0; m <= k; m++) {
          int x = byEst[m];
          if (x != i && (pred[x] || lst[x] <= limit)) {
            mark(x, EST);
            mark(x, DUR);
            result = Math.max(result, justify(i, x));
          }
        }
        return result;
      }
    }
    return 0;
  }

  // marks why task j precedes i: a pair, or the detection the caller marks
  private int justify(int i, int j) {
    mark(j, LST);
    if (pred[j]) {
      mark(i, ECT);
      return 1;
    }
    return 2;
  }

  /**
   * Not-first: task i cannot precede all of a set S of tasks, a prefix by lct of those that would
   * give the bound, so one of them precedes it.
   */
  private boolean notFirst(int i, long target) {
    int m = 0;
    for (int k = 0; k < count; k++) {
      int j = byLct[k];
      if (j != i && ect[j] + t(j, i) >= target) {
        list[m++] = j;
      }
    }
    famStamp++;
    int families = 0;
    boolean famI = false;
    long p = 0;
    long minOut = INF;
    for (int k = 0; k < m; k++) {
      int j = list[k];
      p += dur[j];
      if (famMark[fam[j]] != famStamp) {
        famMark[fam[j]] = famStamp;
        families++;
        famI |= fam[j] == fam[i];
      }
      minOut = Math.min(minOut, t(i, j));
      long chain = Math.max(tt(families) + minOut, tt(families + (famI ? 0 : 1)));
      if (ect[i] + p + chain > lct[j]) {
        mark(i, ECT);
        for (int q = 0; q <= k; q++) {
          mark(list[q], DUR);
          mark(list[q], LCT);
          mark(list[q], ECT);
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Finds a cut by est of the tasks other than i whose lct is at most limit, with i when withI,
   * that cannot end by limit. Returns the position in est order where the cut ends, or -1.
   */
  private int detect(int i, long limit, boolean withI) {
    famStamp++;
    int families = 0;
    long p = 0;
    for (int k = 0; k < count; k++) {
      int j = byEst[k];
      if (j == i ? !withI : lct[j] > limit) {
        continue;
      }
      p += dur[j];
      if (famMark[fam[j]] != famStamp) {
        famMark[fam[j]] = famStamp;
        families++;
      }
      if (est[j] + p + tt(families) > limit) {
        return k;
      }
    }
    return -1;
  }

  private void markDetection(int i, long limit, int at, boolean withI) {
    for (int k = 0; k <= at; k++) {
      int j = byEst[k];
      if (j == i) {
        if (withI) {
          mark(j, EST);
          mark(j, DUR);
        }
      } else if (lct[j] <= limit) {
        mark(j, EST);
        mark(j, DUR);
        mark(j, LCT);
      }
    }
  }

  // a set of present tasks with i cannot end by its largest lct
  private boolean overloadWith(int i) {
    for (int k = 0; k < count; k++) {
      long limit = lct[byLct[k]];
      if (limit < lct[i] || !spend(count)) {
        continue;
      }
      int at = detect(i, limit, true);
      if (at >= 0) {
        markDetection(i, limit, at, true);
        mark(i, LCT);
        return true;
      }
    }
    return false;
  }

  // a set of present tasks cannot end by its largest lct
  private boolean overload() {
    setView(0, -1);
    for (int k = 0; k < count; k++) {
      long limit = lct[byLct[k]];
      if (!spend(count)) {
        return false;
      }
      int at = detect(-1, limit, false);
      if (at >= 0) {
        markDetection(-1, limit, at, false);
        return true;
      }
    }
    return false;
  }

  // ---- views, bounds and atoms ----

  private void start(AtomicTrail trail, int position) {
    for (int i = 0; i < n; i++) {
      sMin[i] = trail.minBefore(c.starts[i], position);
      sMax[i] = trail.maxBefore(c.starts[i], position);
      dMin[i] = trail.minBefore(c.durations[i], position);
      dMax[i] = trail.maxBefore(c.durations[i], position);
      present[i] = c.optional == null || trail.minBefore(c.optional[i], position) >= 1;
    }
    Arrays.fill(atoms, 0);
    holes = 0;
    work = WORK_BUDGET;
  }

  // loads the present tasks, and task focus, into a view
  private void setView(int v, int focus) {
    view = v;
    count = 0;
    for (int i = 0; i < n; i++) {
      if (!present[i] && i != focus) {
        continue;
      }
      if (v == 0) {
        est[i] = sMin[i];
        ect[i] = (long) sMin[i] + dMin[i];
        lst[i] = sMax[i];
        lct[i] = (long) sMax[i] + dMax[i];
      } else {
        est[i] = -((long) sMax[i] + dMax[i]);
        ect[i] = -(long) sMax[i];
        lst[i] = -((long) sMin[i] + dMin[i]);
        lct[i] = -(long) sMin[i];
      }
      dur[i] = dMin[i];
      byEst[count] = i;
      byLct[count] = i;
      count++;
    }
    spend(count * count);
    // by decreasing est and by increasing lct
    for (int a = 1; a < count; a++) {
      int x = byEst[a];
      int b = a - 1;
      while (b >= 0 && est[byEst[b]] < est[x]) {
        byEst[b + 1] = byEst[b];
        b--;
      }
      byEst[b + 1] = x;
      x = byLct[a];
      b = a - 1;
      while (b >= 0 && lct[byLct[b]] > lct[x]) {
        byLct[b + 1] = byLct[b];
        b--;
      }
      byLct[b + 1] = x;
    }
  }

  // the transition from task a to task b in the current view
  private long t(int a, int b) {
    return view == 0 ? c.transition(a, b) : c.transition(b, a);
  }

  private long tt(int k) {
    return ttk[Math.min(k, ttk.length - 1)];
  }

  private void mark(int i, int bound) {
    atoms[i] |= ATOMS[view][bound] | PRESENT;
  }

  private boolean spend(int steps) {
    work -= steps;
    return work >= 0;
  }

  private boolean excluded(AtomicTrail trail, IntVar x, int value, int position) {
    scratch.clear();
    return trail.excludedBefore(x, value, position, scratch);
  }

  private void hole(IntVar x, int from, int to) {
    if (from <= to) {
      holeVar[holes] = x;
      holeFrom[holes] = from;
      holeTo[holes] = to;
      holes++;
    }
  }

  private void addAtoms(AtomicTrail trail, int position, EntryList out) {
    for (int i = 0; i < n; i++) {
      int a = atoms[i];
      if ((a & S_LO) != 0) {
        trail.addLowerBound(c.starts[i], position, out);
      }
      if ((a & S_HI) != 0) {
        trail.addUpperBound(c.starts[i], position, out);
      }
      if ((a & D_LO) != 0) {
        trail.addLowerBound(c.durations[i], position, out);
      }
      if ((a & D_HI) != 0) {
        trail.addUpperBound(c.durations[i], position, out);
      }
      if ((a & PRESENT) != 0 && c.optional != null) {
        trail.addLowerBound(c.optional[i], position, out);
      }
    }
    for (int h = 0; h < holes; h++) {
      for (int value = holeFrom[h]; value <= holeTo[h]; value++) {
        trail.excludedBefore(holeVar[h], value, position, out);
      }
    }
  }
}
