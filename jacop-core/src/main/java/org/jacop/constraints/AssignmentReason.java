/*
 * AssignmentReason.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of the assignment relaxation of {@link CircuitCost} and {@link SubcircuitCost} for
 * lazy clause generation, by reduced costs. The minimum cost assignment of the variables to
 * distinct values over the domains just before the explained atom is solved again (Hungarian
 * method), and its duals u, v bound the cost of every assignment by u + v as long as every arc in
 * the domains keeps a reduced cost c(i, j) - u(i) - v(j) of at least zero. Only the arcs already
 * removed whose reduced cost is negative must stay removed, so the reason cites just those, with
 * the bound of the cost the pruning compared against. An arc forced into the assignment adds its
 * reduced cost to the bound. This is the reduced cost reasoning of F. Focacci, A. Lodi and M.
 * Milano, "Cost-based domain filtering", CP 1999, LNCS 1713, 189-203, turned into explanations as
 * for linear relaxations in lazy clause generation (G. Gange, J. Berg, E. Demirović and P. J.
 * Stuckey, "Core-guided and core-boosted search for CP", CPAIOR 2020, uses the same reduced cost
 * reasons). The maximum assignment explains upper bounds of the cost the same way.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class AssignmentReason {

  // far above any assignment cost of int arc costs, far below an overflow
  private static final long BIG = 1L << 50;

  private final IntVar[] x;
  private final int[][] costs;
  private final IntVar cost;
  private final int offset;
  private final boolean selfLoops;
  private final int n;

  // the duals and the matching of each direction (index 0 minimum, 1 maximum) are kept from one
  // explanation to the next, so that each solve only repairs them (warm start)
  private static final long DRIFT_LIMIT = 1L << 56;
  private final long[][] rowDuals;
  private final long[][] columnDuals;
  private final int[][] mates;

  // the arcs and weights of each direction, for the position solved last in that direction
  private final boolean[][][] allowedOf;
  private final long[][][] weightOf;
  private final int[] solvedPosition = {-1, -1};
  private final int[] solvedEpoch = new int[2];
  private final boolean[] solvedOk = new boolean[2];
  private final boolean[] changed;
  // the entries citeRemoved cites for each direction and row, valid while citedValid
  private final EntryList[][] cited;
  private final boolean[][] citedValid;

  private boolean[][] allowed;
  private long[][] weight;
  private long[] u;
  private long[] v;
  private int[] p;
  private final int[] way;
  private final long[] minv;
  private final boolean[] used;

  /**
   * Explanations for x forming an assignment of cost cost.
   *
   * @param x the successor variables
   * @param costs costs[i][j] is the cost of x[i] = j + offset
   * @param cost the cost variable
   * @param offset the value of the first variable
   * @param selfLoops whether x[i] = i + offset is allowed (a subcircuit), else never (a circuit)
   */
  AssignmentReason(IntVar[] x, int[][] costs, IntVar cost, int offset, boolean selfLoops) {
    this.x = x;
    this.costs = costs;
    this.cost = cost;
    this.offset = offset;
    this.selfLoops = selfLoops;
    this.n = x.length;
    allowedOf = new boolean[2][n][n];
    weightOf = new long[2][n + 1][n + 1];
    changed = new boolean[n];
    cited = new EntryList[2][n];
    citedValid = new boolean[2][n];
    for (EntryList[] rows : cited) {
      for (int i = 0; i < n; i++) {
        rows[i] = new EntryList();
      }
    }
    rowDuals = new long[2][n + 1];
    columnDuals = new long[2][n + 1];
    mates = new int[2][n + 1];
    way = new int[n + 1];
    minv = new long[n + 1];
    used = new boolean[n + 1];
  }

  /**
   * Explains an atom on the cost or on a successor.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param out where the reason is added
   * @return false when neither assignment explains it
   */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    if (y == cost) {
      if (kind == AtomicTrail.NE || occursInX(y)) {
        return false;
      }
      boolean lower = kind == AtomicTrail.GE;
      // cost >= bound by the minimum assignment, cost <= bound by the maximum one
      long sign = lower ? 1 : -1;
      if (!solve(trail, entry, sign)) {
        return false;
      }
      long bound = sign * dualSum();
      int value = trail.value(entry);
      if (lower ? bound < value : bound > value) {
        int skipped = trail.skippedBound(entry);
        if (lower ? bound < skipped : bound > skipped) {
          return false;
        }
        trail.addSkippedHoles(entry, skipped, out);
      }
      citeRemoved(trail, entry, sign, -1, out);
      return true;
    }
    int i = indexOf(y);
    if (i < 0 || y == cost) {
      return false;
    }
    for (long sign : new long[] {1, -1}) {
      int mark = out.size();
      if (explainArcs(trail, entry, i, sign, out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // the successor values the atom removes all cost too much (sign 1) or too little (sign -1)
  private boolean explainArcs(AtomicTrail trail, int entry, int i, long sign, EntryList out) {
    if (!solve(trail, entry, sign)) {
      return false;
    }
    long dual = dualSum();
    // an arc forced into the assignment is out when dual + its reduced cost exceeds threshold
    long threshold = sign > 0 ? trail.maxBefore(cost, entry) : -(long) trail.minBefore(cost, entry);
    // the least dual + reduced cost over the arcs the atom removes that are out by cost
    long forced = Long.MAX_VALUE;
    for (int j = 0; j < n; j++) {
      if (!covered(trail, entry, i, j)) {
        continue;
      }
      long bound = dual + reduced(i, j, sign);
      if (bound > threshold) {
        forced = Math.min(forced, bound);
      } else if (allowed[i][j]) {
        return false;
      } else {
        // already removed, and it must stay removed
        trail.excludedBefore(x[i], j + offset, entry, out);
      }
    }
    if (forced != Long.MAX_VALUE) {
      // sign 1: cost <= forced - 1; sign -1: cost >= -forced + 1
      trail.addBoundReaching(cost, entry, sign < 0, sign > 0 ? forced - 1 : -forced + 1, out);
    }
    citeRemoved(trail, entry, sign, i, out);
    return true;
  }

  // whether the atom of the entry on x[i] removes the arc (i, j) that the constraint allows
  private boolean covered(AtomicTrail trail, int entry, int i, int j) {
    if (!selfLoops && i == j) {
      return false;
    }
    int w = j + offset;
    int atom = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> w < atom;
      case AtomicTrail.LE -> w > atom;
      default -> w == atom;
    };
  }

  /**
   * Explains a failure: the minimum assignment exceeds the upper bound of the cost, or the maximum
   * one is below its lower bound.
   *
   * @param trail the trail
   * @param out where the reason is added
   * @return false when neither does
   */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (occursInX(cost)) {
      return false;
    }
    int now = trail.size();
    for (long sign : new long[] {1, -1}) {
      if (!solve(trail, now, sign)) {
        continue;
      }
      long bound = sign * dualSum();
      if (sign > 0 ? bound > trail.maxBefore(cost, now) : bound < trail.minBefore(cost, now)) {
        trail.addBoundReaching(cost, now, sign < 0, sign > 0 ? bound - 1 : bound + 1, out);
        citeRemoved(trail, now, sign, -1, out);
        return true;
      }
    }
    return false;
  }

  private boolean occursInX(IntVar y) {
    return indexOf(y) >= 0;
  }

  private int indexOf(IntVar y) {
    int found = -1;
    for (int i = 0; i < n; i++) {
      if (x[i] == y) {
        if (found >= 0) {
          return -2;
        }
        found = i;
      }
    }
    return found < 0 ? -1 : found;
  }

  // the reduced cost of arc (i, j) under the duals, in the direction of the sign
  private long reduced(int i, int j, long sign) {
    return sign * costs[i][j] - u[i + 1] - v[j + 1];
  }

  private long dualSum() {
    long s = 0;
    for (int k = 1; k <= n; k++) {
      s += u[k] + v[k];
    }
    return s;
  }

  // cites every arc that is not in the domains and whose reduced cost is negative, except those
  // of row skip (the explained atom's row, whose arcs are dealt with apart); the entries of each
  // row are kept until a solve in the same direction changes the arcs or the duals
  private void citeRemoved(AtomicTrail trail, int position, long sign, int skip, EntryList out) {
    int s = sign > 0 ? 0 : 1;
    EntryList[] rows = cited[s];
    boolean[] valid = citedValid[s];
    for (int i = 0; i < n; i++) {
      if (valid[i]) {
        continue;
      }
      EntryList row = rows[i];
      row.clear();
      for (int j = 0; j < n; j++) {
        if (!allowed[i][j] && (selfLoops || i != j) && reduced(i, j, sign) < 0) {
          trail.excludedBefore(x[i], j + offset, position, row);
        }
      }
      valid[i] = true;
    }
    for (int i = 0; i < n; i++) {
      if (i == skip) {
        continue;
      }
      EntryList row = rows[i];
      for (int k = 0, size = row.size(); k < size; k++) {
        out.addFrom(row, k);
      }
    }
  }

  // the arcs in the domains just before the position; the optimal assignment of sign * cost over
  // them and its duals; false when there is no assignment. The arcs, the duals and the matching of
  // the previous solve in the same direction are kept: only the rows of the variables with an
  // entry between the two positions are rebuilt and repaired, and only the rows that lost their
  // arc are augmented, at O(n^2) each, instead of solving again in O(n^3). Explanations of one
  // conflict come at nearby positions, so most of them change no row and solve nothing.
  private boolean solve(AtomicTrail trail, int position, long sign) {
    int s = sign > 0 ? 0 : 1;
    u = rowDuals[s];
    v = columnDuals[s];
    p = mates[s];
    allowed = allowedOf[s];
    weight = weightOf[s];
    // after a backtrack every row is rebuilt, but the duals still warm-start the solve
    boolean full = solvedPosition[s] < 0 || solvedEpoch[s] != trail.epoch();
    for (int k = 1; k <= n; k++) {
      if (Math.abs(u[k]) > DRIFT_LIMIT || Math.abs(v[k]) > DRIFT_LIMIT) {
        Arrays.fill(u, 0);
        Arrays.fill(v, 0);
        Arrays.fill(p, 0);
        full = true;
        break;
      }
    }
    int from = Math.min(position, solvedPosition[s]);
    int to = Math.max(position, solvedPosition[s]);
    boolean any = false;
    for (int i = 0; i < n; i++) {
      changed[i] = full || trail.lastEntry(x[i], to) >= from;
      any |= changed[i];
    }
    solvedPosition[s] = position;
    solvedEpoch[s] = trail.epoch();
    if (!any) {
      return solvedOk[s];
    }
    for (int i = 0; i < n; i++) {
      if (changed[i]) {
        row(trail, i, position, sign);
      }
    }
    // the tightest feasible duals of the rebuilt rows; a matched arc stays only while tight
    for (int i = 1; i <= n; i++) {
      if (!changed[i - 1]) {
        continue;
      }
      long min = Long.MAX_VALUE;
      long[] w = weight[i];
      for (int j = 1; j <= n; j++) {
        min = Math.min(min, w[j] - v[j]);
      }
      u[i] = min;
    }
    boolean[] matched = used;
    Arrays.fill(matched, false);
    for (int j = 1; j <= n; j++) {
      int r = p[j];
      if (r != 0 && changed[r - 1] && weight[r][j] - u[r] - v[j] != 0) {
        p[j] = 0;
      } else if (r != 0) {
        matched[r] = true;
      }
    }
    int free = 0;
    for (int i = 1; i <= n; i++) {
      if (!matched[i]) {
        way[free++] = i;
      }
    }
    int[] rows = Arrays.copyOf(way, free);
    // a rebuilt row changes its own reduced costs; an augmentation changes the column duals
    for (int i = 0; i < n; i++) {
      if (free > 0 || changed[i]) {
        citedValid[s][i] = false;
      }
    }
    // Hungarian method with potentials, rows 1..n, columns 1..n, p[j] the row of column j
    p[0] = 0;
    for (int i : rows) {
      p[0] = i;
      int j0 = 0;
      Arrays.fill(minv, Long.MAX_VALUE);
      Arrays.fill(used, false);
      do {
        used[j0] = true;
        int i0 = p[j0];
        long delta = Long.MAX_VALUE;
        int j1 = 0;
        for (int j = 1; j <= n; j++) {
          if (!used[j]) {
            long cur = weight[i0][j] - u[i0] - v[j];
            if (cur < minv[j]) {
              minv[j] = cur;
              way[j] = j0;
            }
            if (minv[j] < delta) {
              delta = minv[j];
              j1 = j;
            }
          }
        }
        for (int j = 0; j <= n; j++) {
          if (used[j]) {
            u[p[j]] += delta;
            v[j] -= delta;
          } else {
            minv[j] -= delta;
          }
        }
        j0 = j1;
      } while (p[j0] != 0);
      do {
        int j1 = way[j0];
        p[j0] = p[j1];
        j0 = j1;
      } while (j0 != 0);
    }
    p[0] = 0;
    v[0] = 0;
    // every row is matched to an arc of the domains; the duals are feasible on every arc
    solvedOk[s] = true;
    for (int j = 1; j <= n; j++) {
      if (!allowed[p[j] - 1][j - 1]) {
        solvedOk[s] = false;
      }
    }
    assert dualsFeasible(sign) : "negative reduced cost";
    return solvedOk[s];
  }

  // the arcs of row i in the domains just before the position, and their weights
  private void row(AtomicTrail trail, int i, int position, long sign) {
    IntVar xi = x[i];
    IntDomain root = trail.rootDomain(xi);
    // the bounds before the position, looked up once per row; a value inside them was in the
    // domain unless it is not in the root domain or an NE entry removed it
    int lo = trail.minBefore(xi, position);
    int hi = trail.maxBefore(xi, position);
    for (int j = 0; j < n; j++) {
      int value = j + offset;
      boolean in =
          (selfLoops || i != j)
              && value >= lo
              && value <= hi
              && root.contains(value)
              && trail.notEqualEntry(xi, value, position) < 0;
      allowed[i][j] = in;
      weight[i + 1][j + 1] = in ? sign * costs[i][j] : BIG;
    }
  }

  private boolean dualsFeasible(long sign) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (allowed[i][j] && reduced(i, j, sign) < 0) {
          return false;
        }
      }
    }
    return true;
  }
}
