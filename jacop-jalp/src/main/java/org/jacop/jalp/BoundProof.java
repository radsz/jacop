/*
 * BoundProof.java
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

package org.jacop.jalp;

import java.util.Arrays;

/**
 * A Farkas proof of infeasibility found by bound propagation over the rows, without a basis. The
 * rows {@code L_i <= a_i x <= U_i} tighten the bounds of their columns from the activity bounds of
 * the others (the feasibility-based bound tightening of the presolve of Achterberg, Bixby, Gu,
 * Rothberg and Weninger, "Presolve reductions in mixed integer programming", INFORMS Journal on
 * Computing 32 (2020) 473-506, section 3.2; Brearley, Mitra and Williams, "Analysis of mathematical
 * programming problems prior to applying the simplex algorithm", Mathematical Programming 8 (1975)
 * 54-83). Each tightening is kept on a trail with the row side it came from. When a row cannot
 * reach its bounds, or a column bound crosses the other, the conflict is resolved backwards along
 * the trail, the way a conflict of propagation is explained: every derived bound the conflict rests
 * on is replaced by the row side that implied it, so that the conflict ends as one combination
 * {@code y A x} of the rows whose range over the given column bounds misses the range of {@code y}
 * times the row bounds. That {@code y} is a Farkas ray, checked from scratch before it is given.
 *
 * <p>Presolves find many infeasible LPs this way (HiGHS proves 13 of the 29 infeasible Netlib LPs
 * in its presolve, this proof 12); a dual simplex needs up to thousands of pivots for them.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class BoundProof {

  // a new bound is kept only when it improves the old one by this much, relative to the range
  private static final double STEP = 1e-3;
  // a derived bound beyond this size is no bound
  private static final double HUGE = 1e10;
  // the conflict must exceed its side by this much, relative
  private static final double CONFLICT = 1e-6;
  // the ray must pass the check of the simplex: the margin, relative to the size of each side
  private static final double MARGIN = 1e-7;
  // the entries of y A below this, relative to the largest, are round-off of the cancellations
  private static final double NOISE = 1e-11;
  // the work of the propagation, in entries visited, at most this many times the nonzeros
  private static final int WORK = 40;

  private final int n;
  private final int m;
  private final int[][] rowIdx;
  private final double[][] rowVal;
  private final int[][] colIdx;
  private final int[] colLen;
  private final double[] boundLo;
  private final double[] boundHi;

  private final double[] lo;
  private final double[] hi;

  // the trail: the column, whether its upper bound changed, the row and its side (upper or not)
  private int[] tCol = new int[64];
  private boolean[] tUpper = new boolean[64];
  private int[] tRow = new int[64];
  private boolean[] tSide = new boolean[64];
  private int trail;
  // the last trail entry of each bound of each column, -1 for a given bound
  private final int[] lastLo;
  private final int[] lastHi;
  // per trail entry, the previous entry of the same bound
  private int[] tPrev = new int[64];

  // the conflict: its row side and the trail position it holds at
  private int conflictRow = -1;
  private boolean conflictSide;
  private int conflictAt;

  private long visited;

  // no ray
  private static final double[] NO_RAY = {};

  /**
   * Prepares the propagation over the internal problem of a simplex: the columns {@code 0..n-1} and
   * the slacks {@code n..n+m-1}, with the bounds {@code boundLo} and {@code boundHi}.
   */
  BoundProof(
      int n,
      int[][] rowIdx,
      double[][] rowVal,
      int[][] colIdx,
      int[] colLen,
      double[] boundLo,
      double[] boundHi) {
    this.n = n;
    this.m = rowIdx.length;
    this.rowIdx = rowIdx;
    this.rowVal = rowVal;
    this.colIdx = colIdx;
    this.colLen = colLen;
    this.boundLo = boundLo;
    this.boundHi = boundHi;
    lo = Arrays.copyOf(boundLo, n);
    hi = Arrays.copyOf(boundHi, n);
    lastLo = new int[n];
    lastHi = new int[n];
    Arrays.fill(lastLo, -1);
    Arrays.fill(lastHi, -1);
  }

  /**
   * Propagates the bounds and, at a conflict, resolves it into a Farkas ray.
   *
   * @return the ray over the rows, {@code y (A x - s)} with a range over the bounds that excludes
   *     zero, or an empty array when the propagation found no conflict or the ray does not hold
   */
  double[] run() {
    long nonzeros = 0;
    for (int i = 0; i < m; i++) {
      nonzeros += rowIdx[i].length;
    }
    long budget = WORK * (nonzeros + n + m);
    int[] queue = new int[m];
    boolean[] queued = new boolean[m];
    int head = 0;
    int size = m;
    for (int i = 0; i < m; i++) {
      queue[i] = i;
      queued[i] = true;
    }
    while (size > 0 && visited < budget) {
      int i = queue[head];
      head = head + 1 == m ? 0 : head + 1;
      size--;
      queued[i] = false;
      if (!propagate(i)) {
        return resolve();
      }
      // the rows of the columns this row tightened
      for (int t = touchedFrom; t < trail; t++) {
        int j = tCol[t];
        int[] ci = colIdx[j];
        visited += colLen[j];
        for (int e = 0; e < colLen[j]; e++) {
          int k = ci[e];
          if (!queued[k] && k < m) {
            queued[k] = true;
            int tail = head + size;
            queue[tail >= m ? tail - m : tail] = k;
            size++;
          }
        }
      }
    }
    return NO_RAY;
  }

  // the first trail entry of the last call of propagate
  private int touchedFrom;

  // tightens the columns of row i from each of its sides; false at a conflict
  private boolean propagate(int i) {
    touchedFrom = trail;
    int[] ri = rowIdx[i];
    double[] rv = rowVal[i];
    visited += 2L * ri.length;
    double rlo = boundLo[n + i];
    double rhi = boundHi[n + i];
    if (rhi < Double.POSITIVE_INFINITY && !side(i, ri, rv, rhi, true)) {
      return false;
    }
    return rlo == Double.NEGATIVE_INFINITY || side(i, ri, rv, -rlo, false);
  }

  // one side of row i as s a x <= b, with s = 1 for the upper side and -1 for the lower one
  private boolean side(int i, int[] ri, double[] rv, double b, boolean upperSide) {
    double s = upperSide ? 1 : -1;
    double min = 0;
    int infinite = 0;
    int infiniteAt = -1;
    double size = Math.abs(b);
    for (int e = 0; e < ri.length; e++) {
      int j = ri[e];
      double a = s * rv[e];
      double v = a > 0 ? lo[j] : hi[j];
      if (Double.isInfinite(v)) {
        infinite++;
        infiniteAt = j;
      } else {
        min += a * v;
        size += Math.abs(a * v);
      }
    }
    if (infinite == 0 && min > b + CONFLICT * (1 + size)) {
      return conflict(i, upperSide);
    }
    if (infinite > 1) {
      return true;
    }
    for (int e = 0; e < ri.length; e++) {
      int j = ri[e];
      double a = s * rv[e];
      if (infinite == 1 && j != infiniteAt) {
        continue;
      }
      // the least activity of the other columns
      double rest = infinite == 1 ? min : min - a * (a > 0 ? lo[j] : hi[j]);
      if (!tighten(i, j, a, (b - rest) / a, size, upperSide)) {
        return false;
      }
    }
    return true;
  }

  // the bound s a x <= b of row i implies on column j (x_j <= bound for a > 0, x_j >= bound
  // otherwise); false at a conflict
  private boolean tighten(int i, int j, double a, double bound, double size, boolean upperSide) {
    if (Math.abs(bound) > HUGE) {
      return true;
    }
    if (a > 0) {
      if (hi[j] == Double.POSITIVE_INFINITY || bound < hi[j] - step(j)) {
        if (bound < lo[j] - CONFLICT * (1 + Math.abs(lo[j]) + size / Math.abs(a))) {
          return conflict(i, upperSide);
        }
        push(j, true, i, upperSide);
        hi[j] = Math.max(bound, lo[j]);
      }
    } else if (lo[j] == Double.NEGATIVE_INFINITY || bound > lo[j] + step(j)) {
      if (bound > hi[j] + CONFLICT * (1 + Math.abs(hi[j]) + size / Math.abs(a))) {
        return conflict(i, upperSide);
      }
      push(j, false, i, upperSide);
      lo[j] = Math.min(bound, hi[j]);
    }
    return true;
  }

  // records a conflict of the side of row i at the end of the trail; false
  private boolean conflict(int i, boolean upperSide) {
    conflictRow = i;
    conflictSide = upperSide;
    conflictAt = trail;
    return false;
  }

  // the least change of a finite bound of column j worth a trail entry
  private double step(int j) {
    double range = hi[j] - lo[j];
    double scale = Double.isInfinite(range) ? Math.min(Math.abs(lo[j]), Math.abs(hi[j])) : range;
    return STEP * Math.max(1, scale);
  }

  private void push(int j, boolean upperBound, int i, boolean upperSide) {
    if (trail == tCol.length) {
      int c = 2 * trail;
      tCol = Arrays.copyOf(tCol, c);
      tUpper = Arrays.copyOf(tUpper, c);
      tRow = Arrays.copyOf(tRow, c);
      tSide = Arrays.copyOf(tSide, c);
      tPrev = Arrays.copyOf(tPrev, c);
    }
    tCol[trail] = j;
    tUpper[trail] = upperBound;
    tRow[trail] = i;
    tSide[trail] = upperSide;
    if (upperBound) {
      tPrev[trail] = lastHi[j];
      lastHi[j] = trail;
    } else {
      tPrev[trail] = lastLo[j];
      lastLo[j] = trail;
    }
    trail++;
  }

  // resolves the conflict backwards along the trail into multipliers of the rows, then checks them
  private double[] resolve() {
    double[] g = new double[n];
    double[] y = new double[m];
    add(g, y, conflictRow, conflictSide, 1);
    // a column whose new bound would cross the other: its row side, with the other bound, is the
    // conflict (the other bound is on the trail before conflictAt or given)
    for (int t = conflictAt - 1; t >= 0; t--) {
      int j = tCol[t];
      double gj = g[j];
      if (gj == 0 || (gj < 0) != tUpper[t]) {
        continue;
      }
      // the row side s a_r x <= b_r implied this bound: add it so that x_j leaves the combination
      int r = tRow[t];
      double a = (tSide[t] ? 1 : -1) * entry(r, j);
      double lambda = a == 0 ? Double.NaN : -gj / a;
      if (Double.isNaN(lambda) || lambda <= 0 || Double.isInfinite(lambda)) {
        return NO_RAY;
      }
      add(g, y, r, tSide[t], lambda);
      g[j] = 0;
    }
    return holds(y) ? y : NO_RAY;
  }

  // adds lambda times the side of row r, s a_r x <= b_r, to the combination
  private void add(double[] g, double[] y, int r, boolean upperSide, double lambda) {
    double f = upperSide ? lambda : -lambda;
    y[r] += f;
    int[] ri = rowIdx[r];
    double[] rv = rowVal[r];
    visited += ri.length;
    for (int e = 0; e < ri.length; e++) {
      g[ri[e]] += f * rv[e];
    }
  }

  private double entry(int r, int j) {
    int[] ri = rowIdx[r];
    for (int e = 0; e < ri.length; e++) {
      if (ri[e] == j) {
        return rowVal[r][e];
      }
    }
    return 0;
  }

  // the check of the simplex (proofHolds) over all columns: the range of y (A x - s) over the
  // given bounds excludes zero
  boolean holds(double[] y) {
    double[] alpha = new double[n + m];
    double largest = 0;
    for (int i = 0; i < m; i++) {
      double f = y[i];
      if (f == 0) {
        continue;
      }
      int[] ri = rowIdx[i];
      double[] rv = rowVal[i];
      for (int e = 0; e < ri.length; e++) {
        alpha[ri[e]] += f * rv[e];
      }
      alpha[n + i] = -f;
    }
    for (double a : alpha) {
      largest = Math.max(largest, Math.abs(a));
    }
    double noise = NOISE * largest;
    double min = 0;
    double max = 0;
    double sizeMin = 0;
    double sizeMax = 0;
    for (int j = 0; j < n + m; j++) {
      double a = alpha[j];
      if (Math.abs(a) <= noise) {
        continue;
      }
      double l = boundLo[j];
      double h = boundHi[j];
      double low = a > 0 ? a * l : a * h;
      double high = a > 0 ? a * h : a * l;
      min += low;
      max += high;
      sizeMin += Math.abs(low);
      sizeMax += Math.abs(high);
    }
    return min > MARGIN * (1 + sizeMin) || max < -MARGIN * (1 + sizeMax);
  }

  /** Returns the entries visited, for the work count of the simplex. */
  long work() {
    return visited;
  }
}
