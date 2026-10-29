/*
 * SparseLu.java
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

package org.jacop.constraints.lp;

import java.util.Arrays;

/**
 * A sparse LU factorization of a square basis matrix B, by right-looking Gaussian elimination with
 * Markowitz pivoting and a threshold on the pivot size, followed by product-form (eta) updates when
 * one column of B is replaced. The columns of B are its positions 0..m-1, the rows are the rows of
 * the problem 0..m-1.
 *
 * <p>{@link #ftran} solves {@code B y = x} (x by row, y by position) and {@link #btran} solves
 * {@code y B = z} (z by position, y by row). Both work on dense arrays of length m, in time linear
 * in m and in the nonzeros of the factors.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SparseLu {

  // a pivot must be at least this share of the largest entry of its row in the active matrix
  private static final double THRESHOLD = 0.1;

  // entries this small are taken as zero during elimination
  private static final double DROP = 1e-14;

  // the columns of smallest count searched for a pivot once one acceptable pivot is found
  private static final int SEARCH = 4;

  final int m;

  // the elimination steps: pivot row, pivot position, the pivot, the multipliers of L (row,
  // value) and the entries of U in the pivot row (position, value) for positions pivoted later
  private int steps;
  private final int[] pivotRow;
  private final int[] pivotPos;
  private final double[] diag;
  private final int[][] lIdx;
  private final double[][] lVal;
  private final int[][] uIdx;
  private final double[][] uVal;

  // the eta updates: the replaced position and the column B^-1 a_q, sparse
  private int etas;
  private int[] etaPos = new int[8];
  private int[][] etaIdx = new int[8][];
  private double[][] etaVal = new double[8][];
  private double[] etaPivot = new double[8];
  private long etaNonzeros;

  /** The entries the factorization and the solves have touched, a measure of their work. */
  long ops;

  /** The nonzeros of L and U. */
  long factorNonzeros;

  /** The positions found dependent at the last factorization, replaced by the slacks of rows. */
  int[] replacedPos = new int[0];

  /** The rows whose slacks replaced them, matching {@link #replacedPos}. */
  int[] replacedRow = new int[0];

  /**
   * Factorizes B.
   *
   * @param m the size of B
   * @param colIdx the rows of the nonzeros of each column (position) of B
   * @param colVal the nonzeros of each column of B
   * @param colLen the number of nonzeros of each column of B
   */
  SparseLu(int m, int[][] colIdx, double[][] colVal, int[] colLen) {
    this.m = m;
    pivotRow = new int[m];
    pivotPos = new int[m];
    diag = new double[m];
    lIdx = new int[m][];
    lVal = new double[m][];
    uIdx = new int[m][];
    uVal = new double[m][];
    factor(colIdx, colVal, colLen);
  }

  /**
   * Returns the number of eta updates since the factorization.
   *
   * @return the updates
   */
  int updates() {
    return etas;
  }

  /**
   * Returns the nonzeros of the eta updates.
   *
   * @return the nonzeros
   */
  long updateNonzeros() {
    return etaNonzeros;
  }

  // the active matrix during factorization, row-wise with values and column-wise with patterns
  private int[][] rIdx;
  private double[][] rVal;
  private int[] rLen;
  private int[][] cIdx;
  private int[] cLen;

  // count buckets of the active columns: doubly linked lists by count
  private int[] colHead;
  private int[] colNext;
  private int[] colPrev;

  private void factor(int[][] colIdx, double[][] colVal, int[] colLen) {
    rIdx = new int[m][];
    rVal = new double[m][];
    rLen = new int[m];
    cIdx = new int[m][];
    cLen = new int[m];
    int[] count = new int[m];
    for (int k = 0; k < m; k++) {
      for (int e = 0; e < colLen[k]; e++) {
        if (colVal[k][e] != 0) {
          count[colIdx[k][e]]++;
        }
      }
    }
    for (int i = 0; i < m; i++) {
      rIdx[i] = new int[Math.max(4, count[i])];
      rVal[i] = new double[Math.max(4, count[i])];
    }
    for (int k = 0; k < m; k++) {
      cIdx[k] = new int[Math.max(4, colLen[k])];
      for (int e = 0; e < colLen[k]; e++) {
        double v = colVal[k][e];
        if (v != 0) {
          int i = colIdx[k][e];
          rIdx[i][rLen[i]] = k;
          rVal[i][rLen[i]++] = v;
          cIdx[k][cLen[k]++] = i;
        }
      }
    }
    colHead = new int[m + 1];
    Arrays.fill(colHead, -1);
    colNext = new int[m];
    colPrev = new int[m];
    for (int k = 0; k < m; k++) {
      link(k);
    }
    boolean[] rowDone = new boolean[m];
    boolean[] posDone = new boolean[m];
    // where position c sits in the row being updated, or -1
    int[] where = new int[m];
    Arrays.fill(where, -1);
    int[] replacedP = new int[m];
    int replaced = 0;
    steps = 0;
    factorNonzeros = 0;
    while (steps < m) {
      int p = -1;
      int q = -1;
      long best = Long.MAX_VALUE;
      int searched = 0;
      // the columns in increasing count; a column with no entries left is singular
      for (int c = 0; c <= m && searched < SEARCH; c++) {
        for (int k = colHead[c]; k >= 0 && searched < SEARCH; k = colNext[k]) {
          if (c == 0) {
            continue; // an empty column, taken care of below
          }
          for (int e = 0; e < cLen[k]; e++) {
            int i = cIdx[k][e];
            double v = Math.abs(valueAt(i, k));
            if (v <= DROP || v < THRESHOLD * rowMax(i)) {
              continue;
            }
            long mc = (long) (rLen[i] - 1) * (cLen[k] - 1);
            if (mc < best) {
              best = mc;
              p = i;
              q = k;
            }
          }
          if (p >= 0) {
            searched++;
          }
          if (best == 0) {
            searched = SEARCH;
          }
        }
      }
      if (p < 0) {
        // the remaining columns are dependent: leave them out, the caller puts slacks there
        break;
      }
      eliminate(p, q, rowDone, posDone, where);
    }
    // the positions not pivoted are dependent; each gets the slack of a row not pivoted, whose
    // column -e_i is pivoted at once
    if (steps < m) {
      int[] freeRows = new int[m - steps];
      int fr = 0;
      for (int i = 0; i < m; i++) {
        if (!rowDone[i]) {
          freeRows[fr++] = i;
        }
      }
      int[] freePos = new int[m - steps];
      int fp = 0;
      for (int k = 0; k < m; k++) {
        if (!posDone[k]) {
          freePos[fp++] = k;
        }
      }
      // the slack -e_i of a free row is zero in every pivot row, so the rows of U lose their
      // entries in the free positions
      for (int s = 0; s < steps; s++) {
        int[] ui = uIdx[s];
        double[] uv = uVal[s];
        int keep = 0;
        for (int e = 0; e < ui.length; e++) {
          if (posDone[ui[e]]) {
            ui[keep] = ui[e];
            uv[keep++] = uv[e];
          }
        }
        if (keep < ui.length) {
          uIdx[s] = Arrays.copyOf(ui, keep);
          uVal[s] = Arrays.copyOf(uv, keep);
        }
      }
      replacedPos = new int[fp];
      replacedRow = new int[fp];
      for (int s = 0; s < fp; s++) {
        int k = freePos[s];
        int i = freeRows[s];
        replacedPos[s] = k;
        replacedRow[s] = i;
        pivotRow[steps] = i;
        pivotPos[steps] = k;
        diag[steps] = -1;
        lIdx[steps] = new int[0];
        lVal[steps] = new double[0];
        uIdx[steps] = new int[0];
        uVal[steps] = new double[0];
        steps++;
      }
      // the other rows must not keep entries in the replaced positions: the rows not pivoted have
      // their pivots now, and their entries in other free positions are dropped with the columns
    }
    rIdx = null;
    rVal = null;
    rLen = null;
    cIdx = null;
    cLen = null;
    colHead = null;
    colNext = null;
    colPrev = null;
  }

  private double valueAt(int i, int k) {
    int[] ri = rIdx[i];
    for (int e = 0; e < rLen[i]; e++) {
      if (ri[e] == k) {
        return rVal[i][e];
      }
    }
    return 0;
  }

  private double rowMax(int i) {
    double mx = 0;
    double[] rv = rVal[i];
    for (int e = 0; e < rLen[i]; e++) {
      mx = Math.max(mx, Math.abs(rv[e]));
    }
    return mx;
  }

  private void link(int k) {
    int c = cLen[k];
    colPrev[k] = -1;
    colNext[k] = colHead[c];
    if (colHead[c] >= 0) {
      colPrev[colHead[c]] = k;
    }
    colHead[c] = k;
  }

  private void unlink(int k) {
    if (colPrev[k] >= 0) {
      colNext[colPrev[k]] = colNext[k];
    } else {
      colHead[cLen[k]] = colNext[k];
    }
    if (colNext[k] >= 0) {
      colPrev[colNext[k]] = colPrev[k];
    }
  }

  // removes row i from the pattern of column k
  private void removeFromColumn(int k, int i) {
    int[] ck = cIdx[k];
    for (int e = 0; e < cLen[k]; e++) {
      if (ck[e] == i) {
        ck[e] = ck[--cLen[k]];
        return;
      }
    }
  }

  private void eliminate(int p, int q, boolean[] rowDone, boolean[] posDone, int[] where) {
    double pv = valueAt(p, q);
    ops += rLen[p] + cLen[q];
    // the pivot row leaves the active matrix: its other entries are the row of U
    int len = rLen[p];
    int[] ui = new int[len - 1];
    double[] uv = new double[len - 1];
    int u = 0;
    for (int e = 0; e < len; e++) {
      int k = rIdx[p][e];
      if (k != q) {
        ui[u] = k;
        uv[u++] = rVal[p][e];
        unlink(k);
        removeFromColumn(k, p);
        link(k);
      }
    }
    unlink(q);
    removeFromColumn(q, p);
    // the other rows of the pivot column: eliminate it from them
    int cl = cLen[q];
    int[] li = new int[cl];
    double[] lv = new double[cl];
    int l = 0;
    for (int e = 0; e < cl; e++) {
      int i = cIdx[q][e];
      double v = valueAt(i, q);
      // drop the entry of column q from row i
      int[] ri = rIdx[i];
      double[] rv = rVal[i];
      for (int f = 0; f < rLen[i]; f++) {
        if (ri[f] == q) {
          rLen[i]--;
          ri[f] = ri[rLen[i]];
          rv[f] = rv[rLen[i]];
          break;
        }
      }
      if (v == 0) {
        continue;
      }
      double mult = v / pv;
      ops += rLen[i] + u;
      li[l] = i;
      lv[l++] = mult;
      for (int f = 0; f < rLen[i]; f++) {
        where[ri[f]] = f;
      }
      for (int g = 0; g < u; g++) {
        int k = ui[g];
        double delta = -mult * uv[g];
        int f = where[k];
        if (f >= 0) {
          rVal[i][f] += delta;
        } else {
          // fill-in
          if (rLen[i] == rIdx[i].length) {
            rIdx[i] = Arrays.copyOf(rIdx[i], rLen[i] * 2);
            rVal[i] = Arrays.copyOf(rVal[i], rLen[i] * 2);
          }
          rIdx[i][rLen[i]] = k;
          rVal[i][rLen[i]] = delta;
          where[k] = rLen[i]++;
          unlink(k);
          if (cLen[k] == cIdx[k].length) {
            cIdx[k] = Arrays.copyOf(cIdx[k], cLen[k] * 2);
          }
          cIdx[k][cLen[k]++] = i;
          link(k);
        }
      }
      ri = rIdx[i];
      rv = rVal[i];
      for (int f = 0; f < rLen[i]; f++) {
        where[ri[f]] = -1;
      }
      // entries cancelled to zero leave the row and the column
      for (int f = 0; f < rLen[i]; ) {
        if (Math.abs(rv[f]) <= DROP) {
          int k = ri[f];
          unlink(k);
          removeFromColumn(k, i);
          link(k);
          rLen[i]--;
          ri[f] = ri[rLen[i]];
          rv[f] = rv[rLen[i]];
        } else {
          f++;
        }
      }
    }
    cLen[q] = 0;
    rLen[p] = 0;
    rowDone[p] = true;
    posDone[q] = true;
    pivotRow[steps] = p;
    pivotPos[steps] = q;
    diag[steps] = pv;
    lIdx[steps] = Arrays.copyOf(li, l);
    lVal[steps] = Arrays.copyOf(lv, l);
    uIdx[steps] = ui;
    uVal[steps] = uv;
    factorNonzeros += l + u + 1;
    steps++;
  }

  /**
   * Solves {@code B y = x}.
   *
   * @param x the right-hand side by row, overwritten
   * @param y the solution by position
   */
  void ftran(double[] x, double[] y) {
    ops += 2L * steps + etas + factorNonzeros;
    for (int s = 0; s < steps; s++) {
      double v = x[pivotRow[s]];
      if (v != 0) {
        int[] li = lIdx[s];
        double[] lv = lVal[s];
        for (int e = 0; e < li.length; e++) {
          x[li[e]] -= lv[e] * v;
        }
      }
    }
    for (int s = steps - 1; s >= 0; s--) {
      double sum = x[pivotRow[s]];
      int[] ui = uIdx[s];
      double[] uv = uVal[s];
      for (int e = 0; e < ui.length; e++) {
        double w = y[ui[e]];
        if (w != 0) {
          sum -= uv[e] * w;
        }
      }
      y[pivotPos[s]] = sum / diag[s];
    }
    for (int e = 0; e < etas; e++) {
      int r = etaPos[e];
      double yr = y[r];
      if (yr != 0) {
        yr /= etaPivot[e];
        y[r] = yr;
        int[] ei = etaIdx[e];
        double[] ev = etaVal[e];
        ops += ei.length;
        for (int f = 0; f < ei.length; f++) {
          y[ei[f]] -= ev[f] * yr;
        }
      }
    }
  }

  /**
   * Solves {@code y B = z}.
   *
   * @param z the right-hand side by position, overwritten
   * @param y the solution by row
   */
  void btran(double[] z, double[] y) {
    ops += 3L * steps + etas + etaNonzeros + factorNonzeros;
    for (int e = etas - 1; e >= 0; e--) {
      int r = etaPos[e];
      double sum = z[r];
      int[] ei = etaIdx[e];
      double[] ev = etaVal[e];
      for (int f = 0; f < ei.length; f++) {
        double w = z[ei[f]];
        if (w != 0) {
          sum -= ev[f] * w;
        }
      }
      z[r] = sum / etaPivot[e];
    }
    Arrays.fill(y, 0);
    for (int s = 0; s < steps; s++) {
      double t = z[pivotPos[s]];
      if (t != 0) {
        t /= diag[s];
        y[pivotRow[s]] = t;
        int[] ui = uIdx[s];
        double[] uv = uVal[s];
        for (int e = 0; e < ui.length; e++) {
          z[ui[e]] -= uv[e] * t;
        }
      }
    }
    for (int s = steps - 1; s >= 0; s--) {
      int[] li = lIdx[s];
      double[] lv = lVal[s];
      double sum = y[pivotRow[s]];
      for (int e = 0; e < li.length; e++) {
        double w = y[li[e]];
        if (w != 0) {
          sum -= lv[e] * w;
        }
      }
      y[pivotRow[s]] = sum;
    }
  }

  /**
   * Records that position r of B is replaced by a column a_q.
   *
   * @param r the position
   * @param alpha {@code B^-1 a_q} for the old B, by position
   */
  void update(int r, double[] alpha) {
    int nz = 0;
    for (int i = 0; i < m; i++) {
      if (i != r && alpha[i] != 0) {
        nz++;
      }
    }
    int[] ei = new int[nz];
    double[] ev = new double[nz];
    nz = 0;
    for (int i = 0; i < m; i++) {
      if (i != r && alpha[i] != 0) {
        ei[nz] = i;
        ev[nz++] = alpha[i];
      }
    }
    if (etas == etaPos.length) {
      int len = etas * 2;
      etaPos = Arrays.copyOf(etaPos, len);
      etaIdx = Arrays.copyOf(etaIdx, len);
      etaVal = Arrays.copyOf(etaVal, len);
      etaPivot = Arrays.copyOf(etaPivot, len);
    }
    etaPos[etas] = r;
    etaIdx[etas] = ei;
    etaVal[etas] = ev;
    etaPivot[etas] = alpha[r];
    etaNonzeros += nz + 1;
    etas++;
  }
}
