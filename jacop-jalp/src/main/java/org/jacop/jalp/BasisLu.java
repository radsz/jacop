/*
 * BasisLu.java
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
 * The LU factorization of a basis matrix B for {@link RevisedDualSimplex}: right-looking Gaussian
 * elimination with Markowitz pivoting under a threshold, which takes the triangular part of a basis
 * (column and row singletons, such as slack columns) at no cost, followed by product-form updates
 * when a column of B is replaced. The columns of B are its positions 0..m-1, the rows are the rows
 * of the problem.
 *
 * <p>The factors are kept by step and by row or position, so that both solves skip the zero entries
 * of their right-hand side: {@link #ftran} solves {@code B y = x} (x by row, y by position) and
 * {@link #btran} solves {@code y B = z} (z by position, y by row). The work of both is in the
 * nonzeros they touch plus one pass over the steps.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class BasisLu {

  // a pivot must be at least this share of the largest entry of its column in the active matrix
  private static final double THRESHOLD = 0.1;

  // entries this small are dropped during elimination and from the updates
  private static final double DROP = 1e-14;

  // the candidates looked at once one acceptable pivot is found
  private static final int SEARCH = 4;

  final int m;

  // the elimination: by step, the pivot row, the pivot position and the pivot
  private int steps;
  private final int[] pivotRow;
  private final int[] pivotPos;
  private final double[] diag;

  // L by step (the rows the step eliminated and their multipliers) and by row (the steps that
  // eliminated the row and the multipliers)
  private int[] lStart;
  private int[] lRow;
  private double[] lVal;
  private int[] lrStart;
  private int[] lrStep;
  private double[] lrVal;

  // U by step (the positions pivoted later in the pivot row) and by position (the earlier steps
  // with an entry in the position)
  private int[] uStart;
  private int[] uPos;
  private double[] uVal;
  private int[] ucStart;
  private int[] ucStep;
  private double[] ucVal;

  // the product-form updates: the replaced position, its pivot and the other entries of B^-1 a_q
  private int etas;
  private int[] etaPos = new int[16];
  private double[] etaPivot = new double[16];
  private int[] etaStart = new int[17];
  private int[] etaIdx = new int[64];
  private double[] etaVal = new double[64];

  /** The entries the factorization and the solves have touched, a measure of their work. */
  long ops;

  /** The nonzeros of L and U. */
  long factorNonzeros;

  /** The positions found dependent, to be replaced by the slacks of {@link #replacedRow}. */
  int[] replacedPos = new int[0];

  /** The rows whose slacks replace the dependent positions, matching {@link #replacedPos}. */
  int[] replacedRow = new int[0];

  /**
   * Factorizes B.
   *
   * @param m the size of B
   * @param colIdx the rows of the nonzeros of each column (position) of B
   * @param colVal the nonzeros of each column of B
   * @param colLen the number of nonzeros of each column of B
   */
  BasisLu(int m, int[][] colIdx, double[][] colVal, int[] colLen) {
    this.m = m;
    pivotRow = new int[m];
    pivotPos = new int[m];
    diag = new double[m];
    new Factor(colIdx, colVal, colLen).run();
  }

  /**
   * Returns the number of updates since the factorization.
   *
   * @return the updates
   */
  int updates() {
    return etas;
  }

  /**
   * Returns the nonzeros of the updates since the factorization.
   *
   * @return the nonzeros
   */
  long updateNonzeros() {
    return etaStart[etas];
  }

  // the elimination, with its active matrix by row (positions and values) and by position (rows)
  private final class Factor {
    private final int[][] rIdx = new int[m][];
    private final double[][] rVal = new double[m][];
    private final int[] rLen = new int[m];
    private final double[] rowMax = new double[m];
    private final int[][] cIdx = new int[m][];
    private final int[] cLen = new int[m];
    private final boolean[] rowDone = new boolean[m];
    private final boolean[] posDone = new boolean[m];
    // count buckets of the active columns and rows, as doubly linked lists
    private final int[] colHead = new int[m + 2];
    private final int[] colNext = new int[m];
    private final int[] colPrev = new int[m];
    private final int[] rowHead = new int[m + 2];
    private final int[] rowNext = new int[m];
    private final int[] rowPrev = new int[m];
    // a scatter of the pivot row: the index in the pivot row of each position, or -1
    private final int[] where = new int[m];
    // L and U as they are made, by step
    private final int[][] lStepRow = new int[m][];
    private final double[][] lStepVal = new double[m][];
    private final int[][] uStepPos = new int[m][];
    private final double[][] uStepVal = new double[m][];

    Factor(int[][] colIdx, double[][] colVal, int[] colLen) {
      int[] count = new int[m];
      for (int k = 0; k < m; k++) {
        for (int e = 0; e < colLen[k]; e++) {
          if (colVal[k][e] != 0) {
            count[colIdx[k][e]]++;
          }
        }
      }
      for (int i = 0; i < m; i++) {
        rIdx[i] = new int[Math.max(2, count[i])];
        rVal[i] = new double[Math.max(2, count[i])];
      }
      for (int k = 0; k < m; k++) {
        cIdx[k] = new int[Math.max(2, colLen[k])];
        for (int e = 0; e < colLen[k]; e++) {
          double v = colVal[k][e];
          if (v != 0) {
            int i = colIdx[k][e];
            rIdx[i][rLen[i]] = k;
            rVal[i][rLen[i]++] = v;
            cIdx[k][cLen[k]++] = i;
          }
        }
        ops += colLen[k];
      }
      Arrays.fill(colHead, -1);
      Arrays.fill(rowHead, -1);
      Arrays.fill(where, -1);
      for (int k = 0; k < m; k++) {
        linkCol(k);
      }
      for (int i = 0; i < m; i++) {
        computeRowMax(i);
        linkRow(i);
      }
    }

    void run() {
      steps = 0;
      while (steps < m) {
        if (!pivot()) {
          break;
        }
      }
      if (steps < m) {
        dependent();
      }
      pack(lStepRow, lStepVal, uStepPos, uStepVal);
    }

    // finds and makes one pivot; false when the active matrix has no nonzero left. A pivot must be
    // at least THRESHOLD of the largest entry of its row; among those found in the columns and rows
    // of fewest entries, the one of least Markowitz cost (r - 1)(c - 1) is taken.
    private boolean pivot() {
      int bestRow = -1;
      int bestPos = -1;
      long bestCost = Long.MAX_VALUE;
      double bestV = 0;
      int looked = 0;
      for (int c = 1; c <= m; c++) {
        if (bestRow >= 0 && (looked >= SEARCH || bestCost <= (long) (c - 1) * (c - 1))) {
          break;
        }
        // columns with c entries
        for (int k = colHead[c]; k >= 0; k = colNext[k]) {
          for (int e = 0; e < cLen[k]; e++) {
            int i = cIdx[k][e];
            double v = Math.abs(valueAt(i, k));
            if (v > DROP && v >= THRESHOLD * rowMax[i]) {
              long cost = (long) (rLen[i] - 1) * (c - 1);
              if (cost < bestCost || cost == bestCost && v > bestV) {
                bestCost = cost;
                bestRow = i;
                bestPos = k;
                bestV = v;
              }
            }
          }
          if (++looked >= SEARCH && bestRow >= 0 || bestCost == 0) {
            break;
          }
        }
        if (bestRow >= 0 && (bestCost == 0 || looked >= SEARCH)) {
          break;
        }
        // rows with c entries
        for (int i = rowHead[c]; i >= 0; i = rowNext[i]) {
          double floor = Math.max(DROP, THRESHOLD * rowMax[i]);
          for (int e = 0; e < rLen[i]; e++) {
            double v = Math.abs(rVal[i][e]);
            if (v > floor || v == rowMax[i] && v > DROP) {
              int k = rIdx[i][e];
              long cost = (long) (c - 1) * (cLen[k] - 1);
              if (cost < bestCost || cost == bestCost && v > bestV) {
                bestCost = cost;
                bestRow = i;
                bestPos = k;
                bestV = v;
              }
            }
          }
          ops += rLen[i];
          if (++looked >= SEARCH && bestRow >= 0 || bestCost == 0) {
            break;
          }
        }
      }
      if (bestRow < 0) {
        return false;
      }
      eliminate(bestRow, bestPos);
      return true;
    }

    private void computeRowMax(int i) {
      double big = 0;
      for (int e = 0; e < rLen[i]; e++) {
        big = Math.max(big, Math.abs(rVal[i][e]));
      }
      rowMax[i] = big;
      ops += rLen[i];
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

    private void eliminate(int p, int q) {
      int s = steps++;
      pivotRow[s] = p;
      pivotPos[s] = q;
      unlinkRow(p);
      unlinkCol(q);
      rowDone[p] = true;
      posDone[q] = true;
      // the pivot row: its pivot, and the entries that become the row of U
      int len = rLen[p];
      int[] rp = rIdx[p];
      double[] vp = rVal[p];
      double piv = 0;
      int[] up = new int[len];
      double[] uv = new double[len];
      int u = 0;
      for (int e = 0; e < len; e++) {
        int k = rp[e];
        if (k == q) {
          piv = vp[e];
        } else {
          up[u] = k;
          uv[u++] = vp[e];
          removeFromCol(k, p);
        }
      }
      diag[s] = piv;
      uStepPos[s] = Arrays.copyOf(up, u);
      uStepVal[s] = Arrays.copyOf(uv, u);
      for (int e = 0; e < u; e++) {
        where[up[e]] = e;
      }
      // the other rows of the pivot column: their multipliers, and row_i -= l row_p
      int cl = cLen[q];
      int[] lr = new int[cl];
      double[] lv = new double[cl];
      int nl = 0;
      boolean[] seen = new boolean[u];
      for (int c = 0; c < cl; c++) {
        int i = cIdx[q][c];
        if (i == p) {
          continue;
        }
        unlinkRow(i);
        // take the entry of the pivot column out of row i
        int[] ri = rIdx[i];
        double[] vi = rVal[i];
        double a = 0;
        for (int f = 0; f < rLen[i]; f++) {
          if (ri[f] == q) {
            a = vi[f];
            rLen[i]--;
            ri[f] = ri[rLen[i]];
            vi[f] = vi[rLen[i]];
            break;
          }
        }
        double l = a / piv;
        if (Math.abs(l) > DROP) {
          lr[nl] = i;
          lv[nl++] = l;
          Arrays.fill(seen, false);
          for (int f = 0; f < rLen[i]; f++) {
            int w = where[ri[f]];
            if (w >= 0) {
              vi[f] -= l * uv[w];
              seen[w] = true;
            }
          }
          ops += rLen[i] + u;
          for (int w = 0; w < u; w++) {
            if (!seen[w]) {
              int k = up[w];
              double v = -l * uv[w];
              if (rLen[i] == rIdx[i].length) {
                rIdx[i] = Arrays.copyOf(rIdx[i], rLen[i] * 2);
                rVal[i] = Arrays.copyOf(rVal[i], rLen[i] * 2);
                ri = rIdx[i];
                vi = rVal[i];
              }
              ri[rLen[i]] = k;
              vi[rLen[i]++] = v;
              addToCol(k, i);
            }
          }
          // drop the entries that cancelled; the largest entry of the row is known again after
          for (int f = 0; f < rLen[i]; ) {
            if (Math.abs(vi[f]) <= DROP) {
              removeFromCol(ri[f], i);
              rLen[i]--;
              ri[f] = ri[rLen[i]];
              vi[f] = vi[rLen[i]];
            } else {
              f++;
            }
          }
          computeRowMax(i);
        }
        linkRow(i);
      }
      for (int e = 0; e < u; e++) {
        where[up[e]] = -1;
      }
      lStepRow[s] = Arrays.copyOf(lr, nl);
      lStepVal[s] = Arrays.copyOf(lv, nl);
      cLen[q] = 0;
      rLen[p] = 0;
    }

    // the positions without a pivot are dependent: each is replaced by the slack of a row without
    // a pivot, which is then pivoted on as a unit column
    private void dependent() {
      int left = m - steps;
      replacedPos = new int[left];
      replacedRow = new int[left];
      int a = 0;
      int b = 0;
      for (int k = 0; k < m; k++) {
        if (!posDone[k]) {
          replacedPos[a++] = k;
        }
      }
      for (int i = 0; i < m; i++) {
        if (!rowDone[i]) {
          replacedRow[b++] = i;
        }
      }
      // the slack column of row i is -e_i: its step has pivot -1 and no entries in L; the rows
      // pivoted earlier may have entries in the replaced positions, which belong to the old
      // columns and are dropped
      for (int s = 0; s < steps; s++) {
        int[] ui = uStepPos[s];
        int keep = 0;
        for (int e = 0; e < ui.length; e++) {
          if (posDone[ui[e]]) {
            ui[keep] = ui[e];
            uStepVal[s][keep++] = uStepVal[s][e];
          }
        }
        uStepPos[s] = Arrays.copyOf(ui, keep);
        uStepVal[s] = Arrays.copyOf(uStepVal[s], keep);
      }
      for (int t = 0; t < left; t++) {
        int s = steps++;
        pivotRow[s] = replacedRow[t];
        pivotPos[s] = replacedPos[t];
        diag[s] = -1;
        lStepRow[s] = new int[0];
        lStepVal[s] = new double[0];
        uStepPos[s] = new int[0];
        uStepVal[s] = new double[0];
      }
    }

    private void addToCol(int k, int i) {
      unlinkCol(k);
      if (cLen[k] == cIdx[k].length) {
        cIdx[k] = Arrays.copyOf(cIdx[k], cLen[k] * 2);
      }
      cIdx[k][cLen[k]++] = i;
      linkCol(k);
    }

    private void removeFromCol(int k, int i) {
      int[] ck = cIdx[k];
      for (int e = 0; e < cLen[k]; e++) {
        if (ck[e] == i) {
          unlinkCol(k);
          ck[e] = ck[--cLen[k]];
          linkCol(k);
          return;
        }
      }
    }

    private void linkCol(int k) {
      if (posDone[k]) {
        return;
      }
      int c = Math.min(cLen[k], m + 1);
      colPrev[k] = -1;
      colNext[k] = colHead[c];
      if (colHead[c] >= 0) {
        colPrev[colHead[c]] = k;
      }
      colHead[c] = k;
    }

    private void unlinkCol(int k) {
      if (posDone[k]) {
        return;
      }
      int c = Math.min(cLen[k], m + 1);
      if (colPrev[k] >= 0) {
        colNext[colPrev[k]] = colNext[k];
      } else {
        colHead[c] = colNext[k];
      }
      if (colNext[k] >= 0) {
        colPrev[colNext[k]] = colPrev[k];
      }
    }

    private void linkRow(int i) {
      if (rowDone[i]) {
        return;
      }
      int c = Math.min(rLen[i], m + 1);
      rowPrev[i] = -1;
      rowNext[i] = rowHead[c];
      if (rowHead[c] >= 0) {
        rowPrev[rowHead[c]] = i;
      }
      rowHead[c] = i;
    }

    private void unlinkRow(int i) {
      if (rowDone[i]) {
        return;
      }
      int c = Math.min(rLen[i], m + 1);
      if (rowPrev[i] >= 0) {
        rowNext[rowPrev[i]] = rowNext[i];
      } else {
        rowHead[c] = rowNext[i];
      }
      if (rowNext[i] >= 0) {
        rowPrev[rowNext[i]] = rowPrev[i];
      }
    }
  }

  // the factors as flat arrays by step, by row (L) and by position (U)
  private void pack(int[][] lsr, double[][] lsv, int[][] usp, double[][] usv) {
    int[] rowStep = new int[m];
    int[] posStep = new int[m];
    for (int s = 0; s < m; s++) {
      rowStep[pivotRow[s]] = s;
      posStep[pivotPos[s]] = s;
    }
    int nl = 0;
    int nu = 0;
    for (int s = 0; s < m; s++) {
      nl += lsr[s].length;
      nu += usp[s].length;
    }
    factorNonzeros = nl + nu + m;
    lStart = new int[m + 1];
    lRow = new int[nl];
    lVal = new double[nl];
    int[] rowCount = new int[m + 1];
    for (int s = 0, e = 0; s < m; s++) {
      lStart[s] = e;
      for (int f = 0; f < lsr[s].length; f++, e++) {
        lRow[e] = lsr[s][f];
        lVal[e] = lsv[s][f];
        rowCount[lsr[s][f]]++;
      }
    }
    lStart[m] = nl;
    lrStart = new int[m + 1];
    for (int i = 0; i < m; i++) {
      lrStart[i + 1] = lrStart[i] + rowCount[i];
    }
    lrStep = new int[nl];
    lrVal = new double[nl];
    int[] fill = Arrays.copyOf(lrStart, m);
    for (int s = 0; s < m; s++) {
      for (int e = lStart[s]; e < lStart[s + 1]; e++) {
        int i = lRow[e];
        lrStep[fill[i]] = s;
        lrVal[fill[i]++] = lVal[e];
      }
    }
    uStart = new int[m + 1];
    uPos = new int[nu];
    uVal = new double[nu];
    int[] posCount = new int[m + 1];
    for (int s = 0, e = 0; s < m; s++) {
      uStart[s] = e;
      for (int f = 0; f < usp[s].length; f++, e++) {
        uPos[e] = usp[s][f];
        uVal[e] = usv[s][f];
        posCount[usp[s][f]]++;
      }
    }
    uStart[m] = nu;
    ucStart = new int[m + 1];
    for (int k = 0; k < m; k++) {
      ucStart[k + 1] = ucStart[k] + posCount[k];
    }
    ucStep = new int[nu];
    ucVal = new double[nu];
    fill = Arrays.copyOf(ucStart, m);
    for (int s = 0; s < m; s++) {
      for (int e = uStart[s]; e < uStart[s + 1]; e++) {
        int k = uPos[e];
        ucStep[fill[k]] = s;
        ucVal[fill[k]++] = uVal[e];
      }
    }
    ops += 2L * (nl + nu) + m;
  }

  /**
   * Solves {@code B y = x}. x is overwritten.
   *
   * @param x the right-hand side, by row
   * @param y the solution, by position
   */
  void ftran(double[] x, double[] y) {
    ops += 2L * m;
    for (int s = 0; s < m; s++) {
      double v = x[pivotRow[s]];
      if (v != 0) {
        int end = lStart[s + 1];
        for (int e = lStart[s]; e < end; e++) {
          x[lRow[e]] -= lVal[e] * v;
        }
        ops += end - lStart[s];
      }
    }
    for (int s = m - 1; s >= 0; s--) {
      int p = pivotRow[s];
      int q = pivotPos[s];
      double t = x[p] / diag[s];
      x[p] = 0;
      y[q] = t;
      if (t != 0) {
        int end = ucStart[q + 1];
        for (int e = ucStart[q]; e < end; e++) {
          x[pivotRow[ucStep[e]]] -= ucVal[e] * t;
        }
        ops += end - ucStart[q];
      }
    }
    for (int e = 0; e < etas; e++) {
      int r = etaPos[e];
      double yr = y[r];
      if (yr != 0) {
        yr /= etaPivot[e];
        y[r] = yr;
        int end = etaStart[e + 1];
        for (int f = etaStart[e]; f < end; f++) {
          y[etaIdx[f]] -= etaVal[f] * yr;
        }
        ops += end - etaStart[e];
      }
    }
  }

  /**
   * Solves {@code y B = z}. z is overwritten.
   *
   * @param z the right-hand side, by position
   * @param y the solution, by row
   */
  void btran(double[] z, double[] y) {
    ops += 2L * m;
    for (int e = etas - 1; e >= 0; e--) {
      int r = etaPos[e];
      double v = z[r];
      int end = etaStart[e + 1];
      for (int f = etaStart[e]; f < end; f++) {
        v -= etaVal[f] * z[etaIdx[f]];
      }
      ops += end - etaStart[e];
      z[r] = v / etaPivot[e];
    }
    for (int s = 0; s < m; s++) {
      int q = pivotPos[s];
      double t = z[q] / diag[s];
      z[q] = 0;
      y[pivotRow[s]] = t;
      if (t != 0) {
        int end = uStart[s + 1];
        for (int e = uStart[s]; e < end; e++) {
          z[uPos[e]] -= uVal[e] * t;
        }
        ops += end - uStart[s];
      }
    }
    for (int s = m - 1; s >= 0; s--) {
      int i = pivotRow[s];
      double v = y[i];
      if (v != 0) {
        int end = lrStart[i + 1];
        for (int e = lrStart[i]; e < end; e++) {
          y[pivotRow[lrStep[e]]] -= lrVal[e] * v;
        }
        ops += end - lrStart[i];
      }
    }
  }

  /**
   * Replaces the column of B at position r by the column whose solve {@code B^-1 a_q} is alpha.
   *
   * @param r the position
   * @param alpha {@code B^-1 a_q}, by position
   */
  void update(int r, double[] alpha) {
    int start = etaStart[etas];
    int nz = 0;
    for (int i = 0; i < m; i++) {
      if (i != r && Math.abs(alpha[i]) > DROP) {
        nz++;
      }
    }
    if (etas + 1 >= etaPos.length) {
      etaPos = Arrays.copyOf(etaPos, etaPos.length * 2);
      etaPivot = Arrays.copyOf(etaPivot, etaPivot.length * 2);
      etaStart = Arrays.copyOf(etaStart, etaStart.length * 2 + 1);
    }
    if (start + nz > etaIdx.length) {
      int size = Math.max(etaIdx.length * 2, start + nz);
      etaIdx = Arrays.copyOf(etaIdx, size);
      etaVal = Arrays.copyOf(etaVal, size);
    }
    int f = start;
    for (int i = 0; i < m; i++) {
      if (i != r && Math.abs(alpha[i]) > DROP) {
        etaIdx[f] = i;
        etaVal[f++] = alpha[i];
      }
    }
    etaPos[etas] = r;
    etaPivot[etas] = alpha[r];
    etas++;
    etaStart[etas] = f;
    ops += m;
  }
}
