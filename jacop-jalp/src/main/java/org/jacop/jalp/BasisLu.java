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

  // U by step (the positions of the steps after it in the order, with the entries of its row) and
  // by position (the steps before it with an entry in its column). The Forrest-Tomlin update
  // changes one column and one row of U at a time, so both are kept as lists
  private int[][] urPos;
  private double[][] urVal;
  private int[] urLen;
  private int[][] ucStep;
  private double[][] ucVal;
  private int[] ucLen;
  private long uNonzeros;

  // the step of each position, which an update keeps
  private int[] posStep;

  // the order of the steps in U: an update moves a step to the end, its old slot is dead (the rank
  // of the step is no longer the slot)
  private int[] order;
  private int orderLen;
  private int[] rank;

  // the row transformations of the updates: the step whose row was eliminated, and the multipliers
  // of the rows of the steps that eliminated it
  private int etas;
  private int[] etaStep = new int[16];
  private int[] etaStart = new int[17];
  private int[] etaIdx = new int[64];
  private double[] etaVal = new double[64];

  // the spike of the last column solved with ftranColumn: L^-1 a_q after the row transformations
  private double[] spike;

  // scatter of a row of U by position, for the update
  private double[] rowWork;

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
    return etaStart[etas] + Math.max(0, uNonzeros - initialUNonzeros);
  }

  private long initialUNonzeros;

  // the elimination, with its active matrix by row (positions and values) and by position (rows)
  private final class Factor {
    private final int[][] rIdx = new int[m][];
    private final double[][] rVal = new double[m][];
    private final int[] rLen = new int[m];
    private final double[] rowMax = new double[m];
    private final int[][] cIdx = new int[m][];
    private final int[] cLen = new int[m];
    // the active entries of each column; its list may also hold rows pivoted already and entries
    // that cancelled, which are skipped (removing them would scan dense columns again and again)
    private final int[] cCount = new int[m];
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
            cCount[k]++;
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
            if (rowDone[i]) {
              continue;
            }
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
              long cost = (long) (c - 1) * (cCount[k] - 1);
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
        if (rowDone[i]) {
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
      cCount[q] = 0;
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
        // the rows pivoted already go before the list grows
        int[] ck = cIdx[k];
        int keep = 0;
        for (int e = 0; e < cLen[k]; e++) {
          if (!rowDone[ck[e]]) {
            ck[keep++] = ck[e];
          }
        }
        ops += cLen[k];
        cLen[k] = keep;
        if (keep * 2 > ck.length) {
          cIdx[k] = Arrays.copyOf(ck, ck.length * 2);
        }
      }
      cIdx[k][cLen[k]++] = i;
      cCount[k]++;
      linkCol(k);
    }

    // the entry of row i leaves column k; the list keeps it until it is compacted
    private void removeFromCol(int k, int i) {
      unlinkCol(k);
      cCount[k]--;
      linkCol(k);
    }

    private void linkCol(int k) {
      if (posDone[k]) {
        return;
      }
      int c = Math.min(cCount[k], m + 1);
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
      int c = Math.min(cCount[k], m + 1);
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
    int nl = 0;
    int nu = 0;
    for (int s = 0; s < m; s++) {
      nl += lsr[s].length;
      nu += usp[s].length;
    }
    factorNonzeros = (long) nl + nu + m;
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
    posStep = new int[m];
    for (int t = 0; t < m; t++) {
      posStep[pivotPos[t]] = t;
    }
    urPos = new int[m][];
    urVal = new double[m][];
    urLen = new int[m];
    int[] posCount = new int[m];
    for (int t = 0; t < m; t++) {
      urPos[t] = usp[t];
      urVal[t] = usv[t];
      urLen[t] = usp[t].length;
      for (int k : usp[t]) {
        posCount[k]++;
      }
    }
    ucStep = new int[m][];
    ucVal = new double[m][];
    ucLen = new int[m];
    for (int k = 0; k < m; k++) {
      ucStep[k] = new int[Math.max(1, posCount[k])];
      ucVal[k] = new double[Math.max(1, posCount[k])];
    }
    for (int t = 0; t < m; t++) {
      for (int e = 0; e < usp[t].length; e++) {
        int k = usp[t][e];
        ucStep[k][ucLen[k]] = t;
        ucVal[k][ucLen[k]++] = usv[t][e];
      }
    }
    uNonzeros = nu;
    initialUNonzeros = nu;
    order = new int[m + 16];
    rank = new int[m];
    for (int t = 0; t < m; t++) {
      order[t] = t;
      rank[t] = t;
    }
    orderLen = m;
    ops += 2L * (nl + nu) + m;
  }

  /**
   * Solves {@code B y = x}. x is overwritten.
   *
   * @param x the right-hand side, by row
   * @param y the solution, by position
   */
  void ftran(double[] x, double[] y) {
    ftran(x, y, false);
  }

  /**
   * Solves {@code B y = x} for a column that may enter the basis, and keeps its spike for {@link
   * #update}. x is overwritten.
   *
   * @param x the column, by row
   * @param y the solution, by position
   */
  void ftranColumn(double[] x, double[] y) {
    ftran(x, y, true);
  }

  private void ftran(double[] x, double[] y, boolean keep) {
    ops += 2L * m + orderLen;
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
    for (int e = 0; e < etas; e++) {
      int p = pivotRow[etaStep[e]];
      double v = x[p];
      int end = etaStart[e + 1];
      for (int f = etaStart[e]; f < end; f++) {
        v -= etaVal[f] * x[pivotRow[etaIdx[f]]];
      }
      x[p] = v;
      ops += end - etaStart[e];
    }
    if (keep) {
      if (spike == null) {
        spike = new double[m];
      }
      System.arraycopy(x, 0, spike, 0, m);
    }
    for (int idx = orderLen - 1; idx >= 0; idx--) {
      int s = order[idx];
      if (rank[s] != idx) {
        continue;
      }
      int p = pivotRow[s];
      int q = pivotPos[s];
      double t = x[p] / diag[s];
      x[p] = 0;
      y[q] = t;
      if (t != 0) {
        int[] cs = ucStep[q];
        double[] cv = ucVal[q];
        int end = ucLen[q];
        for (int e = 0; e < end; e++) {
          x[pivotRow[cs[e]]] -= cv[e] * t;
        }
        ops += end;
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
    ops += 2L * m + orderLen;
    for (int idx = 0; idx < orderLen; idx++) {
      int s = order[idx];
      if (rank[s] != idx) {
        continue;
      }
      int q = pivotPos[s];
      double t = z[q] / diag[s];
      z[q] = 0;
      y[pivotRow[s]] = t;
      if (t != 0) {
        int[] rp = urPos[s];
        double[] rv = urVal[s];
        int end = urLen[s];
        for (int e = 0; e < end; e++) {
          z[rp[e]] -= rv[e] * t;
        }
        ops += end;
      }
    }
    for (int e = etas - 1; e >= 0; e--) {
      double w = y[pivotRow[etaStep[e]]];
      if (w != 0) {
        int end = etaStart[e + 1];
        for (int f = etaStart[e]; f < end; f++) {
          y[pivotRow[etaIdx[f]]] -= etaVal[f] * w;
        }
        ops += end - etaStart[e];
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
   * Replaces the column of B at position r by the column last solved with {@link #ftranColumn}
   * (Forrest-Tomlin): the spike becomes column r of U, the row of its step is eliminated by the
   * rows of the later steps (a row transformation kept with the updates), and the step moves to the
   * end of the order with the new pivot.
   *
   * @param r the position
   * @return false when the new pivot is too small, so the basis must be factorized again
   */
  boolean update(int r) {
    int t = posStep[r];
    // the old column r leaves the rows of U
    for (int e = 0; e < ucLen[r]; e++) {
      removeFromRow(ucStep[r][e], r);
    }
    uNonzeros -= ucLen[r];
    ucLen[r] = 0;
    // the row of t, scattered, leaves the columns of U
    if (rowWork == null) {
      rowWork = new double[m];
    }
    for (int e = 0; e < urLen[t]; e++) {
      int k = urPos[t][e];
      rowWork[k] = urVal[t][e];
      removeFromColumn(k, t);
    }
    uNonzeros -= urLen[t];
    ops += urLen[t] + m;
    urLen[t] = 0;
    // eliminate it with the rows of the steps after t, in their order; the spike entries of those
    // rows give the new pivot
    double pivot = spike[pivotRow[t]];
    if (etas + 1 >= etaStep.length) {
      etaStep = Arrays.copyOf(etaStep, etaStep.length * 2);
      etaStart = Arrays.copyOf(etaStart, etaStart.length * 2 + 1);
    }
    int f = etaStart[etas];
    for (int idx = rank[t] + 1; idx < orderLen; idx++) {
      int u = order[idx];
      if (rank[u] != idx) {
        continue;
      }
      int k = pivotPos[u];
      double v = rowWork[k];
      if (v == 0) {
        continue;
      }
      rowWork[k] = 0;
      double mu = v / diag[u];
      if (Math.abs(mu) <= DROP) {
        continue;
      }
      if (f == etaIdx.length) {
        etaIdx = Arrays.copyOf(etaIdx, f * 2);
        etaVal = Arrays.copyOf(etaVal, f * 2);
      }
      etaIdx[f] = u;
      etaVal[f++] = mu;
      int[] rp = urPos[u];
      double[] rv = urVal[u];
      for (int e = 0; e < urLen[u]; e++) {
        rowWork[rp[e]] -= mu * rv[e];
      }
      ops += urLen[u];
      pivot -= mu * spike[pivotRow[u]];
    }
    etaStep[etas] = t;
    etas++;
    etaStart[etas] = f;
    // the spike is the new column r, above the pivot of t, which is last now
    for (int idx = 0; idx < orderLen; idx++) {
      int s = order[idx];
      if (rank[s] != idx || s == t) {
        continue;
      }
      double v = spike[pivotRow[s]];
      if (Math.abs(v) > DROP) {
        addToColumn(r, s, v);
        addToRow(s, r, v);
        uNonzeros++;
      }
    }
    ops += orderLen;
    diag[t] = pivot;
    if (orderLen == order.length) {
      compactOrder();
    }
    order[orderLen] = t;
    rank[t] = orderLen++;
    return Math.abs(pivot) > 1e-11;
  }

  // drops the dead slots of the order
  private void compactOrder() {
    int k = 0;
    for (int idx = 0; idx < orderLen; idx++) {
      int s = order[idx];
      if (rank[s] == idx) {
        order[k] = s;
        rank[s] = k++;
      }
    }
    orderLen = k;
    if (orderLen + 1 >= order.length) {
      order = Arrays.copyOf(order, order.length * 2);
    }
  }

  private void removeFromRow(int s, int k) {
    int[] rp = urPos[s];
    for (int e = 0; e < urLen[s]; e++) {
      if (rp[e] == k) {
        int last = --urLen[s];
        rp[e] = rp[last];
        urVal[s][e] = urVal[s][last];
        ops += e;
        return;
      }
    }
    ops += urLen[s];
  }

  private void removeFromColumn(int k, int s) {
    int[] cs = ucStep[k];
    for (int e = 0; e < ucLen[k]; e++) {
      if (cs[e] == s) {
        int last = --ucLen[k];
        cs[e] = cs[last];
        ucVal[k][e] = ucVal[k][last];
        ops += e;
        return;
      }
    }
    ops += ucLen[k];
  }

  private void addToRow(int s, int k, double v) {
    if (urLen[s] == urPos[s].length) {
      int size = Math.max(4, urLen[s] * 2);
      urPos[s] = Arrays.copyOf(urPos[s], size);
      urVal[s] = Arrays.copyOf(urVal[s], size);
    }
    urPos[s][urLen[s]] = k;
    urVal[s][urLen[s]++] = v;
  }

  private void addToColumn(int k, int s, double v) {
    if (ucLen[k] == ucStep[k].length) {
      int size = Math.max(4, ucLen[k] * 2);
      ucStep[k] = Arrays.copyOf(ucStep[k], size);
      ucVal[k] = Arrays.copyOf(ucVal[k], size);
    }
    ucStep[k][ucLen[k]] = s;
    ucVal[k][ucLen[k]++] = v;
  }
}
