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
 * nonzeros they touch plus one pass over the steps. A solve from a right-hand side whose nonzeros
 * are listed skips that pass when its result is sparse (hypersparse, Gilbert-Peierls): a
 * depth-first search over the factors finds the steps the right-hand side reaches, and only those
 * are processed, sorted into the order of the full pass, so that the result is the same to the last
 * bit.
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

  // L by step (the rows the step eliminated and their multipliers) and by row (the pivot rows of
  // the steps that eliminated the row and the multipliers)
  private int[] lStart;
  private int[] lRow;
  private double[] lVal;
  private int[] lrStart;
  private int[] lrRow;
  private double[] lrVal;

  // U by step (the positions of the steps after it in the order, with the entries of its row) and
  // by position (the pivot rows of the steps before it with an entry in its column, so that ftran
  // reaches its right-hand side directly). The Forrest-Tomlin update
  // changes one column and one row of U at a time, so both are kept as lists
  private int[][] urPos;
  private double[][] urVal;
  private int[] urLen;
  private int[][] ucRow;
  private double[][] ucVal;
  private int[] ucLen;
  private long uNonzeros;

  // the step of each position, which an update keeps, and the step of each row
  private int[] posStep;
  private int[] rowStep;

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

  // the time of a factorization fitted on 29 instances of the LP bench, in units of the work of
  // the solves (about 3 ns): 1 for each entry counted in ops, 1/3 for each entry looked at by the
  // pivot search, and 256 for each step, its arrays and lists
  private static final int STEP_WORK = 256;

  /**
   * The work of the factorization that {@link #ops} leaves out, its pivot search and its arrays, on
   * the scale of the work of the solves.
   */
  long build;

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
      build = build / 3 + STEP_WORK * m;
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
        build++;
        // columns with c entries
        for (int k = colHead[c]; k >= 0; k = colNext[k]) {
          build += cLen[k];
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
        build++;
        if (ri[e] == k) {
          return rVal[i][e];
        }
      }
      return 0;
    }

    private void eliminate(int p, int q) {
      int s = steps++;
      build += cLen[q];
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
    lrRow = new int[nl];
    lrVal = new double[nl];
    int[] fill = Arrays.copyOf(lrStart, m);
    for (int s = 0; s < m; s++) {
      for (int e = lStart[s]; e < lStart[s + 1]; e++) {
        int i = lRow[e];
        lrRow[fill[i]] = pivotRow[s];
        lrVal[fill[i]++] = lVal[e];
      }
    }
    posStep = new int[m];
    rowStep = new int[m];
    for (int t = 0; t < m; t++) {
      posStep[pivotPos[t]] = t;
      rowStep[pivotRow[t]] = t;
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
    ucRow = new int[m][];
    ucVal = new double[m][];
    ucLen = new int[m];
    for (int k = 0; k < m; k++) {
      ucRow[k] = new int[Math.max(1, posCount[k])];
      ucVal[k] = new double[Math.max(1, posCount[k])];
    }
    for (int t = 0; t < m; t++) {
      for (int e = 0; e < usp[t].length; e++) {
        int k = usp[t][e];
        ucRow[k][ucLen[k]] = pivotRow[t];
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
    ftran(x, null, 0, y, null, false);
  }

  /**
   * Solves {@code B y = x} for a column that may enter the basis, and keeps its spike for {@link
   * #update}. x is overwritten.
   *
   * @param x the column, by row
   * @param y the solution, by position
   */
  void ftranColumn(double[] x, double[] y) {
    ftran(x, null, 0, y, null, true);
  }

  /**
   * Solves {@code B y = x} for a right-hand side whose nonzeros are listed. x is zero on return; y
   * must be zero on entry, and its nonzeros are listed on return. The result is the one of {@link
   * #ftran(double[], double[])}, entry for entry.
   *
   * @param x the right-hand side, by row
   * @param xi the rows of the nonzeros of x, overwritten (of length m)
   * @param xn the number of nonzeros of x
   * @param y the solution, by position
   * @param yi the positions of the nonzeros of y
   * @param keep whether x is a column that may enter the basis, whose spike is kept for {@link
   *     #update}
   * @return the number of nonzeros of y
   */
  int ftran(double[] x, int[] xi, int xn, double[] y, int[] yi, boolean keep) {
    return ftran(x, xi, xn, y, yi, keep, keep ? 0 : OTHER);
  }

  /**
   * Solves {@code B y = x} for the change of the basic values when nonbasic columns move to their
   * other bounds (the bound flips of the ratio test), as {@link #ftran(double[], int[], int,
   * double[], int[], boolean)} with a history of result densities of its own: these right-hand
   * sides are usually far sparser than the other ftrans that do not enter.
   *
   * @param x the right-hand side, by row
   * @param xi the rows of the nonzeros of x, overwritten (of length m)
   * @param xn the number of nonzeros of x
   * @param y the solution, by position
   * @param yi the positions of the nonzeros of y
   * @return the number of nonzeros of y
   */
  int ftranFlips(double[] x, int[] xi, int xn, double[] y, int[] yi) {
    return ftran(x, xi, xn, y, yi, false, FLIPS);
  }

  // history: the first of the two density slots of the solve, for L and for U
  private int ftran(double[] x, int[] xi, int xn, double[] y, int[] yi, boolean keep, int history) {
    ops += m;
    // L, by step: the steps the rows of x reach in L, in the order of the steps
    int reached = xi == null ? -1 : reach(xi, xn, L_FTRAN, history + L_FTRAN);
    if (reached < 0) {
      ops += m;
      for (int s = 0; s < m; s++) {
        lColumn(x, s);
      }
    } else {
      for (int k = 0; k < reached; k++) {
        lColumn(x, reach[k]);
      }
    }
    // the row transformations; a row they fill in joins the reached steps
    for (int e = 0; e < etas; e++) {
      int t = etaStep[e];
      int p = pivotRow[t];
      double v = x[p];
      int end = etaStart[e + 1];
      for (int f = etaStart[e]; f < end; f++) {
        v -= etaVal[f] * x[pivotRow[etaIdx[f]]];
      }
      x[p] = v;
      ops += end - etaStart[e];
      if (reached >= 0 && v != 0 && mark[t] != stamp) {
        mark[t] = stamp;
        reach = grow(reach, reached);
        reach[reached++] = t;
      }
    }
    if (keep) {
      keepSpike(x, reached);
    }
    // U, by position, from the last step in the order to the first
    if (reached >= 0) {
      for (int k = 0; k < reached; k++) {
        xi[k] = pivotRow[reach[k]];
      }
      reached = reach(xi, reached, U_FTRAN, history + U_FTRAN);
    }
    int yn = 0;
    if (reached < 0) {
      ops += orderLen;
      for (int idx = orderLen - 1; idx >= 0; idx--) {
        int s = order[idx];
        if (rank[s] == idx && uColumn(x, y, s) && yi != null) {
          yi[yn++] = pivotPos[s];
        }
      }
    } else {
      for (int k = reached - 1; k >= 0; k--) {
        int s = order[reach[k]];
        if (uColumn(x, y, s)) {
          yi[yn++] = pivotPos[s];
        }
      }
    }
    return yn;
  }

  // x -= the column of L of step s times the entry of x in its pivot row
  private void lColumn(double[] x, int s) {
    double v = x[pivotRow[s]];
    if (v != 0) {
      int end = lStart[s + 1];
      for (int e = lStart[s]; e < end; e++) {
        x[lRow[e]] -= lVal[e] * v;
      }
      ops += end - lStart[s];
    }
  }

  // the entry of y of step s from x, and x less the column of U of its position times it; whether
  // the entry is not zero
  private boolean uColumn(double[] x, double[] y, int s) {
    int p = pivotRow[s];
    int q = pivotPos[s];
    double v = x[p];
    if (v == 0) {
      y[q] = 0;
      return false;
    }
    double t = v / diag[s];
    x[p] = 0;
    y[q] = t;
    if (t == 0) {
      return false;
    }
    int[] cr = ucRow[q];
    double[] cv = ucVal[q];
    int end = ucLen[q];
    for (int e = 0; e < end; e++) {
      x[cr[e]] -= cv[e] * t;
    }
    ops += end;
    return true;
  }

  // the spike: x after L and the row transformations, for the update
  private void keepSpike(double[] x, int reached) {
    if (spike == null) {
      spike = new double[m];
      spikeRows = new int[m];
    }
    if (spikeLen < 0) {
      Arrays.fill(spike, 0);
    } else {
      for (int k = 0; k < spikeLen; k++) {
        spike[spikeRows[k]] = 0;
      }
    }
    if (reached < 0) {
      System.arraycopy(x, 0, spike, 0, m);
      spikeLen = -1;
      return;
    }
    for (int k = 0; k < reached; k++) {
      int i = pivotRow[reach[k]];
      spike[i] = x[i];
      spikeRows[k] = i;
    }
    spikeLen = reached;
  }

  /**
   * Solves {@code y B = z}. z is overwritten.
   *
   * @param z the right-hand side, by position
   * @param y the solution, by row
   */
  void btran(double[] z, double[] y) {
    btran(z, null, 0, y, null);
  }

  /**
   * Solves {@code y B = z} for a right-hand side whose nonzeros are listed. z is zero on return; y
   * must be zero on entry, and its nonzeros are listed on return. The result is the one of {@link
   * #btran(double[], double[])}, entry for entry.
   *
   * @param z the right-hand side, by position
   * @param zi the positions of the nonzeros of z, overwritten (of length m)
   * @param zn the number of nonzeros of z
   * @param y the solution, by row
   * @param yi the rows of the nonzeros of y
   * @return the number of nonzeros of y
   */
  int btran(double[] z, int[] zi, int zn, double[] y, int[] yi) {
    ops += m;
    // U, by step in the order: the steps the positions of z reach
    int reached = zi == null ? -1 : reach(zi, zn, U_BTRAN, U_BTRAN);
    if (reached < 0) {
      ops += orderLen;
      for (int idx = 0; idx < orderLen; idx++) {
        int s = order[idx];
        if (rank[s] == idx) {
          uRow(z, y, s);
        }
      }
    } else {
      for (int k = 0; k < reached; k++) {
        int s = order[reach[k]];
        uRow(z, y, s);
        reach[k] = s;
      }
    }
    // the row transformations, last first; a row they fill in joins the reached steps
    for (int e = etas - 1; e >= 0; e--) {
      double w = y[pivotRow[etaStep[e]]];
      if (w != 0) {
        int end = etaStart[e + 1];
        for (int f = etaStart[e]; f < end; f++) {
          int u = etaIdx[f];
          y[pivotRow[u]] -= etaVal[f] * w;
          if (reached >= 0 && mark[u] != stamp) {
            mark[u] = stamp;
            reach = grow(reach, reached);
            reach[reached++] = u;
          }
        }
        ops += end - etaStart[e];
      }
    }
    // L, by row, from the last step to the first
    if (reached >= 0) {
      for (int k = 0; k < reached; k++) {
        zi[k] = pivotRow[reach[k]];
      }
      reached = reach(zi, reached, L_BTRAN, L_BTRAN);
    }
    int yn = 0;
    if (reached < 0) {
      ops += m;
      for (int s = m - 1; s >= 0; s--) {
        if (lRow(y, s) && yi != null) {
          yi[yn++] = pivotRow[s];
        }
      }
    } else {
      for (int k = reached - 1; k >= 0; k--) {
        int s = reach[k];
        if (lRow(y, s)) {
          yi[yn++] = pivotRow[s];
        }
      }
    }
    return yn;
  }

  // the entry of y of step s from z, and z less the row of U of the step times it
  private void uRow(double[] z, double[] y, int s) {
    int q = pivotPos[s];
    double v = z[q];
    if (v == 0) {
      y[pivotRow[s]] = 0;
      return;
    }
    double t = v / diag[s];
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

  // y less the row of L of the pivot row of step s times its entry; whether the entry is not zero
  private boolean lRow(double[] y, int s) {
    int i = pivotRow[s];
    double v = y[i];
    if (v == 0) {
      return false;
    }
    int end = lrStart[i + 1];
    for (int e = lrStart[i]; e < end; e++) {
      y[lrRow[e]] -= lrVal[e] * v;
    }
    ops += end - lrStart[i];
    return true;
  }

  // the four triangular solves, for the search of the steps a right-hand side reaches
  private static final int L_FTRAN = 0;
  private static final int U_FTRAN = 1;
  private static final int U_BTRAN = 2;
  private static final int L_BTRAN = 3;

  // the history of an ftran of a column that may enter is kept apart from that of other ftrans
  private static final int OTHER = 4;

  // the history of the row eliminations of the updates
  private static final int UPDATE = 6;

  // the history of the ftrans of bound flips
  private static final int FLIPS = 7;

  /**
   * The share of the steps a solve may reach for its search to pay (Gilbert-Peierls): above it, or
   * when the recent solves of the same kind reached more, the solve runs over all steps.
   */
  static final double HYPER = Double.parseDouble(System.getProperty("org.jacop.jalp.hyper", "0.1"));

  // the steps reached by the last search, sorted: by step for L, by slot of the order for U
  private int[] reach = new int[16];

  // the depth-first search: its stack, with the next entry of each node, and the visited marks
  private int[] stack;
  private int[] next;
  private int[] mark;
  private int stamp;

  // the share of the steps reached by recent solves of each kind
  private final double[] density = new double[9];

  // the rows of the spike's nonzeros, or -1 when the spike was copied whole
  private int[] spikeRows;
  private int spikeLen = -1;

  /**
   * The steps of the solve {@code kind} that the rows or positions {@code from} reach, into {@link
   * #reach} in the order the solve takes them; -1 when the solve should run over all steps instead.
   * A depth-first search from each start step, over the entries of the factor of the solve.
   */
  private int reach(int[] from, int count, int kind, int slot) {
    int limit = (int) (HYPER * m);
    if (count > limit || density[slot] > HYPER) {
      // the solve runs over all steps; its share is taken as all, and decays with the solves that
      // skip the search, so that the search is tried again now and then
      density[slot] *= 0.95;
      return -1;
    }
    if (mark == null) {
      mark = new int[m];
      stack = new int[m];
      next = new int[m];
    }
    if (reach.length < limit + 1) {
      reach = new int[limit + 1];
    }
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(mark, 0);
      stamp = 1;
    }
    int found = 0;
    long work = 0;
    for (int k = 0; k < count; k++) {
      int start = kind == U_BTRAN ? posStep[from[k]] : rowStep[from[k]];
      if (mark[start] == stamp) {
        continue;
      }
      mark[start] = stamp;
      int top = 0;
      stack[0] = start;
      next[0] = 0;
      while (top >= 0) {
        int s = stack[top];
        int child = child(s, next[top]++, kind);
        work++;
        if (child == -1) {
          // s is done
          if (found == limit) {
            density[slot] = 1;
            ops += work;
            return -1;
          }
          reach[found++] = kind == U_FTRAN || kind == U_BTRAN ? rank[s] : s;
          top--;
        } else if (child >= 0 && mark[child] != stamp) {
          mark[child] = stamp;
          stack[++top] = child;
          next[top] = 0;
        }
      }
    }
    // the order of the dense solve: by step for L, by slot of the order for U (each solve walks
    // the sorted list in its own direction)
    Arrays.sort(reach, 0, found);
    ops += work + found + (long) found * (32 - Integer.numberOfLeadingZeros(found + 1));
    density[slot] = 0.9 * density[slot] + 0.1 * found / m;
    return found;
  }

  // the e-th step that step s leads to in the factor of the solve kind: -1 after the last, -2
  // for an entry to skip
  private int child(int s, int e, int kind) {
    switch (kind) {
      case L_FTRAN:
        {
          int f = lStart[s] + e;
          return f < lStart[s + 1] ? rowStep[lRow[f]] : -1;
        }
      case U_FTRAN:
        {
          int q = pivotPos[s];
          return e < ucLen[q] ? rowStep[ucRow[q][e]] : -1;
        }
      case U_BTRAN:
        return e < urLen[s] ? posStep[urPos[s][e]] : -1;
      default:
        {
          int i = pivotRow[s];
          int f = lrStart[i] + e;
          return f < lrStart[i + 1] ? rowStep[lrRow[f]] : -1;
        }
    }
  }

  private static int[] grow(int[] a, int used) {
    return used < a.length ? a : Arrays.copyOf(a, a.length * 2);
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
      removeFromRow(rowStep[ucRow[r][e]], r);
    }
    uNonzeros -= ucLen[r];
    ucLen[r] = 0;
    // the row of t, scattered, leaves the columns of U
    if (rowWork == null) {
      rowWork = new double[m];
    }
    int rowLen = urLen[t];
    for (int e = 0; e < rowLen; e++) {
      int k = urPos[t][e];
      rowWork[k] = urVal[t][e];
      removeFromColumn(k, t);
    }
    uNonzeros -= rowLen;
    ops += rowLen;
    urLen[t] = 0;
    // eliminate it with the rows of the steps after t, in their order; the spike entries of those
    // rows give the new pivot
    double pivot = spike[pivotRow[t]];
    if (etas + 1 >= etaStep.length) {
      etaStep = Arrays.copyOf(etaStep, etaStep.length * 2);
      etaStart = Arrays.copyOf(etaStart, etaStart.length * 2 + 1);
    }
    etaFill = etaStart[etas];
    // the steps the row reaches in U, in their order, or all steps after t
    int reached = reach(urPos[t], rowLen, U_BTRAN, UPDATE);
    if (reached < 0) {
      ops += orderLen;
      for (int idx = rank[t] + 1; idx < orderLen; idx++) {
        int u = order[idx];
        if (rank[u] == idx) {
          pivot = eliminateRow(u, pivot);
        }
      }
    } else {
      for (int k = 0; k < reached; k++) {
        pivot = eliminateRow(order[reach[k]], pivot);
      }
    }
    int f = etaFill;
    etaStep[etas] = t;
    etas++;
    etaStart[etas] = f;
    // the spike is the new column r, above the pivot of t, which is last now
    if (spikeLen < 0) {
      for (int idx = 0; idx < orderLen; idx++) {
        int s = order[idx];
        if (rank[s] == idx && s != t) {
          spikeEntry(r, s);
        }
      }
      ops += orderLen;
    } else {
      for (int k = 0; k < spikeLen; k++) {
        int s = rowStep[spikeRows[k]];
        if (s != t) {
          spikeEntry(r, s);
        }
      }
      ops += spikeLen;
    }
    diag[t] = pivot;
    if (orderLen == order.length) {
      compactOrder();
    }
    order[orderLen] = t;
    rank[t] = orderLen++;
    return Math.abs(pivot) > 1e-11;
  }

  // the next free entry of the row transformation being built by update
  private int etaFill;

  // eliminates the entry of rowWork at the position of step u with the row of u, into the row
  // transformation being built; returns the pivot less the share of u's spike entry
  private double eliminateRow(int u, double pivot) {
    int k = pivotPos[u];
    double v = rowWork[k];
    if (v == 0) {
      return pivot;
    }
    rowWork[k] = 0;
    double mu = v / diag[u];
    if (Math.abs(mu) <= DROP) {
      return pivot;
    }
    int f = etaFill;
    if (f == etaIdx.length) {
      etaIdx = Arrays.copyOf(etaIdx, f * 2);
      etaVal = Arrays.copyOf(etaVal, f * 2);
    }
    etaIdx[f] = u;
    etaVal[f] = mu;
    etaFill = f + 1;
    int[] rp = urPos[u];
    double[] rv = urVal[u];
    for (int e = 0; e < urLen[u]; e++) {
      rowWork[rp[e]] -= mu * rv[e];
    }
    ops += urLen[u];
    return pivot - mu * spike[pivotRow[u]];
  }

  // the spike entry of step s joins U in column r, unless it is too small
  private void spikeEntry(int r, int s) {
    double v = spike[pivotRow[s]];
    if (Math.abs(v) > DROP) {
      addToColumn(r, s, v);
      addToRow(s, r, v);
      uNonzeros++;
    }
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
    int[] cs = ucRow[k];
    int i = pivotRow[s];
    for (int e = 0; e < ucLen[k]; e++) {
      if (cs[e] == i) {
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
    if (ucLen[k] == ucRow[k].length) {
      int size = Math.max(4, ucLen[k] * 2);
      ucRow[k] = Arrays.copyOf(ucRow[k], size);
      ucVal[k] = Arrays.copyOf(ucVal[k], size);
    }
    ucRow[k][ucLen[k]] = pivotRow[s];
    ucVal[k][ucLen[k]++] = v;
  }
}
