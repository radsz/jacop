/*
 * Presolve.java
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
import java.util.HashMap;

/**
 * A presolve of the problem of a {@link RevisedDualSimplex} for its first solve, with a postsolve
 * of the basis only. The reductions are those of Andersen and Andersen, "Presolving in linear
 * programming", Mathematical Programming 71 (1995) 221-245, that keep a basis easy to recover:
 * empty, singleton and redundant rows (and row bounds that the column bounds imply), empty, fixed
 * and dominated columns (dual fixing: a column whose cost and entries all pull it to one bound is
 * fixed there), implied free column singletons, doubleton equations (one column of the equation is
 * substituted by the other), parallel rows (a row that is a multiple of another gives its bounds to
 * the other and goes) and parallel columns (a column that is a multiple of another, in its entries
 * and its cost, is merged into it, which then stands for their sum).
 *
 * <p>The problem is the internal one of the simplex, already scaled: the rows {@code L_i <= a_i x
 * <= U_i} with the slack of row i as column {@code n + i}, and the perturbed costs. The reduced
 * problem is solved from its slack basis; {@link #postsolve} then makes a basis of the whole
 * problem from the reduced one, computing the duals of the removed rows on the way, in the reverse
 * order of the reductions and over the columns as they were when each was made (Andersen and
 * Andersen, section 4), so that the basis stays optimal and the simplex of the whole problem ends
 * after few or no pivots. Only the basis comes back: the values, duals and certificates are those
 * of the whole problem, from its own factorization.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Presolve {

  // a row or column bound closer than this, relative, is the same bound
  private static final double SAME = 1e-9;

  // a row violated by more than this by its activity bounds: the presolve gives up
  private static final double INFEASIBLE = 1e-6;

  // a pivot of a reduction (singleton row, free column, doubleton) smaller than this is not taken
  private static final double SMALL_ENTRY = 1e-7;

  // an entry of a substitution that becomes smaller than this, relative to the entries it came
  // from, cancels
  private static final double CANCEL = 1e-12;

  // a doubleton is substituted only when the ratio of its entries is at most this
  private static final double DOUBLETON_RATIO = 1e3;

  private static final int MAX_PASSES = 20;

  // the kinds of the reductions, in the order they were made
  private static final byte DROP_ROW = 0;
  private static final byte SINGLETON = 1;
  private static final byte FIX_COLUMN = 2;
  private static final byte FREE_COLUMN = 3;
  private static final byte DOUBLETON = 4;
  static final byte PARALLEL_ROW = 5;
  private static final byte PARALLEL_COLUMN = 6;

  // entries of parallel rows or columns, and costs of parallel columns, that differ by more than
  // this, relative, from the multiple are not parallel
  private static final double PARALLEL = 1e-12;

  // the rounds of the passes and of the search for parallel rows and columns
  private static final int MAX_ROUNDS = 4;

  // whether parallel rows and columns are looked for (org.jacop.jalp.presolveParallel)
  private static final boolean PARALLEL_RULES =
      Boolean.parseBoolean(System.getProperty("org.jacop.jalp.presolveParallel", "true"));

  private final int n;
  private final int m;

  // the matrix as the reductions leave it: an entry is gone when its row or column is, or when it
  // is 0 (cancelled)
  private final int[][] rIdx;
  private final double[][] rVal;
  private final int[] rLen;
  private final int[][] cIdx;
  private final double[][] cVal;
  private final int[] cLen;

  private final double[] cost;
  // the costs of the reduced problem, perturbed and not: a substituted column moves its cost onto
  // the other columns of its row
  private final double[] wcost;
  private final double[] wtrue;

  // the bounds as they are at the end of the presolve, and the column bounds as given
  private final double[] lo;
  private final double[] hi;
  private final double[] givenLo;
  private final double[] givenHi;
  private final double[] rowLo;
  private final double[] rowHi;

  private final boolean[] rowAlive;
  private final boolean[] colAlive;
  private final int[] rowCount;
  private final int[] colCount;

  // the reductions: kind, row, column (the one removed), a second column, numbers and flags, and
  // the lengths of the column histories at the time
  private byte[] kind = new byte[16];
  private int[] recRow = new int[16];
  private int[] recCol = new int[16];
  private int[] recOther = new int[16];
  private double[][] recNum = new double[9][16];
  private byte[] recFlag = new byte[16];
  // the history of each column for the postsolve: its entries as given, then each change a
  // substitution made to one (row, change); the column as it was at a reduction is a prefix of
  // it, whose length the reduction keeps (recLenA for its column, recLenB for the other column of
  // a doubleton)
  private int[] recLenA = new int[16];
  private int[] recLenB = new int[16];
  private final int[][] logRow;
  private final double[][] logVal;
  private final int[] logLen;
  private final boolean[] logOwned;
  private int records;

  // the value of each removed column
  private final double[] fixedAt;

  private int rowsLeft;
  private int colsLeft;
  private long ops;
  // a row bound was dropped as implied by the column bounds
  private boolean relaxed;

  // the reduced problem: the old index of each new row and column, the new index of each old one
  int[] oldRow;
  int[] oldCol;
  int[] newRow;
  int[] newCol;

  /**
   * Prepares the presolve of a problem; nothing is changed in the arrays given, except for the
   * perturbation of the costs (see below).
   *
   * @param n the structural columns
   * @param rowIdx the columns of each row
   * @param rowVal the entries of each row
   * @param colIdx the rows of each column
   * @param colVal the entries of each column
   * @param colLen the length of each column
   * @param cost the perturbed costs of the structural columns; the perturbation of a column without
   *     cost that dual fixing puts at its upper bound changes sign
   * @param trueCost the costs without the perturbation
   * @param bLo the lower bounds of the n structural columns and then of the m slacks
   * @param bHi the upper bounds, the same way
   */
  Presolve(
      int n,
      int[][] rowIdx,
      double[][] rowVal,
      int[][] colIdx,
      double[][] colVal,
      int[] colLen,
      double[] cost,
      double[] trueCost,
      double[] bLo,
      double[] bHi) {
    this.n = n;
    this.m = rowIdx.length;
    this.cost = cost;
    rIdx = new int[m][];
    rVal = new double[m][];
    rLen = new int[m];
    rowCount = new int[m];
    for (int i = 0; i < m; i++) {
      rIdx[i] = rowIdx[i].clone();
      rVal[i] = rowVal[i].clone();
      rLen[i] = rIdx[i].length;
      rowCount[i] = rLen[i];
      ops += rLen[i];
    }
    cIdx = new int[n][];
    cVal = new double[n][];
    cLen = new int[n];
    colCount = new int[n];
    for (int j = 0; j < n; j++) {
      cIdx[j] = Arrays.copyOf(colIdx[j], Math.max(colLen[j], 1));
      cVal[j] = Arrays.copyOf(colVal[j], Math.max(colLen[j], 1));
      cLen[j] = colLen[j];
      colCount[j] = colLen[j];
    }
    wcost = Arrays.copyOf(cost, n);
    wtrue = Arrays.copyOf(trueCost, n);
    lo = Arrays.copyOf(bLo, n);
    hi = Arrays.copyOf(bHi, n);
    givenLo = Arrays.copyOf(bLo, n);
    givenHi = Arrays.copyOf(bHi, n);
    rowLo = Arrays.copyOfRange(bLo, n, n + m);
    rowHi = Arrays.copyOfRange(bHi, n, n + m);
    rowAlive = new boolean[m];
    colAlive = new boolean[n];
    fixedAt = new double[n];
    logRow = colIdx.clone();
    logVal = colVal.clone();
    logLen = colLen.clone();
    logOwned = new boolean[n];
    Arrays.fill(rowAlive, true);
    Arrays.fill(colAlive, true);
    rowsLeft = m;
    colsLeft = n;
  }

  /**
   * Reduces the problem.
   *
   * @return whether anything was removed; false also when the bounds proved the problem infeasible
   *     (the simplex then finds and proves that on the whole problem)
   */
  boolean run() {
    for (int round = 0; round < MAX_ROUNDS; round++) {
      if (!passes()) {
        return false;
      }
      if (!PARALLEL_RULES) {
        break;
      }
      int found = parallelRows();
      if (found < 0) {
        return false;
      }
      found += parallelColumns();
      if (found == 0) {
        break;
      }
    }
    if (rowsLeft == m && colsLeft == n && !relaxed) {
      return false;
    }
    newRow = new int[m];
    newCol = new int[n];
    oldRow = new int[rowsLeft];
    oldCol = new int[colsLeft];
    int k = 0;
    for (int i = 0; i < m; i++) {
      newRow[i] = rowAlive[i] ? k : -1;
      if (rowAlive[i]) {
        oldRow[k++] = i;
      }
    }
    k = 0;
    for (int j = 0; j < n; j++) {
      newCol[j] = colAlive[j] ? k : -1;
      if (colAlive[j]) {
        oldCol[k++] = j;
      }
    }
    return true;
  }

  // the passes over the rows and columns until nothing changes; false when the bounds cannot hold
  private boolean passes() {
    boolean changed = true;
    for (int pass = 0; changed && pass < MAX_PASSES; pass++) {
      changed = false;
      for (int i = 0; i < m; i++) {
        if (rowAlive[i]) {
          int r = reduceRow(i);
          if (r < 0) {
            return false;
          }
          changed |= r > 0;
        }
      }
      for (int j = 0; j < n; j++) {
        if (colAlive[j]) {
          int r = reduceColumn(j);
          if (r < 0) {
            return false;
          }
          changed |= r > 0;
        }
      }
    }
    return true;
  }

  /**
   * Returns the work of the presolve, in the units of {@link RevisedDualSimplex#work()}.
   *
   * @return the work
   */
  long ops() {
    return ops;
  }

  int rowsLeft() {
    return rowsLeft;
  }

  int columnsLeft() {
    return colsLeft;
  }

  /**
   * Returns how many reductions of each kind were made: rows dropped, singleton rows, columns
   * fixed, free columns, doubletons, parallel rows, parallel columns.
   *
   * @return the counts
   */
  int[] counts() {
    int[] c = new int[7];
    for (int t = 0; t < records; t++) {
      c[kind[t]]++;
    }
    return c;
  }

  // 1 when the row was reduced, 0 when not, -1 when its bounds cannot hold
  private int reduceRow(int i) {
    int[] idx = rIdx[i];
    double[] val = rVal[i];
    int len = rLen[i];
    ops += len;
    if (rowCount[i] == 0) {
      if (rowLo[i] > INFEASIBLE || rowHi[i] < -INFEASIBLE) {
        return -1;
      }
      dropRow(i);
      return 1;
    }
    if (rowCount[i] == 1) {
      int e = 0;
      while (!colAlive[idx[e]] || val[e] == 0) {
        e++;
      }
      if (Math.abs(val[e]) >= SMALL_ENTRY) {
        return singleton(i, idx[e], val[e]);
      }
    }
    // the activity bounds of the row over the column bounds, with the infinite terms counted
    double min = 0;
    double max = 0;
    int minInf = 0;
    int maxInf = 0;
    for (int e = 0; e < len; e++) {
      int j = idx[e];
      double a = val[e];
      if (!colAlive[j] || a == 0) {
        continue;
      }
      double l = a > 0 ? lo[j] : hi[j];
      double h = a > 0 ? hi[j] : lo[j];
      if (Double.isInfinite(l)) {
        minInf++;
      } else {
        min += a * l;
      }
      if (Double.isInfinite(h)) {
        maxInf++;
      } else {
        max += a * h;
      }
    }
    if (minInf == 0 && min > rowHi[i] + INFEASIBLE * (1 + Math.abs(rowHi[i]))
        || maxInf == 0 && max < rowLo[i] - INFEASIBLE * (1 + Math.abs(rowLo[i]))) {
      return -1;
    }
    boolean loHolds =
        rowLo[i] == Double.NEGATIVE_INFINITY
            || minInf == 0 && min >= rowLo[i] - SAME * (1 + Math.abs(rowLo[i]));
    boolean hiHolds =
        rowHi[i] == Double.POSITIVE_INFINITY
            || maxInf == 0 && max <= rowHi[i] + SAME * (1 + Math.abs(rowHi[i]));
    if (loHolds && hiHolds) {
      dropRow(i);
      return 1;
    }
    int r = 0;
    if (loHolds && rowLo[i] != Double.NEGATIVE_INFINITY) {
      rowLo[i] = Double.NEGATIVE_INFINITY;
      relaxed = true;
      r = 1;
    }
    if (hiHolds && rowHi[i] != Double.POSITIVE_INFINITY) {
      rowHi[i] = Double.POSITIVE_INFINITY;
      relaxed = true;
      r = 1;
    }
    if (rowCount[i] == 2 && rowLo[i] == rowHi[i]) {
      return doubleton(i);
    }
    return r;
  }

  // the row of one column a x in [L, U] becomes bounds of the column
  private int singleton(int i, int j, double a) {
    double l = a > 0 ? rowLo[i] / a : rowHi[i] / a;
    double h = a > 0 ? rowHi[i] / a : rowLo[i] / a;
    byte tight = 0;
    if (raises(l, lo[j])) {
      lo[j] = l;
      tight |= 1;
    }
    if (lowers(h, hi[j])) {
      hi[j] = h;
      tight |= 2;
    }
    if (lo[j] > hi[j]) {
      if (lo[j] > hi[j] + INFEASIBLE * (1 + Math.abs(hi[j]))) {
        return -1;
      }
      // within the tolerance: one value, the bound the row set
      if ((tight & 1) != 0) {
        hi[j] = lo[j];
      } else {
        lo[j] = hi[j];
      }
    }
    int t = record(SINGLETON, i, j);
    recNum[0][t] = a;
    recNum[1][t] = rowLo[i];
    recNum[2][t] = rowHi[i];
    recNum[3][t] = wcost[j];
    recFlag[t] = tight;
    recLenA[t] = logLen[j];
    removeRow(i);
    return 1;
  }

  // 1 when the column was removed, 0 when not
  private int reduceColumn(int j) {
    ops += cLen[j];
    if (lo[j] == hi[j]
        || !Double.isInfinite(lo[j])
            && !Double.isInfinite(hi[j])
            && hi[j] - lo[j] <= SAME * (1 + Math.abs(lo[j]))) {
      fixColumn(j, lo[j]);
      return 1;
    }
    // dual fixing: lowering the column keeps every row feasible (its entries meet only rows with no
    // lower bound when positive, no upper bound when negative), and the cost asks for it; a column
    // without cost may go either way, whatever the sign of its perturbation
    double c = wtrue[j];
    boolean down = c >= 0;
    boolean up = c <= 0;
    int[] ci = cIdx[j];
    double[] cv = cVal[j];
    for (int e = 0; e < cLen[j] && (down || up); e++) {
      int i = ci[e];
      double a = cv[e];
      if (!rowAlive[i] || a == 0) {
        continue;
      }
      boolean noLo = rowLo[i] == Double.NEGATIVE_INFINITY;
      boolean noHi = rowHi[i] == Double.POSITIVE_INFINITY;
      if (a > 0 ? !noLo : !noHi) {
        down = false;
      }
      if (a > 0 ? !noHi : !noLo) {
        up = false;
      }
    }
    boolean canDown = down && lo[j] != Double.NEGATIVE_INFINITY;
    boolean canUp = up && hi[j] != Double.POSITIVE_INFINITY;
    if (canDown && (!canUp || wcost[j] >= 0)) {
      if (wcost[j] < 0) {
        flipPerturbation(j, c);
      }
      fixColumn(j, lo[j]);
      return 1;
    }
    if (canUp) {
      if (wcost[j] > 0) {
        flipPerturbation(j, c);
      }
      fixColumn(j, hi[j]);
      return 1;
    }
    if (colCount[j] == 1) {
      return freeColumn(j);
    }
    return 0;
  }

  // the perturbation of a column without cost changes sign, here and in the simplex
  private void flipPerturbation(int j, double c) {
    double delta = 2 * (c - wcost[j]);
    wcost[j] += delta;
    cost[j] += delta;
  }

  // the entry of the only row of column k
  private int onlyEntry(int k) {
    int e = 0;
    while (!rowAlive[cIdx[k][e]] || cVal[k][e] == 0) {
      e++;
    }
    return e;
  }

  // a column in one row only, whose bounds that row implies (an implied free column singleton):
  // the row fixes it, so both go and its cost moves onto the other columns of the row; an
  // inequality row is held at the bound the cost of the column pushes it to
  private int freeColumn(int k) {
    int e = onlyEntry(k);
    int i = cIdx[k][e];
    double a = cVal[k][e];
    if (Math.abs(a) < SMALL_ENTRY) {
      return 0;
    }
    // with x_k = (s - rest) / a the slack costs c_k / a: it ends at the bound that lowers the
    // objective
    double ratio = wcost[k] / a;
    boolean slackUpper;
    double b;
    if (rowLo[i] == rowHi[i]) {
      b = rowLo[i];
      slackUpper = false;
    } else if (ratio > 0 && rowLo[i] != Double.NEGATIVE_INFINITY) {
      b = rowLo[i];
      slackUpper = false;
    } else if (ratio < 0 && rowHi[i] != Double.POSITIVE_INFINITY) {
      b = rowHi[i];
      slackUpper = true;
    } else {
      return 0;
    }
    if (!impliedFree(i, k, a, b)) {
      return 0;
    }
    int t = record(FREE_COLUMN, i, k);
    recNum[0][t] = a;
    recNum[3][t] = ratio;
    recFlag[t] = (byte) (slackUpper ? 2 : 0);
    double tr = wtrue[k] / a;
    int[] idx = rIdx[i];
    double[] val = rVal[i];
    for (int f = 0; f < rLen[i]; f++) {
      int j = idx[f];
      if (j != k && colAlive[j] && val[f] != 0) {
        wcost[j] -= ratio * val[f];
        wtrue[j] -= tr * val[f];
      }
    }
    colAlive[k] = false;
    colsLeft--;
    removeRow(i);
    return 1;
  }

  // whether x_k = (b - rest) / a stays within the bounds of x_k for every value of the rest of row
  // i
  private boolean impliedFree(int i, int k, double a, double b) {
    double min = 0;
    double max = 0;
    int minInf = 0;
    int maxInf = 0;
    int[] idx = rIdx[i];
    double[] val = rVal[i];
    ops += rLen[i];
    for (int f = 0; f < rLen[i]; f++) {
      int j = idx[f];
      double v = val[f];
      if (j == k || !colAlive[j] || v == 0) {
        continue;
      }
      double l = v > 0 ? lo[j] : hi[j];
      double h = v > 0 ? hi[j] : lo[j];
      if (Double.isInfinite(l)) {
        minInf++;
      } else {
        min += v * l;
      }
      if (Double.isInfinite(h)) {
        maxInf++;
      } else {
        max += v * h;
      }
    }
    double kLo;
    double kHi;
    if (a > 0) {
      kLo = maxInf > 0 ? Double.NEGATIVE_INFINITY : (b - max) / a;
      kHi = minInf > 0 ? Double.POSITIVE_INFINITY : (b - min) / a;
    } else {
      kLo = minInf > 0 ? Double.NEGATIVE_INFINITY : (b - min) / a;
      kHi = maxInf > 0 ? Double.POSITIVE_INFINITY : (b - max) / a;
    }
    return (lo[k] == Double.NEGATIVE_INFINITY || kLo >= lo[k] - SAME * (1 + Math.abs(lo[k])))
        && (hi[k] == Double.POSITIVE_INFINITY || kHi <= hi[k] + SAME * (1 + Math.abs(hi[k])));
  }

  // an equation a_j x_j + a_k x_k = b: x_k = (b - a_j x_j) / a_k is substituted into the other rows
  // of x_k, its bounds become bounds of x_j, and the row and x_k go
  private int doubleton(int i) {
    int[] idx = rIdx[i];
    double[] val = rVal[i];
    int e1 = -1;
    int e2 = -1;
    for (int e = 0; e < rLen[i]; e++) {
      if (colAlive[idx[e]] && val[e] != 0) {
        if (e1 < 0) {
          e1 = e;
        } else {
          e2 = e;
        }
      }
    }
    int p = idx[e1];
    int q = idx[e2];
    double ap = val[e1];
    double aq = val[e2];
    // the column substituted: the shorter one, unless its entry is much the smaller
    int k = colCount[q] < colCount[p] ? q : p;
    int j = k == p ? q : p;
    double ak = k == p ? ap : aq;
    double aj = k == p ? aq : ap;
    if (Math.abs(aj) > DOUBLETON_RATIO * Math.abs(ak)) {
      int s = k;
      k = j;
      j = s;
      double v = ak;
      ak = aj;
      aj = v;
    }
    if (Math.abs(ak) < SMALL_ENTRY
        || Math.abs(aj) < SMALL_ENTRY
        || Math.abs(aj) > DOUBLETON_RATIO * Math.abs(ak)) {
      return 0;
    }
    double b = rowLo[i];
    // the range of x_j = (b - a_k x_k) / a_j over the bounds of x_k
    double r = ak / aj;
    double fromLo =
        lo[k] == Double.NEGATIVE_INFINITY
            ? (r > 0 ? 1 : -1) * Double.POSITIVE_INFINITY
            : (b - ak * lo[k]) / aj;
    double fromHi =
        hi[k] == Double.POSITIVE_INFINITY
            ? (r > 0 ? -1 : 1) * Double.POSITIVE_INFINITY
            : (b - ak * hi[k]) / aj;
    double jl = Math.min(fromLo, fromHi);
    double jh = Math.max(fromLo, fromHi);
    byte tight = 0;
    double newLo = lo[j];
    double newHi = hi[j];
    if (raises(jl, newLo)) {
      newLo = jl;
      tight |= 1;
    }
    if (lowers(jh, newHi)) {
      newHi = jh;
      tight |= 2;
    }
    if (newLo > newHi) {
      if (newLo > newHi + INFEASIBLE * (1 + Math.abs(newHi))) {
        return -1;
      }
      if ((tight & 1) != 0) {
        newHi = newLo;
      } else {
        newLo = newHi;
      }
    }
    int t = record(DOUBLETON, i, k);
    recOther[t] = j;
    recNum[0][t] = ak;
    recNum[1][t] = aj;
    recNum[2][t] = b;
    recNum[3][t] = wcost[k];
    recNum[4][t] = wcost[j];
    recNum[5][t] = lo[k];
    recNum[6][t] = hi[k];
    // the bounds x_j has after the substitution
    recNum[7][t] = newLo;
    recNum[8][t] = newHi;
    recFlag[t] = tight;
    recLenA[t] = logLen[k];
    recLenB[t] = logLen[j];
    lo[j] = newLo;
    hi[j] = newHi;
    // the cost of x_k onto x_j
    wcost[j] -= wcost[k] * aj / ak;
    wtrue[j] -= wtrue[k] * aj / ak;
    removeRow(i);
    colAlive[k] = false;
    colsLeft--;
    int[] ci = cIdx[k];
    double[] cv = cVal[k];
    for (int e = 0; e < cLen[k]; e++) {
      int row = ci[e];
      double a = cv[e];
      if (!rowAlive[row] || a == 0) {
        continue;
      }
      rowCount[row]--;
      // a x_k = a (b - a_j x_j) / a_k
      double shift = a * b / ak;
      if (shift != 0) {
        rowLo[row] -= shift;
        rowHi[row] -= shift;
      }
      addEntry(row, j, -a * aj / ak);
    }
    ops += cLen[k];
    return 1;
  }

  // rows whose entries over the columns left are multiples of each other: the later one goes and
  // its bounds, divided by the multiple, tighten the bounds of the other (Andersen and Andersen,
  // section 3.4); the number removed, or -1 when the bounds cannot hold
  private int parallelRows() {
    int[] cols = new int[n];
    double[] vals = new double[n];
    double[] dense = new double[n];
    int[][] keptCols = new int[m][];
    double[][] keptVals = new double[m][];
    int[] next = new int[m];
    HashMap<Long, Integer> first = new HashMap<>();
    int found = 0;
    for (int i = 0; i < m; i++) {
      if (!rowAlive[i] || rowCount[i] < 2) {
        continue;
      }
      int len = gather(rIdx[i], rVal[i], rLen[i], colAlive, cols, vals, dense);
      long h = hash(cols, vals, len);
      Integer head = first.get(h);
      int k = head == null ? -1 : head;
      while (k >= 0) {
        double lambda = multiple(keptCols[k], keptVals[k], cols, vals, len);
        if (lambda != 0) {
          if (mergeRows(k, i, lambda) < 0) {
            return -1;
          }
          found++;
          break;
        }
        k = next[k];
      }
      if (k < 0) {
        keptCols[i] = Arrays.copyOf(cols, len);
        keptVals[i] = Arrays.copyOf(vals, len);
        next[i] = head == null ? -1 : head;
        first.put(h, i);
      }
    }
    return found;
  }

  // row i is lambda times row k: s_i = lambda s_k, so the bounds of s_i bound s_k
  private int mergeRows(int k, int i, double lambda) {
    double l = lambda > 0 ? rowLo[i] / lambda : rowHi[i] / lambda;
    double h = lambda > 0 ? rowHi[i] / lambda : rowLo[i] / lambda;
    byte tight = 0;
    if (raises(l, rowLo[k])) {
      rowLo[k] = l;
      tight |= 1;
    }
    if (lowers(h, rowHi[k])) {
      rowHi[k] = h;
      tight |= 2;
    }
    if (rowLo[k] > rowHi[k]) {
      if (rowLo[k] > rowHi[k] + INFEASIBLE * (1 + Math.abs(rowHi[k]))) {
        return -1;
      }
      if ((tight & 1) != 0) {
        rowHi[k] = rowLo[k];
      } else {
        rowLo[k] = rowHi[k];
      }
    }
    int t = record(PARALLEL_ROW, i, -1);
    recOther[t] = k;
    recNum[0][t] = lambda;
    recFlag[t] = tight;
    removeRow(i);
    return 1;
  }

  // columns whose entries over the rows left and whose costs are multiples of each other: x_k =
  // lambda x_j in all rows and in the objective, so the later one, x_k, goes and x_j stands for x_j
  // + lambda x_k, with the bounds of that sum (Andersen and Andersen, section 3.6). The costs
  // compared are those without the perturbation; the reduced problem keeps the perturbed cost of
  // x_j, and the solve of the whole problem makes up for the perturbation of x_k
  private int parallelColumns() {
    int[] rows = new int[m];
    double[] vals = new double[m];
    double[] dense = new double[m];
    int[][] keptRows = new int[n][];
    double[][] keptVals = new double[n][];
    int[] next = new int[n];
    HashMap<Long, Integer> first = new HashMap<>();
    int found = 0;
    for (int k = 0; k < n; k++) {
      if (!colAlive[k] || colCount[k] < 1) {
        continue;
      }
      int len = gather(cIdx[k], cVal[k], cLen[k], rowAlive, rows, vals, dense);
      long h = hash(rows, vals, len);
      Integer head = first.get(h);
      int j = head == null ? -1 : head;
      boolean free = lo[k] == Double.NEGATIVE_INFINITY && hi[k] == Double.POSITIVE_INFINITY;
      while (j >= 0 && !free) {
        double lambda = multiple(keptRows[j], keptVals[j], rows, vals, len);
        if (lambda != 0 && sameMultiple(wtrue[k], lambda * wtrue[j])) {
          mergeColumns(j, k, lambda);
          found++;
          break;
        }
        j = next[j];
      }
      if (free || j < 0) {
        keptRows[k] = Arrays.copyOf(rows, len);
        keptVals[k] = Arrays.copyOf(vals, len);
        next[k] = head == null ? -1 : head;
        first.put(h, k);
      }
    }
    return found;
  }

  // column k is lambda times column j: x_j + lambda x_k takes the place of x_j
  private void mergeColumns(int j, int k, double lambda) {
    double newLo = lo[j] + (lambda > 0 ? lambda * lo[k] : lambda * hi[k]);
    double newHi = hi[j] + (lambda > 0 ? lambda * hi[k] : lambda * lo[k]);
    int t = record(PARALLEL_COLUMN, -1, k);
    recOther[t] = j;
    recNum[0][t] = lambda;
    recNum[1][t] = lo[j];
    recNum[2][t] = hi[j];
    recNum[3][t] = lo[k];
    recNum[4][t] = hi[k];
    recNum[5][t] = newLo;
    recNum[6][t] = newHi;
    recNum[7][t] = wcost[j];
    recLenA[t] = logLen[j];
    lo[j] = newLo;
    hi[j] = newHi;
    colAlive[k] = false;
    colsLeft--;
    int[] ci = cIdx[k];
    double[] cv = cVal[k];
    ops += cLen[k];
    for (int e = 0; e < cLen[k]; e++) {
      if (rowAlive[ci[e]] && cv[e] != 0) {
        rowCount[ci[e]]--;
      }
    }
  }

  // the entries of a row or column over the columns or rows left, sorted by index, into idx and
  // val; the count. dense is all 0 and is left so
  private int gather(
      int[] at, double[] of, int len, boolean[] alive, int[] idx, double[] val, double[] dense) {
    int count = 0;
    ops += len;
    for (int e = 0; e < len; e++) {
      if (alive[at[e]] && of[e] != 0) {
        idx[count++] = at[e];
        dense[at[e]] = of[e];
      }
    }
    Arrays.sort(idx, 0, count);
    for (int e = 0; e < count; e++) {
      val[e] = dense[idx[e]];
      dense[idx[e]] = 0;
    }
    return count;
  }

  // a hash of the indices and of the entries divided by the first, rounded, so that multiples of
  // each other have the same hash
  private static long hash(int[] idx, double[] val, int len) {
    long h = len;
    for (int e = 0; e < len; e++) {
      h = h * 0x9E3779B97F4A7C15L + idx[e];
      h = h * 31 + Math.round(val[e] / val[0] * 1e6);
    }
    return h;
  }

  // lambda when the entries given are lambda times the entries kept (same indices), else 0
  private double multiple(int[] keptIdx, double[] keptVal, int[] idx, double[] val, int len) {
    if (keptIdx.length != len) {
      return 0;
    }
    ops += len;
    double lambda = val[0] / keptVal[0];
    for (int e = 0; e < len; e++) {
      if (idx[e] != keptIdx[e] || !sameMultiple(val[e], lambda * keptVal[e])) {
        return 0;
      }
    }
    return lambda;
  }

  private static boolean sameMultiple(double a, double b) {
    return Math.abs(a - b) <= PARALLEL * Math.max(Math.abs(a), Math.abs(b));
  }

  // adds f to the entry of column j in row i, with fill-in and cancellation
  private void addEntry(int i, int j, double f) {
    int[] idx = rIdx[i];
    double[] val = rVal[i];
    ops += rLen[i];
    for (int e = 0; e < rLen[i]; e++) {
      if (idx[e] == j) {
        double old = val[e];
        double v = old + f;
        boolean wasAlive = old != 0;
        if (Math.abs(v) <= CANCEL * Math.max(Math.abs(old), Math.abs(f))) {
          v = 0;
        }
        val[e] = v;
        setColumnEntry(j, i, v);
        logChange(j, i, v - old);
        if (wasAlive && v == 0) {
          rowCount[i]--;
          colCount[j]--;
        } else if (!wasAlive && v != 0) {
          rowCount[i]++;
          colCount[j]++;
        }
        return;
      }
    }
    if (rLen[i] == idx.length) {
      rIdx[i] = idx = Arrays.copyOf(idx, idx.length * 2 + 1);
      rVal[i] = val = Arrays.copyOf(val, val.length * 2 + 1);
    }
    idx[rLen[i]] = j;
    val[rLen[i]++] = f;
    rowCount[i]++;
    if (cLen[j] == cIdx[j].length) {
      cIdx[j] = Arrays.copyOf(cIdx[j], cIdx[j].length * 2 + 1);
      cVal[j] = Arrays.copyOf(cVal[j], cVal[j].length * 2 + 1);
    }
    cIdx[j][cLen[j]] = i;
    cVal[j][cLen[j]++] = f;
    colCount[j]++;
    logChange(j, i, f);
  }

  private void setColumnEntry(int j, int i, double v) {
    int[] ci = cIdx[j];
    ops += cLen[j];
    for (int e = 0; e < cLen[j]; e++) {
      if (ci[e] == i) {
        cVal[j][e] = v;
        return;
      }
    }
  }

  private void dropRow(int i) {
    record(DROP_ROW, i, -1);
    removeRow(i);
  }

  private void removeRow(int i) {
    rowAlive[i] = false;
    rowsLeft--;
    int[] idx = rIdx[i];
    double[] val = rVal[i];
    ops += rLen[i];
    for (int e = 0; e < rLen[i]; e++) {
      if (colAlive[idx[e]] && val[e] != 0) {
        colCount[idx[e]]--;
      }
    }
  }

  // the column is removed at value v, which moves the bounds of its rows
  private void fixColumn(int j, double v) {
    record(FIX_COLUMN, -1, j);
    fixedAt[j] = v;
    colAlive[j] = false;
    colsLeft--;
    int[] ci = cIdx[j];
    double[] cv = cVal[j];
    ops += cLen[j];
    for (int e = 0; e < cLen[j]; e++) {
      int i = ci[e];
      if (rowAlive[i] && cv[e] != 0) {
        rowCount[i]--;
        if (v != 0) {
          rowLo[i] -= cv[e] * v;
          rowHi[i] -= cv[e] * v;
        }
      }
    }
  }

  private int record(byte k, int i, int j) {
    if (records == kind.length) {
      int c = records * 2;
      kind = Arrays.copyOf(kind, c);
      recRow = Arrays.copyOf(recRow, c);
      recCol = Arrays.copyOf(recCol, c);
      recOther = Arrays.copyOf(recOther, c);
      for (int q = 0; q < recNum.length; q++) {
        recNum[q] = Arrays.copyOf(recNum[q], c);
      }
      recFlag = Arrays.copyOf(recFlag, c);
      recLenA = Arrays.copyOf(recLenA, c);
      recLenB = Arrays.copyOf(recLenB, c);
    }
    kind[records] = k;
    recRow[records] = i;
    recCol[records] = j;
    return records++;
  }

  // a substitution changed the entry of column j in row i by f
  private void logChange(int j, int i, double f) {
    if (!logOwned[j] || logLen[j] == logRow[j].length) {
      logRow[j] = Arrays.copyOf(logRow[j], logLen[j] * 2 + 2);
      logVal[j] = Arrays.copyOf(logVal[j], logLen[j] * 2 + 2);
      logOwned[j] = true;
    }
    logRow[j][logLen[j]] = i;
    logVal[j][logLen[j]++] = f;
  }

  /**
   * The rows of the reduced problem over its columns, as {@link RevisedDualSimplex} takes them.
   *
   * @param columns filled with the columns of each new row
   * @param weights filled with the entries of each new row
   */
  void reducedRows(int[][] columns, double[][] weights) {
    for (int k = 0; k < oldRow.length; k++) {
      int i = oldRow[k];
      int[] idx = rIdx[i];
      double[] val = rVal[i];
      int[] c = new int[rowCount[i]];
      double[] w = new double[rowCount[i]];
      int len = 0;
      for (int e = 0; e < rLen[i]; e++) {
        if (colAlive[idx[e]] && val[e] != 0) {
          c[len] = newCol[idx[e]];
          w[len++] = val[e];
        }
      }
      columns[k] = c;
      weights[k] = w;
      ops += rLen[i];
    }
  }

  double rowLo(int i) {
    return rowLo[i];
  }

  double rowHi(int i) {
    return rowHi[i];
  }

  /**
   * Returns the cost of a column in the reduced problem, perturbed as in the simplex.
   *
   * @param j the column, by its index in the whole problem
   * @return its cost
   */
  double cost(int j) {
    return wcost[j];
  }

  double columnLo(int j) {
    return lo[j];
  }

  double columnHi(int j) {
    return hi[j];
  }

  /**
   * Makes a basis of the whole problem from an optimal basis of the reduced one. A removed row gets
   * a basic slack, or the column it removed becomes basic, whichever keeps the duals feasible; the
   * dual of the row then follows from the reduced cost of that column (Andersen and Andersen,
   * section 4). A removed column is nonbasic at the bound it was fixed to. A removed parallel row
   * takes the bound and the dual of the row it was merged into when that row's slack sits at a
   * bound the removed row set; a removed parallel column is nonbasic at the bound that, with the
   * bound of the column it was merged into, makes the bound of their sum.
   *
   * @param basicR whether each column of the reduced problem (structural, then slack) is basic
   * @param upperR whether each nonbasic column of the reduced problem is at its upper bound
   * @param valueR the value of each nonbasic structural column of the reduced problem
   * @param yR the dual of each row of the reduced problem (the reduced cost of its slack)
   * @param basic filled with whether each column of the whole problem is basic
   * @param upper filled with whether each nonbasic column of the whole problem is at its upper
   *     bound
   * @return the basic columns, m of them, or null when the counts do not match
   */
  int[] postsolve(
      boolean[] basicR,
      boolean[] upperR,
      double[] valueR,
      double[] yR,
      boolean[] basic,
      boolean[] upper) {
    int nr = oldCol.length;
    double[] y = new double[m];
    double[] value = new double[n];
    for (int k = 0; k < nr; k++) {
      int j = oldCol[k];
      basic[j] = basicR[k];
      upper[j] = upperR[k];
      value[j] = valueR[k];
    }
    for (int k = 0; k < oldRow.length; k++) {
      int i = oldRow[k];
      basic[n + i] = basicR[nr + k];
      upper[n + i] = upperR[nr + k];
      y[i] = basic[n + i] ? 0 : yR[k];
    }
    for (int t = records - 1; t >= 0; t--) {
      int i = recRow[t];
      int j = recCol[t];
      switch (kind[t]) {
        case FIX_COLUMN:
          basic[j] = false;
          value[j] = fixedAt[j];
          upper[j] = fixedAt[j] == givenHi[j] && givenHi[j] != givenLo[j];
          break;
        case DROP_ROW:
          basic[n + i] = true;
          y[i] = 0;
          break;
        case FREE_COLUMN:
          // the column basic, the slack at the bound the row was held to; d_k = 0 sets the dual
          basic[j] = true;
          basic[n + i] = false;
          upper[n + i] = recFlag[t] != 0;
          y[i] = recNum[3][t];
          break;
        case SINGLETON:
          basic[n + i] = true;
          y[i] = 0;
          if (!basic[j] && recFlag[t] != 0) {
            singletonBasis(t, i, j, y, value, basic, upper);
          }
          break;
        case PARALLEL_ROW:
          parallelRowBasis(t, i, recOther[t], y, basic, upper);
          break;
        case PARALLEL_COLUMN:
          parallelColumnBasis(t, j, recOther[t], y, value, basic, upper);
          break;
        default:
          doubletonBasis(t, i, j, recOther[t], y, value, basic, upper);
          break;
      }
    }
    int[] list = new int[m];
    int count = 0;
    for (int j = 0; j < n + m; j++) {
      if (basic[j]) {
        if (count == m) {
          return null;
        }
        list[count++] = j;
      }
    }
    if (count != m) {
      return null;
    }
    // a nonbasic column left inside its bounds goes to the nearer one
    for (int j = 0; j < n; j++) {
      if (!basic[j]
          && value[j] != givenLo[j]
          && value[j] != givenHi[j]
          && givenHi[j] != Double.POSITIVE_INFINITY) {
        upper[j] =
            givenLo[j] == Double.NEGATIVE_INFINITY || givenHi[j] - value[j] < value[j] - givenLo[j];
      }
    }
    return list;
  }

  // the reduced cost of column j, from its cost and its entries as they were: the first len
  // entries of its history. A row removed before that time is postsolved after it, so its dual is
  // still 0 here
  private double reducedCost(double c, int j, int len, double[] y) {
    double d = c;
    int[] r = logRow[j];
    double[] v = logVal[j];
    for (int e = 0; e < len; e++) {
      d -= y[r[e]] * v[e];
    }
    ops += len;
    return d;
  }

  // the column of a singleton row, nonbasic: basic in place of the row's slack when it sits at a
  // bound the row set and its reduced cost pulls it there
  private void singletonBasis(
      int t, int i, int j, double[] y, double[] value, boolean[] basic, boolean[] upper) {
    double a = recNum[0][t];
    double d = reducedCost(recNum[3][t], j, recLenA[t], y);
    double v = value[j];
    double l = a > 0 ? recNum[1][t] / a : recNum[2][t] / a;
    double h = a > 0 ? recNum[2][t] / a : recNum[1][t] / a;
    boolean atHi = (recFlag[t] & 2) != 0 && same(v, h) && d <= 0;
    boolean atLo = (recFlag[t] & 1) != 0 && same(v, l) && d >= 0;
    if (!atHi && !atLo) {
      return;
    }
    // x_j = s_i / a: at its upper bound h the slack is at U when a > 0, at L when a < 0
    basic[j] = true;
    basic[n + i] = false;
    upper[n + i] = atHi == a > 0;
    // the reduced cost of the column becomes 0: d - y_i a = 0
    y[i] = d / a;
  }

  // the substituted column k of the equation a_k x_k + a_j x_j = b: basic, unless x_j sits at a
  // bound that came from a bound of x_k; then x_j is basic and x_k at that bound
  private void doubletonBasis(
      int t, int i, int k, int j, double[] y, double[] value, boolean[] basic, boolean[] upper) {
    double ak = recNum[0][t];
    double aj = recNum[1][t];
    basic[n + i] = false;
    upper[n + i] = false;
    y[i] = 0;
    if (!basic[j] && recFlag[t] != 0) {
      double v = value[j];
      boolean jLow = (recFlag[t] & 1) != 0 && same(v, recNum[7][t]);
      boolean jHigh = (recFlag[t] & 2) != 0 && same(v, recNum[8][t]);
      if (jLow || jHigh) {
        // x_j = (b - a_k x_k) / a_j falls as x_k rises when a_k / a_j > 0
        boolean kUpper = jLow == ak / aj > 0;
        double dj = reducedCost(recNum[4][t], j, recLenB[t], y);
        double yi = dj / aj;
        y[i] = yi;
        double dk = reducedCost(recNum[3][t], k, recLenA[t], y);
        if (kUpper ? dk <= 1e-9 : dk >= -1e-9) {
          basic[j] = true;
          basic[k] = false;
          upper[k] = kUpper;
          value[k] = kUpper ? recNum[6][t] : recNum[5][t];
          return;
        }
        y[i] = 0;
      }
    }
    basic[k] = true;
    y[i] = reducedCost(recNum[3][t], k, recLenA[t], y) / ak;
  }

  // the removed row i, lambda times the kept row k: its slack is basic, unless the slack of row k
  // sits at a bound that row i set; then the slack of row i takes that bound and the dual of row k
  private void parallelRowBasis(int t, int i, int k, double[] y, boolean[] basic, boolean[] upper) {
    basic[n + i] = true;
    y[i] = 0;
    if (basic[n + k]) {
      return;
    }
    // the dual tells the bound the slack is held to: an equality row k (its bounds may have met
    // in mergeRows) is at both, and the reduced solve leaves its flag at either
    boolean atUpper = y[k] < 0 || y[k] == 0 && upper[n + k];
    if ((recFlag[t] & (atUpper ? 2 : 1)) == 0) {
      return;
    }
    double lambda = recNum[0][t];
    // s_i = lambda s_k: at the upper bound of s_k, s_i is at its upper bound when lambda > 0
    basic[n + i] = false;
    upper[n + i] = atUpper == lambda > 0;
    basic[n + k] = true;
    y[i] = y[k] / lambda;
    y[k] = 0;
  }

  // the removed column k, lambda times the kept column j, which stood for x_j + lambda x_k: when
  // x_j is basic, x_k is at a finite bound; when x_j is at a bound of the sum, both are at the
  // bounds that make it
  private void parallelColumnBasis(
      int t, int k, int j, double[] y, double[] value, boolean[] basic, boolean[] upper) {
    double lambda = recNum[0][t];
    double loJ = recNum[1][t];
    double hiJ = recNum[2][t];
    double loK = recNum[3][t];
    double hiK = recNum[4][t];
    basic[k] = false;
    if (basic[j]) {
      upper[k] = loK == Double.NEGATIVE_INFINITY;
      value[k] = upper[k] ? hiK : loK;
      return;
    }
    double v = value[j];
    boolean atHi = recNum[6][t] != Double.POSITIVE_INFINITY && same(v, recNum[6][t]);
    boolean atLo = recNum[5][t] != Double.NEGATIVE_INFINITY && same(v, recNum[5][t]);
    if (atLo && atHi) {
      // the sum fixed: its reduced cost tells the bound that holds it, as for parallel rows
      atLo = reducedCost(recNum[7][t], j, recLenA[t], y) >= 0;
      atHi = !atLo;
    }
    if (atLo) {
      upper[j] = false;
      value[j] = loJ;
      upper[k] = lambda < 0;
    } else if (atHi) {
      upper[j] = true;
      value[j] = hiJ;
      upper[k] = lambda > 0;
    } else {
      // inside the bounds of the sum (a free column at 0): x_k at a finite bound, x_j as it was
      upper[k] = loK == Double.NEGATIVE_INFINITY;
    }
    value[k] = upper[k] ? hiK : loK;
  }

  // whether v is a lower bound above lower bound b by more than the tolerance
  private static boolean raises(double v, double b) {
    return b == Double.NEGATIVE_INFINITY
        ? v != Double.NEGATIVE_INFINITY
        : v > b + SAME * (1 + Math.abs(b));
  }

  // whether v is an upper bound below upper bound b by more than the tolerance
  private static boolean lowers(double v, double b) {
    return b == Double.POSITIVE_INFINITY
        ? v != Double.POSITIVE_INFINITY
        : v < b - SAME * (1 + Math.abs(b));
  }

  private static boolean same(double a, double b) {
    return Math.abs(a - b) <= SAME * (1 + Math.abs(b));
  }
}
