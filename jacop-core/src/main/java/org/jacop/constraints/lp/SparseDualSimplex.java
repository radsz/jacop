/*
 * SparseDualSimplex.java
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
import java.util.Random;

/**
 * A sparse revised bounded-variable dual simplex: the same method as {@link DualSimplex}, but it
 * keeps a sparse LU factorization of the basis ({@link SparseLu}) with eta updates instead of the
 * dense tableau, and builds only the row of the tableau it pivots on. A pivot costs time in the
 * nonzeros of the rows, the factors and the updates rather than in rows times columns, so it fits
 * large sparse relaxations, and rows can be added and removed cheaply.
 *
 * <p>Each pivot does one BTRAN for the row of the basis inverse, one pass over the rows it touches
 * for the row of the tableau, one FTRAN for the entering column, and one more FTRAN for the dual
 * steepest-edge weights. The leaving row is chosen by dual steepest edge, the entering column by
 * the bound-flipping ratio test with Harris tolerances, as in {@link DualSimplex}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SparseDualSimplex implements LpSolver {

  private static final double PERTURBATION = 1e-7;

  // refactorizations after this many updates, against the growth and drift of the eta file
  private static final int REFACTOR_UPDATES = 100;

  // the pivot of the row and of the column must agree this closely, or the basis is refactorized
  private static final double PIVOT_AGREEMENT = 1e-7;

  private int m;
  private final int n;
  private int cols;

  // the rows of A, sparse over the structural columns
  private int[][] rowIdx;
  private double[][] rowVal;

  // the structural columns of A
  private final int[][] colIdx;
  private final double[][] colVal;
  private final int[] colLen;
  private long nonzeros;

  private double[] cost;
  private double[] lo;
  private double[] hi;

  private int[] basis;
  private int[] row; // the row of a basic column, -1 for a nonbasic one
  private boolean[] upper; // a nonbasic column at its upper bound
  private double[] d;
  private double[] beta;
  private double[] weight; // dual steepest edge: the squared norm of each row of B^-1

  // the values of the nonbasic columns that beta was computed with
  private double[] at;
  private boolean betaValid;

  private SparseLu lu;
  private boolean factorValid;

  // the rows from which on the steepest-edge weights are not known yet
  private int weightsFrom;

  private int infeasibleRow = -1;

  // work arrays by row or position, and by column for the row of the tableau
  private double[] rho;
  private double[] work;
  private double[] alphaQ;
  private double[] tau;
  private double[] alphaRow;
  private int[] touched;
  private int touchedCount;
  private boolean[] isTouched;

  // the ratio test, with the columns it flips to their other bound
  private RatioTest ratioTest;

  /** Statistics: pivots made. */
  long totalPivots;

  /** Statistics: factorizations. */
  long factorizations;

  // the work of the loops of this class, and of the factorizations replaced
  private long ops;

  /**
   * Creates the problem with the slack basis.
   *
   * @param a the rows, dense, m by n
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective over the n columns, minimized
   */
  SparseDualSimplex(double[][] a, double[] rowLo, double[] rowHi, double[] cost) {
    this(sparseColumns(a), sparseWeights(a), rowLo, rowHi, cost);
  }

  /**
   * Creates the problem with the slack basis.
   *
   * @param columns the columns of each row
   * @param weights the weights of each row, matching its columns
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective over the n columns, minimized
   */
  SparseDualSimplex(
      int[][] columns, double[][] weights, double[] rowLo, double[] rowHi, double[] cost) {
    this.n = cost.length;
    this.m = 0;
    this.cols = n;
    this.rowIdx = new int[0][];
    this.rowVal = new double[0][];
    this.colIdx = new int[n][];
    this.colVal = new double[n][];
    this.colLen = new int[n];
    for (int j = 0; j < n; j++) {
      colIdx[j] = new int[2];
      colVal[j] = new double[2];
    }
    this.cost = new double[n];
    // the same perturbation of the costs as DualSimplex, against dual degeneracy
    Random rnd = new Random(n * 31L + columns.length);
    for (int j = 0; j < n; j++) {
      this.cost[j] = cost[j] + PERTURBATION * (1 + rnd.nextDouble()) * (1 + Math.abs(cost[j]));
    }
    lo = new double[n];
    hi = new double[n];
    basis = new int[0];
    row = new int[n];
    Arrays.fill(row, -1);
    upper = new boolean[n];
    d = this.cost.clone();
    beta = new double[0];
    weight = new double[0];
    at = new double[n];
    allocateWork();
    appendRows(columns, weights, rowLo, rowHi);
    // the slack basis: B = -I, so every row of B^-1 has norm 1
    Arrays.fill(weight, 1);
    weightsFrom = m;
  }

  // a deep copy of the state of another simplex
  private SparseDualSimplex(SparseDualSimplex o) {
    m = o.m;
    n = o.n;
    cols = o.cols;
    rowIdx = o.rowIdx.clone(); // the rows themselves are never changed
    rowVal = o.rowVal.clone();
    colIdx = new int[n][];
    colVal = new double[n][];
    for (int j = 0; j < n; j++) {
      colIdx[j] = o.colIdx[j].clone();
      colVal[j] = o.colVal[j].clone();
    }
    colLen = o.colLen.clone();
    nonzeros = o.nonzeros;
    cost = o.cost.clone();
    lo = o.lo.clone();
    hi = o.hi.clone();
    basis = o.basis.clone();
    row = o.row.clone();
    upper = o.upper.clone();
    d = o.d.clone();
    beta = o.beta.clone();
    weight = o.weight.clone();
    at = o.at.clone();
    betaValid = false;
    factorValid = false; // the copy factorizes its basis again when it is solved
    weightsFrom = o.weightsFrom;
    infeasibleRow = o.infeasibleRow;
    totalPivots = o.totalPivots;
    factorizations = o.factorizations;
    ops = o.ops + (o.lu == null ? 0 : o.lu.ops);
    lu = null;
    touchedCount = 0;
    allocateWork();
  }

  @Override
  public SparseDualSimplex copy() {
    return new SparseDualSimplex(this);
  }

  private static int[][] sparseColumns(double[][] a) {
    int[][] c = new int[a.length][];
    for (int i = 0; i < a.length; i++) {
      int nz = 0;
      for (double v : a[i]) {
        if (v != 0) {
          nz++;
        }
      }
      c[i] = new int[nz];
      nz = 0;
      for (int j = 0; j < a[i].length; j++) {
        if (a[i][j] != 0) {
          c[i][nz++] = j;
        }
      }
    }
    return c;
  }

  private static double[][] sparseWeights(double[][] a) {
    double[][] w = new double[a.length][];
    for (int i = 0; i < a.length; i++) {
      int nz = 0;
      for (double v : a[i]) {
        if (v != 0) {
          nz++;
        }
      }
      w[i] = new double[nz];
      nz = 0;
      for (double v : a[i]) {
        if (v != 0) {
          w[i][nz++] = v;
        }
      }
    }
    return w;
  }

  private void allocateWork() {
    rho = new double[m];
    work = new double[m];
    alphaQ = new double[m];
    tau = new double[m];
    alphaRow = new double[cols];
    touched = new int[cols];
    isTouched = new boolean[cols];
    ratioTest = new RatioTest(cols);
  }

  // appends rows with basic slacks; the factorization and the values must be rebuilt after
  private void appendRows(int[][] columns, double[][] weights, double[] rowLo, double[] rowHi) {
    int k = columns.length;
    int m2 = m + k;
    int cols2 = cols + k;
    rowIdx = Arrays.copyOf(rowIdx, m2);
    rowVal = Arrays.copyOf(rowVal, m2);
    for (int q = 0; q < k; q++) {
      int i = m + q;
      // duplicates merged, zeros dropped
      int[] cs = columns[q].clone();
      double[] ws = weights[q].clone();
      int len = 0;
      for (int e = 0; e < cs.length; e++) {
        int f = 0;
        while (f < len && cs[f] != cs[e]) {
          f++;
        }
        if (f < len) {
          ws[f] += ws[e];
        } else {
          cs[len] = cs[e];
          ws[len++] = ws[e];
        }
      }
      int keep = 0;
      for (int e = 0; e < len; e++) {
        if (ws[e] != 0) {
          cs[keep] = cs[e];
          ws[keep++] = ws[e];
        }
      }
      rowIdx[i] = Arrays.copyOf(cs, keep);
      rowVal[i] = Arrays.copyOf(ws, keep);
      nonzeros += keep;
      for (int e = 0; e < keep; e++) {
        int j = rowIdx[i][e];
        if (colLen[j] == colIdx[j].length) {
          colIdx[j] = Arrays.copyOf(colIdx[j], colLen[j] * 2);
          colVal[j] = Arrays.copyOf(colVal[j], colLen[j] * 2);
        }
        colIdx[j][colLen[j]] = i;
        colVal[j][colLen[j]++] = rowVal[i][e];
      }
    }
    // the slack of row i is column n + i; the slacks of the old rows keep their columns
    cost = Arrays.copyOf(cost, cols2);
    lo = Arrays.copyOf(lo, cols2);
    hi = Arrays.copyOf(hi, cols2);
    row = Arrays.copyOf(row, cols2);
    upper = Arrays.copyOf(upper, cols2);
    d = Arrays.copyOf(d, cols2);
    at = Arrays.copyOf(at, cols2);
    basis = Arrays.copyOf(basis, m2);
    beta = Arrays.copyOf(beta, m2);
    weight = Arrays.copyOf(weight, m2);
    for (int q = 0; q < k; q++) {
      int s = cols + q;
      lo[s] = rowLo[q];
      hi[s] = rowHi[q];
      basis[m + q] = s;
      row[s] = m + q;
    }
    weightsFrom = Math.min(weightsFrom, m);
    m = m2;
    cols = cols2;
    factorValid = false;
    betaValid = false;
    allocateWork();
  }

  @Override
  public int rows() {
    return m;
  }

  @Override
  public int columns() {
    return n;
  }

  @Override
  public long pivots() {
    return totalPivots;
  }

  // a sparse operation, with its indirect access, against an update of a dense tableau entry
  private static final long OP_COST = 3;

  @Override
  public long work() {
    return OP_COST * (ops + (lu == null ? 0 : lu.ops));
  }

  @Override
  public long pivotWork() {
    // the average so far, and before any pivot the passes over the rows and columns
    long base = OP_COST * (2L * m + cols);
    return totalPivots == 0 ? base : Math.max(base, work() / totalPivots);
  }

  @Override
  public void setBounds(int j, double min, double max) {
    lo[j] = min;
    hi[j] = max;
  }

  @Override
  public int solve(int limit) {
    infeasibleRow = -1;
    if (!factorValid) {
      factorize();
    }
    placeNonbasic();
    updateBeta();
    for (int iter = 0; iter < limit; iter++) {
      ops += 3L * m;
      int r = leavingRow();
      if (r < 0) {
        return OPTIMAL;
      }
      int p = basis[r];
      boolean toLower = beta[r] < lo[p];
      unitRowOfInverse(r, rho);
      pivotRow();
      int q = enteringColumn(toLower, toLower ? lo[p] - beta[r] : beta[r] - hi[p]);
      if (q == RatioTest.NUMERIC) {
        clearTouched();
        return LIMIT;
      }
      if (q < 0) {
        infeasibleRow = r;
        clearTouched();
        return INFEASIBLE;
      }
      column(q, work);
      lu.ftran(work, alphaQ);
      double fromRow = alphaRow[q];
      double fromColumn = alphaQ[r];
      if (lu.updates() > 0
          && Math.abs(fromRow - fromColumn) > PIVOT_AGREEMENT * (1 + Math.abs(fromColumn))) {
        // the updates drifted: start again from a fresh factorization
        clearTouched();
        factorize();
        placeNonbasic();
        updateBeta();
        continue;
      }
      if (ratioTest.flips() > 0) {
        Arrays.fill(work, 0);
        for (int k = 0; k < ratioTest.flips(); k++) {
          int j = ratioTest.flipped(k);
          double old = upper[j] ? hi[j] : lo[j];
          upper[j] = !upper[j];
          double now = upper[j] ? hi[j] : lo[j];
          at[j] = now;
          addColumn(j, now - old, work);
        }
        lu.ftran(work, tau);
        for (int i = 0; i < m; i++) {
          beta[i] -= tau[i];
        }
      }
      // the primal step: x_q moves until x_p reaches the bound it leaves at
      double bound = toLower ? lo[p] : hi[p];
      double theta = (beta[r] - bound) / fromColumn;
      double xq = (upper[q] ? hi[q] : lo[q]) + theta;
      if (theta != 0) {
        for (int i = 0; i < m; i++) {
          double v = alphaQ[i];
          if (v != 0) {
            beta[i] -= v * theta;
          }
        }
      }
      beta[r] = xq;
      // the dual step along the row of the tableau
      double thetaD = d[q] / fromRow;
      for (int t = 0; t < touchedCount; t++) {
        int j = touched[t];
        d[j] -= thetaD * alphaRow[j];
      }
      d[p] = -thetaD;
      d[q] = 0;
      // the steepest-edge weights, from tau = B^-1 rho
      double wr = 0;
      for (int i = 0; i < m; i++) {
        wr += rho[i] * rho[i];
      }
      System.arraycopy(rho, 0, work, 0, m);
      lu.ftran(work, tau);
      for (int i = 0; i < m; i++) {
        double v = alphaQ[i];
        if (i != r && v != 0) {
          double f = v / fromColumn;
          weight[i] = Math.max(weight[i] + f * (f * wr - 2 * tau[i]), 1e-12);
        }
      }
      weight[r] = Math.max(wr / (fromColumn * fromColumn), 1e-12);
      clearTouched();
      lu.update(r, alphaQ);
      basis[r] = q;
      row[q] = r;
      row[p] = -1;
      upper[p] = !toLower;
      at[p] = bound;
      totalPivots++;
      if (lu.updates() >= REFACTOR_UPDATES || lu.updateNonzeros() > 2 * (lu.factorNonzeros + m)) {
        factorize();
        placeNonbasic();
        updateBeta();
      }
    }
    return LIMIT;
  }

  @Override
  public double[] farkas() {
    return inverseRow(infeasibleRow);
  }

  @Override
  public double[] inverseRow(int r) {
    if (!factorValid) {
      factorize();
    }
    double[] y = new double[m];
    unitRowOfInverse(r, y);
    return y;
  }

  @Override
  public double[] duals() {
    if (!factorValid) {
      factorize();
    }
    double[] y = new double[m];
    double[] z = new double[m];
    for (int k = 0; k < m; k++) {
      z[k] = cost[basis[k]];
    }
    lu.btran(z, y);
    return y;
  }

  @Override
  public double objective() {
    double z = 0;
    for (int j = 0; j < n; j++) {
      if (cost[j] != 0) {
        z += cost[j] * value(j);
      }
    }
    return z;
  }

  @Override
  public double value(int j) {
    return row[j] >= 0 ? beta[row[j]] : upper[j] ? hi[j] : lo[j];
  }

  @Override
  public int basicRow(int j) {
    return row[j];
  }

  @Override
  public void addRows(double[][] rows, double[] rowLo, double[] rowHi) {
    addRows(sparseColumns(rows), sparseWeights(rows), rowLo, rowHi);
  }

  @Override
  public void addRows(int[][] columns, double[][] weights, double[] rowLo, double[] rowHi) {
    if (columns.length > 0) {
      appendRows(columns, weights, rowLo, rowHi);
    }
  }

  /**
   * Removes rows whose slacks are basic. Their slacks leave with them, the basis of the other rows
   * stays, and so does dual feasibility; a row whose slack is nonbasic is kept.
   *
   * @param rows the rows to remove
   * @return the old row of each new row, or null when no row was removed
   */
  int[] removeRows(int[] rows) {
    boolean[] gone = new boolean[m];
    int removed = 0;
    for (int i : rows) {
      if (i >= 0 && i < m && !gone[i] && row[n + i] >= 0) {
        gone[i] = true;
        removed++;
      }
    }
    if (removed == 0) {
      return null;
    }
    int m2 = m - removed;
    int cols2 = cols - removed;
    int[] newRow = new int[m]; // old row to new row, or -1
    int[] oldRow = new int[m2];
    int k = 0;
    for (int i = 0; i < m; i++) {
      if (gone[i]) {
        newRow[i] = -1;
      } else {
        newRow[i] = k;
        oldRow[k++] = i;
      }
    }
    // the positions of the basis: the positions of the removed slacks go, the others keep order
    int[] newPos = new int[m];
    int[] basis2 = new int[m2];
    double[] beta2 = new double[m2];
    double[] weight2 = new double[m2];
    k = 0;
    for (int r = 0; r < m; r++) {
      int j = basis[r];
      if (j >= n && gone[j - n]) {
        newPos[r] = -1;
        continue;
      }
      newPos[r] = k;
      basis2[k] = j < n ? j : n + newRow[j - n];
      beta2[k] = beta[r];
      weight2[k++] = weight[r];
    }
    double[] cost2 = new double[cols2];
    double[] lo2 = new double[cols2];
    double[] hi2 = new double[cols2];
    boolean[] upper2 = new boolean[cols2];
    double[] d2 = new double[cols2];
    double[] at2 = new double[cols2];
    int[] row2 = new int[cols2];
    for (int j = 0; j < cols; j++) {
      int j2;
      if (j < n) {
        j2 = j;
      } else if (gone[j - n]) {
        continue;
      } else {
        j2 = n + newRow[j - n];
      }
      cost2[j2] = cost[j];
      lo2[j2] = lo[j];
      hi2[j2] = hi[j];
      upper2[j2] = upper[j];
      d2[j2] = d[j];
      at2[j2] = at[j];
      row2[j2] = row[j] >= 0 ? newPos[row[j]] : -1;
    }
    int[][] rowIdx2 = new int[m2][];
    double[][] rowVal2 = new double[m2][];
    for (int i = 0; i < m2; i++) {
      rowIdx2[i] = rowIdx[oldRow[i]];
      rowVal2[i] = rowVal[oldRow[i]];
    }
    rowIdx = rowIdx2;
    rowVal = rowVal2;
    nonzeros = 0;
    Arrays.fill(colLen, 0);
    for (int i = 0; i < m2; i++) {
      nonzeros += rowIdx[i].length;
      for (int e = 0; e < rowIdx[i].length; e++) {
        int j = rowIdx[i][e];
        if (colLen[j] == colIdx[j].length) {
          colIdx[j] = Arrays.copyOf(colIdx[j], colLen[j] * 2 + 1);
          colVal[j] = Arrays.copyOf(colVal[j], colLen[j] * 2 + 1);
        }
        colIdx[j][colLen[j]] = i;
        colVal[j][colLen[j]++] = rowVal[i][e];
      }
    }
    // weights not known yet are all computed again
    weightsFrom = weightsFrom < m ? 0 : m2;
    basis = basis2;
    beta = beta2;
    weight = weight2;
    cost = cost2;
    lo = lo2;
    hi = hi2;
    upper = upper2;
    d = d2;
    at = at2;
    row = row2;
    m = m2;
    cols = cols2;
    factorValid = false;
    infeasibleRow = -1;
    allocateWork();
    return oldRow;
  }

  // the column j of [A -I], dense by row, into x
  private void column(int j, double[] x) {
    Arrays.fill(x, 0);
    addColumn(j, 1, x);
  }

  // x += f times the column j of [A -I]
  private void addColumn(int j, double f, double[] x) {
    if (f == 0) {
      return;
    }
    if (j < n) {
      int[] ci = colIdx[j];
      double[] cv = colVal[j];
      for (int e = 0; e < colLen[j]; e++) {
        x[ci[e]] += f * cv[e];
      }
    } else {
      x[j - n] -= f;
    }
  }

  // the row r of B^-1 into y
  private void unitRowOfInverse(int r, double[] y) {
    double[] z = work;
    Arrays.fill(z, 0);
    z[r] = 1;
    lu.btran(z, y);
  }

  // the row of the tableau rho [A -I] over the nonbasic columns, into alphaRow and touched
  private void pivotRow() {
    touchedCount = 0;
    ops += m;
    for (int i = 0; i < m; i++) {
      double ri = rho[i];
      if (ri == 0) {
        continue;
      }
      int[] idx = rowIdx[i];
      ops += idx.length;
      double[] val = rowVal[i];
      for (int e = 0; e < idx.length; e++) {
        int j = idx[e];
        if (row[j] < 0) {
          if (!isTouched[j]) {
            isTouched[j] = true;
            touched[touchedCount++] = j;
          }
          alphaRow[j] += ri * val[e];
        }
      }
      int s = n + i;
      if (row[s] < 0) {
        isTouched[s] = true;
        touched[touchedCount++] = s;
        alphaRow[s] = -ri;
      }
    }
  }

  private void clearTouched() {
    for (int t = 0; t < touchedCount; t++) {
      int j = touched[t];
      isTouched[j] = false;
      alphaRow[j] = 0;
    }
    touchedCount = 0;
  }

  /**
   * The dual ratio test with bound flipping over the touched columns ({@link RatioTest}).
   *
   * @return the entering column, or -1 when the row proves infeasibility
   */
  private int enteringColumn(boolean toLower, double gap) {
    ops += 2L * touchedCount;
    ratioTest.start();
    for (int t = 0; t < touchedCount; t++) {
      int j = touched[t];
      ratioTest.offer(j, alphaRow[j], upper[j], d[j], lo[j], hi[j], toLower);
    }
    return ratioTest.choose(gap, lo, hi);
  }

  // the basic row farthest outside its bounds, by dual steepest edge, or -1
  private int leavingRow() {
    int r = -1;
    double worst = 0;
    for (int i = 0; i < m; i++) {
      int p = basis[i];
      double v = beta[i];
      double gap = RatioTest.gap(v, lo[p], hi[p]);
      if (gap > 0) {
        double score = gap * gap / weight[i];
        if (score > worst) {
          worst = score;
          r = i;
        }
      }
    }
    return r;
  }

  // puts each nonbasic column at the bound its reduced cost asks for, a finite one
  private void placeNonbasic() {
    ops += cols;
    RatioTest.placeNonbasic(row, d, upper, lo, hi, cols);
  }

  // moves the basic values with the nonbasic columns whose values changed since the last call
  private void updateBeta() {
    if (!betaValid) {
      computeBeta();
      return;
    }
    ops += cols + m;
    Arrays.fill(work, 0);
    boolean any = false;
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        double v = upper[j] ? hi[j] : lo[j];
        double delta = v - at[j];
        if (delta != 0) {
          addColumn(j, delta, work);
          at[j] = v;
          any = true;
        }
      }
    }
    if (any) {
      lu.ftran(work, tau);
      for (int i = 0; i < m; i++) {
        beta[i] -= tau[i];
      }
    }
  }

  // x_B = -B^-1 N x_N
  private void computeBeta() {
    betaValid = true;
    ops += cols + m + nonzeros;
    Arrays.fill(work, 0);
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        double v = upper[j] ? hi[j] : lo[j];
        at[j] = v;
        addColumn(j, v, work);
      }
    }
    lu.ftran(work, beta);
    for (int i = 0; i < m; i++) {
      beta[i] = -beta[i];
    }
  }

  // d_j = c_j - y a_j with y = c_B B^-1
  private void computeDuals() {
    ops += nonzeros + cols;
    double[] y = duals();
    for (int j = 0; j < n; j++) {
      if (row[j] >= 0) {
        d[j] = 0;
        continue;
      }
      double s = cost[j];
      int[] ci = colIdx[j];
      double[] cv = colVal[j];
      for (int e = 0; e < colLen[j]; e++) {
        s -= y[ci[e]] * cv[e];
      }
      d[j] = s;
    }
    for (int i = 0; i < m; i++) {
      d[n + i] = row[n + i] >= 0 ? 0 : cost[n + i] + y[i];
    }
  }

  /**
   * Factorizes the basis again. Basic columns found dependent are replaced by slacks of rows; the
   * reduced costs and basic values are computed again from the factorization, and the steepest-edge
   * weights not known yet are computed exactly.
   */
  private void factorize() {
    int[][] ci = new int[m][];
    double[][] cv = new double[m][];
    int[] cl = new int[m];
    for (int k = 0; k < m; k++) {
      int j = basis[k];
      if (j < n) {
        ci[k] = colIdx[j];
        cv[k] = colVal[j];
        cl[k] = colLen[j];
      } else {
        ci[k] = new int[] {j - n};
        cv[k] = new double[] {-1};
        cl[k] = 1;
      }
    }
    if (lu != null) {
      ops += lu.ops;
    }
    lu = new SparseLu(m, ci, cv, cl);
    factorizations++;
    factorValid = true;
    boolean replaced = lu.replacedPos.length > 0;
    for (int s = 0; s < lu.replacedPos.length; s++) {
      int k = lu.replacedPos[s];
      int p = basis[k];
      int sl = n + lu.replacedRow[s];
      row[p] = -1;
      basis[k] = sl;
      row[sl] = k;
      weight[k] = 1;
    }
    computeDuals();
    betaValid = false;
    if (replaced) {
      // the replaced columns are nonbasic now, at the bounds their reduced costs ask for
      weightsFrom = 0;
    }
    if (weightsFrom < m) {
      double[] y = new double[m];
      for (int r = weightsFrom; r < m; r++) {
        unitRowOfInverse(r, y);
        double s = 0;
        for (int i = 0; i < m; i++) {
          s += y[i] * y[i];
        }
        weight[r] = Math.max(s, 1e-12);
      }
      weightsFrom = m;
    }
  }
}
