/*
 * DualSimplex.java
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
 * A dense bounded-variable dual simplex for {@code min c x} subject to {@code L <= A x <= U} and
 * {@code lo <= x <= hi}, warm-started from its last basis when the bounds of x change. Each row i
 * has a slack {@code s_i = a_i x} with bounds {@code [L_i, U_i]}, so the system is {@code [A -I]
 * (x, s) = 0} and the tableau keeps {@code B^-1 [A -I]}. The basis stays dual feasible when only
 * bounds change, so a re-solve after a few bound changes takes a few dual pivots.
 *
 * <p>It works in floating point. Its multipliers are only a guide: the caller turns them into an
 * integer combination of the rows and checks that combination exactly.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class DualSimplex implements LpSolver {

  private static final double PERTURBATION = 1e-7;

  // refactorizations after this many pivots, against the drift of the tableau
  private static final int REFACTOR_PIVOTS = 400;

  int m;
  final int n;
  private int cols;
  private double[][] a;
  private double[] cost;
  private double[] lo;
  private double[] hi;

  private double[][] t;
  private int[] basis;
  private int[] row; // the row of a basic column, -1 for a nonbasic one
  private boolean[] upper; // a nonbasic column at its upper bound
  private double[] d;
  private double[] beta;
  private int pivots;
  private int infeasibleRow = -1;

  // the values of the nonbasic columns that beta was computed with
  private double[] at;
  private boolean betaValid;

  // the nonbasic columns that move beta, and by how much
  private int[] moved;
  private double[] movedBy;

  // the squared norm of the row of B^-1 in each row of the tableau, valid while the row is
  // unchanged
  private double[] norm;
  private boolean[] normValid;

  // the ratio test, with the columns it flips to their other bound
  private RatioTest ratioTest;

  /** Statistics: pivots made. */
  long totalPivots;

  /**
   * Creates the problem with the slack basis.
   *
   * @param a the rows, dense, m by n
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective over the n columns, minimized
   */
  DualSimplex(double[][] a, double[] rowLo, double[] rowHi, double[] cost) {
    this.m = a.length;
    this.n = cost.length;
    this.cols = n + m;
    this.a = a;
    this.cost = new double[cols];
    // a small perturbation of the costs against dual degeneracy, which makes the dual simplex
    // cycle, above all without an objective
    Random rnd = new Random(n * 31L + m);
    for (int j = 0; j < n; j++) {
      this.cost[j] = cost[j] + PERTURBATION * (1 + rnd.nextDouble()) * (1 + Math.abs(cost[j]));
    }
    lo = new double[cols];
    hi = new double[cols];
    for (int i = 0; i < m; i++) {
      lo[n + i] = rowLo[i];
      hi[n + i] = rowHi[i];
    }
    t = new double[m][cols];
    basis = new int[m];
    row = new int[cols];
    upper = new boolean[cols];
    d = new double[cols];
    beta = new double[m];
    at = new double[cols];
    moved = new int[cols];
    movedBy = new double[cols];
    norm = new double[m];
    normValid = new boolean[m];
    ratioTest = new RatioTest(cols);
    slackBasis();
  }

  // a deep copy of the state of another simplex
  private DualSimplex(DualSimplex o) {
    m = o.m;
    n = o.n;
    cols = o.cols;
    a = o.a.clone(); // the rows themselves are never changed
    cost = o.cost.clone();
    lo = o.lo.clone();
    hi = o.hi.clone();
    t = new double[m][];
    for (int i = 0; i < m; i++) {
      t[i] = o.t[i].clone();
    }
    basis = o.basis.clone();
    row = o.row.clone();
    upper = o.upper.clone();
    d = o.d.clone();
    beta = o.beta.clone();
    at = o.at.clone();
    betaValid = o.betaValid;
    moved = new int[cols];
    movedBy = new double[cols];
    norm = o.norm.clone();
    normValid = o.normValid.clone();
    ratioTest = new RatioTest(o.ratioTest);
    pivots = o.pivots;
    infeasibleRow = o.infeasibleRow;
    totalPivots = o.totalPivots;
  }

  /**
   * Returns a copy of this simplex with its basis, which goes on independently.
   *
   * @return the copy
   */
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

  @Override
  public long pivotWork() {
    return (long) m * cols;
  }

  @Override
  public DualSimplex copy() {
    return new DualSimplex(this);
  }

  /**
   * Sets the bounds of a column.
   *
   * @param j the column
   * @param min its lower bound
   * @param max its upper bound
   */
  @Override
  public void setBounds(int j, double min, double max) {
    lo[j] = min;
    hi[j] = max;
  }

  /**
   * Re-solves from the current basis with the current bounds.
   *
   * @param limit the most pivots
   * @return {@link #OPTIMAL}, {@link #INFEASIBLE} or {@link #LIMIT}
   */
  @Override
  public int solve(int limit) {
    infeasibleRow = -1;
    placeNonbasic();
    updateBeta();
    for (int iter = 0; iter < limit; iter++) {
      int r = leavingRow();
      if (r < 0) {
        return OPTIMAL;
      }
      int p = basis[r];
      boolean toLower = beta[r] < lo[p];
      int q = enteringColumn(r, toLower, toLower ? lo[p] - beta[r] : beta[r] - hi[p]);
      if (q < 0) {
        infeasibleRow = r;
        return INFEASIBLE;
      }
      for (int k = 0; k < ratioTest.flips(); k++) {
        upper[ratioTest.flipped(k)] = !upper[ratioTest.flipped(k)];
      }
      pivot(r, q, toLower);
      if (pivots >= REFACTOR_PIVOTS) {
        refactor();
      }
      computeBeta();
    }
    return LIMIT;
  }

  /**
   * Adds rows, each with a basic slack, keeping the current basis: the basis stays dual feasible,
   * so a re-solve goes on from it with a few dual pivots for the rows the current solution breaks.
   *
   * @param rows the new rows, dense over the n columns
   * @param rowLo their lower bounds, or negative infinity
   * @param rowHi their upper bounds, or positive infinity
   */
  @Override
  public void addRows(double[][] rows, double[] rowLo, double[] rowHi) {
    int k = rows.length;
    if (k == 0) {
      return;
    }
    int m2 = m + k;
    int cols2 = cols + k;
    a = Arrays.copyOf(a, m2);
    cost = Arrays.copyOf(cost, cols2);
    lo = Arrays.copyOf(lo, cols2);
    hi = Arrays.copyOf(hi, cols2);
    t = Arrays.copyOf(t, m2);
    for (int i = 0; i < m; i++) {
      t[i] = Arrays.copyOf(t[i], cols2);
    }
    for (int q = 0; q < k; q++) {
      a[m + q] = rows[q];
      lo[cols + q] = rowLo[q];
      hi[cols + q] = rowHi[q];
      // s - a x = 0, with the basic columns eliminated by their rows of the tableau
      double[] v = new double[cols2];
      for (int j = 0; j < n; j++) {
        v[j] = -rows[q][j];
      }
      v[cols + q] = 1;
      for (int j = 0; j < n; j++) {
        double f = v[j];
        if (Math.abs(f) > 0 && row[j] >= 0) {
          double[] tr = t[row[j]];
          for (int c = 0; c < cols; c++) {
            v[c] -= f * tr[c];
          }
          v[j] = 0;
        }
      }
      t[m + q] = v;
    }
    basis = Arrays.copyOf(basis, m2);
    row = Arrays.copyOf(row, cols2);
    for (int q = 0; q < k; q++) {
      basis[m + q] = cols + q;
      row[cols + q] = m + q;
    }
    upper = Arrays.copyOf(upper, cols2);
    d = Arrays.copyOf(d, cols2);
    beta = Arrays.copyOf(beta, m2);
    norm = Arrays.copyOf(norm, m2);
    normValid = Arrays.copyOf(normValid, m2);
    at = new double[cols2];
    moved = new int[cols2];
    movedBy = new double[cols2];
    ratioTest.resize(cols2);
    betaValid = false;
    m = m2;
    cols = cols2;
  }

  /**
   * Returns the row of the tableau in which a column is basic.
   *
   * @param j the column
   * @return its row, or -1 when the column is nonbasic
   */
  @Override
  public int basicRow(int j) {
    return row[j];
  }

  /**
   * Returns a row of the basis inverse: the multipliers of the rows whose combination is the row of
   * the tableau, {@code x_B(r) + sum_N t_rj x_j}.
   *
   * @param r the row of the tableau
   * @return y, by row
   */
  @Override
  public double[] inverseRow(int r) {
    double[] y = new double[m];
    double[] tr = t[r];
    for (int i = 0; i < m; i++) {
      y[i] = -tr[n + i];
    }
    return y;
  }

  /**
   * Returns the multipliers of the rows that prove infeasibility: the row of the basis inverse of
   * the infeasible row, so that {@code y [A -I] (x, s) = 0} has no solution within the bounds.
   *
   * @return y, by row
   */
  @Override
  public double[] farkas() {
    return inverseRow(infeasibleRow);
  }

  /**
   * Returns the dual values of the rows at an optimal basis, {@code c_B B^-1}.
   *
   * @return y, by row
   */
  @Override
  public double[] duals() {
    // the reduced cost of the slack of row i is 0 - c_B B^-1 (-e_i), the dual value of the row
    return Arrays.copyOfRange(d, n, cols);
  }

  /**
   * Returns the objective value of the current basic solution.
   *
   * @return c x
   */
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

  /**
   * Returns the value of a column in the current basic solution.
   *
   * @param j the column
   * @return its value
   */
  @Override
  public double value(int j) {
    return row[j] >= 0 ? beta[row[j]] : upper[j] ? hi[j] : lo[j];
  }

  private void slackBasis() {
    for (int i = 0; i < m; i++) {
      double[] ti = t[i];
      Arrays.fill(ti, 0);
      for (int j = 0; j < n; j++) {
        ti[j] = -a[i][j];
      }
      ti[n + i] = 1;
      basis[i] = n + i;
    }
    Arrays.fill(row, -1);
    for (int i = 0; i < m; i++) {
      row[n + i] = i;
    }
    System.arraycopy(cost, 0, d, 0, cols);
    pivots = 0;
    betaValid = false;
    Arrays.fill(normValid, false);
  }

  // puts each nonbasic column at the bound its reduced cost asks for, a finite one
  private void placeNonbasic() {
    RatioTest.placeNonbasic(row, d, upper, lo, hi, cols);
  }

  // moves the basic values with the nonbasic columns whose values changed since the last call
  private void updateBeta() {
    if (!betaValid) {
      computeBeta();
      return;
    }
    int k = 0;
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        double v = upper[j] ? hi[j] : lo[j];
        double delta = v - at[j];
        if (delta != 0) {
          moved[k] = j;
          movedBy[k++] = delta;
          at[j] = v;
        }
      }
    }
    if (k > 0) {
      subtractColumns(k);
    }
  }

  private void computeBeta() {
    betaValid = true;
    int k = 0;
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        double v = upper[j] ? hi[j] : lo[j];
        at[j] = v;
        if (v != 0) {
          moved[k] = j;
          movedBy[k++] = v;
        }
      }
    }
    Arrays.fill(beta, 0);
    if (k > 0) {
      subtractColumns(k);
    }
  }

  // beta[i] -= sum over the first k moved columns of t[i][j] times its move, row by row (the
  // tableau is row-major) and over the columns in increasing order, so the sums stay the same
  private void subtractColumns(int k) {
    // four rows at a time: their sums are independent, so the processor overlaps them
    int i = 0;
    for (; i + 3 < m; i += 4) {
      double[] t0 = t[i];
      double[] t1 = t[i + 1];
      double[] t2 = t[i + 2];
      double[] t3 = t[i + 3];
      double b0 = beta[i];
      double b1 = beta[i + 1];
      double b2 = beta[i + 2];
      double b3 = beta[i + 3];
      for (int c = 0; c < k; c++) {
        int j = moved[c];
        double by = movedBy[c];
        double v0 = t0[j];
        double v1 = t1[j];
        double v2 = t2[j];
        double v3 = t3[j];
        if (v0 != 0) {
          b0 -= v0 * by;
        }
        if (v1 != 0) {
          b1 -= v1 * by;
        }
        if (v2 != 0) {
          b2 -= v2 * by;
        }
        if (v3 != 0) {
          b3 -= v3 * by;
        }
      }
      beta[i] = b0;
      beta[i + 1] = b1;
      beta[i + 2] = b2;
      beta[i + 3] = b3;
    }
    for (; i < m; i++) {
      double[] ti = t[i];
      double b = beta[i];
      for (int c = 0; c < k; c++) {
        double tij = ti[moved[c]];
        if (tij != 0) {
          b -= tij * movedBy[c];
        }
      }
      beta[i] = b;
    }
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
        // dual steepest edge: the infeasibility relative to the norm of the row of B^-1
        if (!normValid[i]) {
          double[] ti = t[i];
          double s = 0;
          for (int k = n; k < cols; k++) {
            s += ti[k] * ti[k];
          }
          norm[i] = s;
          normValid[i] = true;
        }
        double score = gap * gap / Math.max(norm[i], 1e-12);
        if (score > worst) {
          worst = score;
          r = i;
        }
      }
    }
    return r;
  }

  /**
   * The dual ratio test with bound flipping over the nonbasic columns ({@link RatioTest}).
   *
   * @return the entering column, or -1 when the row proves infeasibility
   */
  private int enteringColumn(int r, boolean toLower, double gap) {
    double[] tr = t[r];
    ratioTest.start();
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        ratioTest.offer(j, tr[j], upper[j], d[j], lo[j], hi[j], toLower);
      }
    }
    return ratioTest.choose(gap, lo, hi);
  }

  private void pivot(int r, int q, boolean toLower) {
    int p = basis[r];
    double[] tr = t[r];
    double inv = 1 / tr[q];
    for (int j = 0; j < cols; j++) {
      tr[j] *= inv;
    }
    tr[q] = 1;
    normValid[r] = false;
    for (int i = 0; i < m; i++) {
      if (i != r) {
        double[] ti = t[i];
        double f = ti[q];
        if (f != 0) {
          for (int j = 0; j < cols; j++) {
            ti[j] -= f * tr[j];
          }
          ti[q] = 0;
          normValid[i] = false;
        }
      }
    }
    double f = d[q];
    if (f != 0) {
      for (int j = 0; j < cols; j++) {
        d[j] -= f * tr[j];
      }
    }
    d[q] = 0;
    basis[r] = q;
    row[q] = r;
    row[p] = -1;
    upper[p] = !toLower;
    pivots++;
    totalPivots++;
  }

  /**
   * Rebuilds the tableau of the current basis from the rows by Gauss-Jordan elimination, or goes
   * back to the slack basis when the basis is singular in floating point.
   */
  private void refactor() {
    Arrays.fill(normValid, false);
    int[] columns = basis.clone();
    for (int i = 0; i < m; i++) {
      double[] ti = t[i];
      Arrays.fill(ti, 0);
      for (int j = 0; j < n; j++) {
        ti[j] = a[i][j];
      }
      ti[n + i] = -1;
    }
    boolean[] used = new boolean[m];
    int[] newRow = new int[m];
    for (int k = 0; k < m; k++) {
      int c = columns[k];
      int pr = -1;
      double best = 1e-9;
      for (int i = 0; i < m; i++) {
        if (!used[i] && Math.abs(t[i][c]) > best) {
          best = Math.abs(t[i][c]);
          pr = i;
        }
      }
      if (pr < 0) {
        slackBasis();
        return;
      }
      used[pr] = true;
      newRow[k] = pr;
      double[] tp = t[pr];
      double inv = 1 / tp[c];
      for (int j = 0; j < cols; j++) {
        tp[j] *= inv;
      }
      tp[c] = 1;
      for (int i = 0; i < m; i++) {
        if (i != pr) {
          double[] ti = t[i];
          double f = ti[c];
          if (f != 0) {
            for (int j = 0; j < cols; j++) {
              ti[j] -= f * tp[j];
            }
            ti[c] = 0;
          }
        }
      }
    }
    Arrays.fill(row, -1);
    for (int k = 0; k < m; k++) {
      basis[newRow[k]] = columns[k];
      row[columns[k]] = newRow[k];
    }
    System.arraycopy(cost, 0, d, 0, cols);
    for (int i = 0; i < m; i++) {
      double c = cost[basis[i]];
      if (c != 0) {
        double[] ti = t[i];
        for (int j = 0; j < cols; j++) {
          d[j] -= c * ti[j];
        }
      }
    }
    pivots = 0;
  }
}
