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
final class DualSimplex {

  /** The solve result: an optimal basis. */
  static final int OPTIMAL = 0;

  /** The solve result: a row whose basic variable cannot reach its bounds. */
  static final int INFEASIBLE = 1;

  /** The solve result: the iteration limit was reached. */
  static final int LIMIT = 2;

  private static final double PRIMAL_TOL = 1e-6;
  private static final double DUAL_TOL = 1e-9;
  private static final double PIVOT_TOL = 1e-9;
  private static final double PERTURBATION = 1e-7;

  // refactorizations after this many pivots, against the drift of the tableau
  private static final int REFACTOR_PIVOTS = 400;

  final int m;
  final int n;
  private final int cols;
  private final double[][] a;
  private final double[] cost;
  private final double[] lo;
  private final double[] hi;

  private final double[][] t;
  private final int[] basis;
  private final int[] row; // the row of a basic column, -1 for a nonbasic one
  private final boolean[] upper; // a nonbasic column at its upper bound
  private final double[] d;
  private final double[] beta;
  private int pivots;
  private int infeasibleRow = -1;

  // the values of the nonbasic columns that beta was computed with
  private final double[] at;
  private boolean betaValid;

  // the nonbasic columns that move beta, and by how much
  private final int[] moved;
  private final double[] movedBy;

  // the squared norm of the row of B^-1 in each row of the tableau, valid while the row is
  // unchanged
  private final double[] norm;
  private final boolean[] normValid;

  // the ratio test: its candidates, and the columns it flips to their other bound
  private final int[] candidate;
  private final double[] pivotSize;
  private final double[] ratio;
  private final int[] flipped;
  private int flips;

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
    candidate = new int[cols];
    pivotSize = new double[cols];
    ratio = new double[cols];
    flipped = new int[cols];
    slackBasis();
  }

  /**
   * Sets the bounds of a column.
   *
   * @param j the column
   * @param min its lower bound
   * @param max its upper bound
   */
  void setBounds(int j, double min, double max) {
    lo[j] = min;
    hi[j] = max;
  }

  /**
   * Re-solves from the current basis with the current bounds.
   *
   * @param limit the most pivots
   * @return {@link #OPTIMAL}, {@link #INFEASIBLE} or {@link #LIMIT}
   */
  int solve(int limit) {
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
      for (int k = 0; k < flips; k++) {
        upper[flipped[k]] = !upper[flipped[k]];
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
   * Returns the multipliers of the rows that prove infeasibility: the row of the basis inverse of
   * the infeasible row, so that {@code y [A -I] (x, s) = 0} has no solution within the bounds.
   *
   * @return y, by row
   */
  double[] farkas() {
    double[] y = new double[m];
    double[] tr = t[infeasibleRow];
    for (int i = 0; i < m; i++) {
      y[i] = -tr[n + i];
    }
    return y;
  }

  /**
   * Returns the dual values of the rows at an optimal basis, {@code c_B B^-1}.
   *
   * @return y, by row
   */
  double[] duals() {
    double[] y = new double[m];
    for (int r = 0; r < m; r++) {
      double c = cost[basis[r]];
      if (c != 0) {
        double[] tr = t[r];
        for (int i = 0; i < m; i++) {
          y[i] -= c * tr[n + i];
        }
      }
    }
    return y;
  }

  /**
   * Returns the objective value of the current basic solution.
   *
   * @return c x
   */
  double objective() {
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
  double value(int j) {
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
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        if (d[j] > DUAL_TOL) {
          upper[j] = false;
        } else if (d[j] < -DUAL_TOL) {
          upper[j] = true;
        }
        if (upper[j] ? hi[j] == Double.POSITIVE_INFINITY : lo[j] == Double.NEGATIVE_INFINITY) {
          upper[j] = !upper[j];
        }
      }
    }
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
    for (int i = 0; i < m; i++) {
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
      double gap = 0;
      if (v < lo[p] - PRIMAL_TOL * Math.max(1, Math.abs(lo[p]))) {
        gap = lo[p] - v;
      } else if (v > hi[p] + PRIMAL_TOL * Math.max(1, Math.abs(hi[p]))) {
        gap = v - hi[p];
      }
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
   * The dual ratio test with bound flipping: the eligible columns are taken in the order of their
   * dual ratios, and a boxed column whose move to its other bound leaves the basic variable still
   * outside its bound is flipped ({@link #flipped}) instead of entering. Among ratios within the
   * tolerance of the smallest, the largest pivot is taken.
   *
   * @return the entering column, or -1 when even every eligible column at its other bound leaves
   *     the basic variable outside its bound, so the row proves infeasibility
   */
  private int enteringColumn(int r, boolean toLower, double gap) {
    double[] tr = t[r];
    int k = 0;
    for (int j = 0; j < cols; j++) {
      double alpha = eligible(tr[j], j, toLower);
      if (alpha > 0) {
        candidate[k] = j;
        pivotSize[k] = alpha;
        ratio[k] = Math.max(0, upper[j] ? -d[j] : d[j]) / alpha;
        k++;
      }
    }
    flips = 0;
    double slope = gap;
    while (k > 0) {
      // Harris: the largest pivot among the ratios that keep every reduced cost within tolerance
      double least = Double.POSITIVE_INFINITY;
      for (int i = 0; i < k; i++) {
        least = Math.min(least, ratio[i] + DUAL_TOL / pivotSize[i]);
      }
      int pick = -1;
      for (int i = 0; i < k; i++) {
        if (ratio[i] <= least && (pick < 0 || pivotSize[i] > pivotSize[pick])) {
          pick = i;
        }
      }
      int j = candidate[pick];
      double range = hi[j] - lo[j];
      slope -= pivotSize[pick] * range;
      if (slope <= PRIMAL_TOL * Math.max(1, gap) || Double.isInfinite(range)) {
        return j;
      }
      flipped[flips++] = j;
      k--;
      candidate[pick] = candidate[k];
      pivotSize[pick] = pivotSize[k];
      ratio[pick] = ratio[k];
    }
    flips = 0;
    return -1;
  }

  /**
   * Returns |alpha| when moving nonbasic column j towards its other bound brings the basic variable
   * of the row back towards the bound it leaves at, otherwise 0. With x_B = -sum alpha_j x_j, a
   * basic variable below its lower bound rises when x_j rises with alpha_j &lt; 0 or falls with
   * alpha_j &gt; 0.
   */
  private double eligible(double alpha, int j, boolean toLower) {
    if (row[j] >= 0 || Math.abs(alpha) < PIVOT_TOL || lo[j] == hi[j]) {
      return 0;
    }
    boolean rises = upper[j] ? alpha > 0 : alpha < 0;
    return rises == toLower ? Math.abs(alpha) : 0;
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
