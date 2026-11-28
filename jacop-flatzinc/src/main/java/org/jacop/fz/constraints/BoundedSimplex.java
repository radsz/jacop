/*
 * BoundedSimplex.java
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

package org.jacop.fz.constraints;

/**
 * The primal simplex method with bounded variables 0 &lt;= x_j &lt;= upperBound[j] on a tableau
 * that starts in a feasible basis with every nonbasic variable at 0. It works in place on the
 * arrays given to the constructor.
 */
final class BoundedSimplex {

  static final double EPS = 1e-9;

  /** The outcomes of {@link #run(long, boolean)}. */
  enum Outcome {
    OPTIMAL,
    UNBOUNDED,
    LIMIT
  }

  private final double[][] t;
  private final double[] beta;
  private final int[] basis;
  private final double[] d;
  private final double[] upperBound;
  private final boolean[] upper;
  private final boolean[] basic;

  /**
   * It creates the method over a tableau.
   *
   * @param t the rows of the tableau, m by cols, the column basis[i] a unit column for row i.
   * @param beta the values of the basic variables.
   * @param basis the basic variable of each row.
   * @param d the reduced costs.
   * @param upperBound the upper bound of each variable, possibly infinite.
   */
  BoundedSimplex(double[][] t, double[] beta, int[] basis, double[] d, double[] upperBound) {
    this.t = t;
    this.beta = beta;
    this.basis = basis;
    this.d = d;
    this.upperBound = upperBound;
    this.upper = new boolean[d.length];
    this.basic = new boolean[d.length];
    for (int b : basis) {
      basic[b] = true;
    }
  }

  /**
   * It pivots until no nonbasic variable improves the objective.
   *
   * @param limit the largest number of iterations.
   * @param minimize true to decrease the objective, false to increase it.
   * @return whether the optimum was reached, the objective is unbounded, or the limit was hit.
   */
  Outcome run(long limit, boolean minimize) {
    int m = t.length;
    int cols = d.length;
    for (long iter = 0; iter < limit; iter++) {
      // entering: the largest improvement per unit, Bland's rule after a while against cycling
      boolean bland = iter > 10L * cols;
      int q = -1;
      double best = EPS;
      for (int j = 0; j < cols; j++) {
        if (basic[j] || upperBound[j] == 0) {
          continue;
        }
        double gain = upper[j] != minimize ? -d[j] : d[j];
        if (gain > best) {
          q = j;
          best = gain;
          if (bland) {
            break;
          }
        }
      }
      if (q < 0) {
        return Outcome.OPTIMAL;
      }
      double dir = upper[q] ? -1 : 1;
      double step = upperBound[q];
      int r = -1;
      for (int i = 0; i < m; i++) {
        double alpha = dir * t[i][q];
        double ratio;
        if (alpha > EPS) {
          ratio = beta[i] / alpha;
        } else if (alpha < -EPS && upperBound[basis[i]] < Double.POSITIVE_INFINITY) {
          ratio = (upperBound[basis[i]] - beta[i]) / -alpha;
        } else {
          continue;
        }
        if (ratio < step - EPS || (r >= 0 && ratio <= step + EPS && basis[i] < basis[r])) {
          step = ratio;
          r = i;
        }
      }
      if (Double.isInfinite(step)) {
        return Outcome.UNBOUNDED;
      }
      step = Math.max(step, 0);
      for (int i = 0; i < m; i++) {
        beta[i] -= dir * step * t[i][q];
      }
      if (r < 0) {
        // the entering variable reaches its other bound
        upper[q] = !upper[q];
        continue;
      }
      pivot(r, q, dir, step);
    }
    return Outcome.LIMIT;
  }

  private void pivot(int r, int q, double dir, double step) {
    int leaving = basis[r];
    upper[leaving] = dir * t[r][q] < 0;
    beta[r] = (upper[q] ? upperBound[q] : 0) + dir * step;
    basic[leaving] = false;
    basic[q] = true;
    upper[q] = false;
    basis[r] = q;
    double pivot = t[r][q];
    double[] row = t[r];
    for (int j = 0; j < row.length; j++) {
      row[j] /= pivot;
    }
    for (int i = 0; i < t.length; i++) {
      double f = t[i][q];
      if (i != r && f != 0) {
        double[] ti = t[i];
        for (int j = 0; j < row.length; j++) {
          ti[j] -= f * row[j];
        }
      }
    }
    double f = d[q];
    for (int j = 0; j < row.length; j++) {
      d[j] -= f * row[j];
    }
  }
}
