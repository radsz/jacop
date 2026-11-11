/*
 * CoreLp.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in material form or reasonable ways of identifying the work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.jalp.RevisedDualSimplex;

/**
 * A linear program built column by column and row by row, solved once for a lower bound of one of
 * its columns. The bound is safe against the rounding of the simplex: it is computed from the duals
 * the simplex returns, whatever they are, as in Neumaier and Shcherbina, "Safe bounds in linear and
 * mixed-integer linear programming", Mathematical Programming 99 (2004) 283-296. Any vector y gives
 * {@code c x = y A x + (c - y A) x >= sum_i y_i (lo_i or hi_i) + sum_j min over [l_j, u_j] of (c -
 * y A)_j x_j}, so a wrong dual vector only weakens the bound.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CoreLp {

  private static final double INF = Double.POSITIVE_INFINITY;

  private final Map<Object, Integer> index = new HashMap<>();
  private final List<double[]> bounds = new ArrayList<>();
  private final List<int[]> rowColumns = new ArrayList<>();
  private final List<double[]> rowValues = new ArrayList<>();
  private final List<double[]> rowSides = new ArrayList<>();

  /** The pivots of the last solve. */
  long pivots;

  /** The status of the last solve. */
  int status = -1;

  /**
   * Returns the column of a key, made with the given bounds or narrowed to them.
   *
   * @param key the key, compared with equals
   * @param lo the lower bound
   * @param hi the upper bound
   * @return the column
   */
  int column(Object key, double lo, double hi) {
    Integer j = index.get(key);
    if (j == null) {
      j = bounds.size();
      index.put(key, j);
      bounds.add(new double[] {lo, hi});
    } else {
      double[] b = bounds.get(j);
      b[0] = Math.max(b[0], lo);
      b[1] = Math.min(b[1], hi);
    }
    return j;
  }

  int columns() {
    return bounds.size();
  }

  int rows() {
    return rowColumns.size();
  }

  /**
   * Adds the row {@code lo <= sum w_k x_{c_k} <= hi}, with the coefficients of a repeated column
   * added together.
   */
  void row(int[] columns, double[] weights, double lo, double hi) {
    Map<Integer, Double> sum = new HashMap<>();
    for (int k = 0; k < columns.length; k++) {
      sum.merge(columns[k], weights[k], Double::sum);
    }
    sum.values().removeIf(w -> w == 0);
    if (sum.isEmpty()) {
      return;
    }
    int[] cs = new int[sum.size()];
    double[] ws = new double[sum.size()];
    int k = 0;
    for (Map.Entry<Integer, Double> e : sum.entrySet()) {
      cs[k] = e.getKey();
      ws[k++] = e.getValue();
    }
    rowColumns.add(cs);
    rowValues.add(ws);
    rowSides.add(new double[] {lo, hi});
  }

  /**
   * Minimizes a column and returns a safe lower bound of it, or negative infinity when the solve
   * does not end optimal or no finite bound follows from its duals.
   *
   * @param objective the column minimized
   * @param pivotLimit the most pivots
   * @return the bound
   */
  double minimize(int objective, int pivotLimit) {
    int m = rowColumns.size();
    int n = bounds.size();
    double[] lo = new double[m];
    double[] hi = new double[m];
    for (int i = 0; i < m; i++) {
      lo[i] = rowSides.get(i)[0];
      hi[i] = rowSides.get(i)[1];
    }
    double[] cost = new double[n];
    cost[objective] = 1;
    RevisedDualSimplex lp =
        new RevisedDualSimplex(
            rowColumns.toArray(new int[0][]),
            rowValues.toArray(new double[0][]),
            lo,
            hi,
            cost,
            true);
    for (int j = 0; j < n; j++) {
      double[] b = bounds.get(j);
      if (b[0] > b[1]) {
        status = RevisedDualSimplex.INFEASIBLE;
        return INF;
      }
      lp.setBounds(j, b[0], b[1]);
    }
    status = lp.solve(pivotLimit);
    pivots = lp.pivots();
    if (status != RevisedDualSimplex.OPTIMAL) {
      return Double.NEGATIVE_INFINITY;
    }
    return safeBound(lp.duals(), cost, lo, hi);
  }

  private double safeBound(double[] y, double[] cost, double[] lo, double[] hi) {
    int n = cost.length;
    double[] d = cost.clone();
    double[] size = new double[n]; // the sum of the magnitudes of the terms of each d_j
    double bound = 0;
    double error = 0;
    for (int i = 0; i < y.length; i++) {
      double yi = y[i];
      if (yi == 0) {
        continue;
      }
      double side = yi > 0 ? lo[i] : hi[i];
      if (Double.isInfinite(side)) {
        return Double.NEGATIVE_INFINITY;
      }
      bound += yi * side;
      error += Math.abs(yi * side);
      int[] cs = rowColumns.get(i);
      double[] ws = rowValues.get(i);
      for (int k = 0; k < cs.length; k++) {
        d[cs[k]] -= yi * ws[k];
        size[cs[k]] += Math.abs(yi * ws[k]);
      }
    }
    for (int j = 0; j < n; j++) {
      double[] b = bounds.get(j);
      // the rounding of d_j is far below 1e-12 of the magnitudes summed into it; widen it by that
      double slack = 1e-12 * (Math.abs(cost[j]) + size[j]);
      double low = d[j] - slack;
      double high = d[j] + slack;
      // min over x in [l, u] of dj x, for every dj in [low, high]
      double best = INF;
      for (double dj : new double[] {low, high}) {
        for (double x : new double[] {b[0], b[1]}) {
          double v;
          if (dj == 0) {
            v = 0;
          } else if (Double.isInfinite(x)) {
            v = (dj > 0) == (x > 0) ? INF : Double.NEGATIVE_INFINITY;
          } else {
            v = dj * x;
          }
          best = Math.min(best, v);
        }
      }
      if (best == Double.NEGATIVE_INFINITY) {
        return Double.NEGATIVE_INFINITY;
      }
      bound += best;
      error += Math.abs(best);
    }
    return bound - 1e-9 * (1 + error);
  }
}
