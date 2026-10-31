/*
 * RatioTest.java
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

/**
 * The dual ratio test with bound flipping and Harris tolerances, shared by {@link DualSimplex} and
 * {@link SparseDualSimplex}: the eligible columns are taken in the order of their dual ratios, and
 * a boxed column whose move to its other bound leaves the basic variable still outside its bound is
 * flipped instead of entering. Among ratios within the tolerance of the smallest, the largest pivot
 * is taken.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class RatioTest {

  static final double PRIMAL_TOL = 1e-6;
  static final double DUAL_TOL = 1e-9;
  static final double PIVOT_TOL = 1e-9;

  // the candidates, and the columns flipped to their other bound
  private int[] candidate;
  private double[] pivotSize;
  private double[] ratio;
  private int[] flipped;
  private int flips;
  private int count;

  RatioTest(int cols) {
    resize(cols);
  }

  RatioTest(RatioTest o) {
    resize(o.candidate.length);
    System.arraycopy(o.flipped, 0, flipped, 0, o.flips);
    flips = o.flips;
  }

  // room for cols columns; forgets the candidates and the flips
  void resize(int cols) {
    candidate = new int[cols];
    pivotSize = new double[cols];
    ratio = new double[cols];
    flipped = new int[cols];
    flips = 0;
    count = 0;
  }

  /** The choice when the ratios are not numbers (NaN reduced costs or entries). */
  static final int NUMERIC = -2;

  // starts a ratio test
  void start() {
    count = 0;
    flips = 0;
  }

  /**
   * Offers a nonbasic column to the ratio test.
   *
   * @param j the column
   * @param alpha its entry in the row of the tableau
   * @param atUpper whether it is at its upper bound
   * @param d its reduced cost
   * @param lo its lower bound
   * @param hi its upper bound
   * @param toLower whether the basic variable of the row is below its lower bound
   */
  void offer(
      int j, double alpha, boolean atUpper, double d, double lo, double hi, boolean toLower) {
    // moving x_j towards its other bound must bring the basic variable back towards the bound it
    // leaves at: with x_B = -sum alpha_j x_j, it rises when x_j rises with alpha_j < 0 or falls
    // with alpha_j > 0
    if (Math.abs(alpha) < PIVOT_TOL || lo == hi || (atUpper ? alpha > 0 : alpha < 0) != toLower) {
      return;
    }
    double size = Math.abs(alpha);
    candidate[count] = j;
    pivotSize[count] = size;
    ratio[count] = Math.max(0, atUpper ? -d : d) / size;
    count++;
  }

  /**
   * Chooses the entering column among the offered ones.
   *
   * @param gap how far the basic variable is outside its bound
   * @param lo the lower bounds of the columns
   * @param hi the upper bounds of the columns
   * @return the entering column, or -1 when even every eligible column at its other bound leaves
   *     the basic variable outside its bound, so the row proves infeasibility, or {@link #NUMERIC}
   *     when the ratios are not numbers
   */
  int choose(double gap, double[] lo, double[] hi) {
    int k = count;
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
      if (pick < 0) {
        // a ratio is NaN: the simplex has lost its numbers
        flips = 0;
        return NUMERIC;
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

  // the columns the last choice flips to their other bound
  int flips() {
    return flips;
  }

  int flipped(int k) {
    return flipped[k];
  }

  /**
   * Returns how far a basic value is outside its bounds, beyond the primal tolerance, or 0.
   *
   * @param v the value
   * @param lo its lower bound
   * @param hi its upper bound
   * @return the distance to the bound it breaks, or 0
   */
  static double gap(double v, double lo, double hi) {
    if (v < lo - PRIMAL_TOL * Math.max(1, Math.abs(lo))) {
      return lo - v;
    } else if (v > hi + PRIMAL_TOL * Math.max(1, Math.abs(hi))) {
      return v - hi;
    }
    return 0;
  }

  /**
   * Puts each nonbasic column at the bound its reduced cost asks for, a finite one.
   *
   * @param row the row of each basic column, -1 for a nonbasic one
   * @param d the reduced costs
   * @param upper whether each nonbasic column is at its upper bound
   * @param lo the lower bounds
   * @param hi the upper bounds
   * @param cols the columns
   */
  static void placeNonbasic(
      int[] row, double[] d, boolean[] upper, double[] lo, double[] hi, int cols) {
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
}
