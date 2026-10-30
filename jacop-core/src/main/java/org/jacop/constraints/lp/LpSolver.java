/*
 * LpSolver.java
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
 * A bounded-variable dual simplex for {@code min c x} subject to {@code L <= A x <= U} and {@code
 * lo <= x <= hi}, warm-started from its last basis when the bounds of x change. Row i has a slack
 * column {@code n + i} with the bounds of the row, so the system is {@code [A -I] (x, s) = 0}; the
 * basis has one basic column for each row of the tableau {@code B^-1 [A -I]}.
 *
 * <p>Its results are in floating point and only a guide: the caller turns the multipliers into an
 * integer combination of the rows and checks that combination exactly.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
interface LpSolver {

  /** The solve result: an optimal basis. */
  int OPTIMAL = 0;

  /** The solve result: a row whose basic variable cannot reach its bounds. */
  int INFEASIBLE = 1;

  /** The solve result: the iteration limit was reached. */
  int LIMIT = 2;

  /**
   * Returns the number of rows.
   *
   * @return the rows
   */
  int rows();

  /**
   * Returns the number of structural columns, the columns of A.
   *
   * @return n
   */
  int columns();

  /**
   * Returns the pivots made so far.
   *
   * @return the pivots
   */
  long pivots();

  /**
   * Returns an estimate of the work of one pivot, in the units of the tableau entries a dense pivot
   * updates, so that a caller can share one work budget between the implementations.
   *
   * @return the work of a pivot
   */
  long pivotWork();

  /**
   * Returns the work done so far, in the units of {@link #pivotWork}: for the sparse simplex the
   * entries its loops have touched, counted as they run, so the same solves always count the same.
   *
   * @return the work
   */
  default long work() {
    return pivots() * pivotWork();
  }

  /**
   * Sets the bounds of a column.
   *
   * @param j the column
   * @param min its lower bound
   * @param max its upper bound
   */
  void setBounds(int j, double min, double max);

  /**
   * Re-solves from the current basis with the current bounds.
   *
   * @param limit the most pivots
   * @return {@link #OPTIMAL}, {@link #INFEASIBLE} or {@link #LIMIT}
   */
  int solve(int limit);

  /**
   * Returns the multipliers of the rows that prove infeasibility after {@link #solve} returned
   * {@link #INFEASIBLE}: the row of the basis inverse of the infeasible row, so that {@code y [A
   * -I] (x, s) = 0} has no solution within the bounds.
   *
   * @return y, by row
   */
  double[] farkas();

  /**
   * Returns the dual values of the rows at an optimal basis, {@code c_B B^-1}.
   *
   * @return y, by row
   */
  double[] duals();

  /**
   * Returns the objective value of the current basic solution.
   *
   * @return c x
   */
  double objective();

  /**
   * Returns the value of a column in the current basic solution.
   *
   * @param j the column, a structural column or a slack {@code n + i}
   * @return its value
   */
  double value(int j);

  /**
   * Returns the row of the tableau in which a column is basic.
   *
   * @param j the column
   * @return its row, or -1 when the column is nonbasic
   */
  int basicRow(int j);

  /**
   * Returns a row of the basis inverse: the multipliers of the rows whose combination is the row of
   * the tableau, {@code x_B(r) + sum_N t_rj x_j}.
   *
   * @param r the row of the tableau
   * @return y, by row
   */
  double[] inverseRow(int r);

  /**
   * Adds rows, each with a basic slack, keeping the current basis: the basis stays dual feasible,
   * so a re-solve goes on from it with a few dual pivots for the rows the current solution breaks.
   *
   * @param rows the new rows, dense over the n columns
   * @param rowLo their lower bounds, or negative infinity
   * @param rowHi their upper bounds, or positive infinity
   */
  void addRows(double[][] rows, double[] rowLo, double[] rowHi);

  /**
   * Adds rows given sparse, each with a basic slack, as {@link #addRows(double[][], double[],
   * double[])} does.
   *
   * @param columns the columns of each new row
   * @param weights the weights of each new row, matching its columns
   * @param rowLo their lower bounds, or negative infinity
   * @param rowHi their upper bounds, or positive infinity
   */
  default void addRows(int[][] columns, double[][] weights, double[] rowLo, double[] rowHi) {
    int n = columns();
    double[][] dense = new double[columns.length][n];
    for (int q = 0; q < columns.length; q++) {
      for (int k = 0; k < columns[q].length; k++) {
        dense[q][columns[q][k]] += weights[q][k];
      }
    }
    addRows(dense, rowLo, rowHi);
  }

  /**
   * Returns a copy with its basis, which goes on independently.
   *
   * @return the copy
   */
  LpSolver copy();
}
