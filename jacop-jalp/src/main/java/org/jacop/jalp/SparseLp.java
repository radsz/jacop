/*
 * SparseLp.java
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

/**
 * A sparse LP engine as LinearRelaxation uses it: JaLP's {@link RevisedDualSimplex} or HiGHS
 * through {@link HighsLp}. The rows are y = A x with bounds on x and y; column n + i is the slack
 * of row i.
 */
public interface SparseLp {

  /**
   * Returns the number of rows.
   *
   * @return the rows
   */
  int rows();

  /**
   * Returns the number of structural columns.
   *
   * @return the columns
   */
  int columns();

  /**
   * Returns the pivots made so far.
   *
   * @return the pivots
   */
  long pivots();

  /**
   * Returns the cost of one pivot in work units.
   *
   * @return the work of a pivot
   */
  long pivotWork();

  /**
   * Returns the work done so far, in the units of {@link #pivotWork()}.
   *
   * @return the work
   */
  long work();

  /**
   * Sets the bounds of a column (structural or slack).
   *
   * @param j the column
   * @param min the lower bound
   * @param max the upper bound
   */
  void setBounds(int j, double min, double max);

  /**
   * Solves from the current basis.
   *
   * @param limit the most pivots
   * @return {@link RevisedDualSimplex#OPTIMAL}, {@code INFEASIBLE}, {@code LIMIT} or {@code
   *     UNBOUNDED}
   */
  int solve(int limit);

  /**
   * Returns the Farkas multipliers of the rows after an infeasible solve.
   *
   * @return the multipliers
   */
  double[] farkas();

  /**
   * Returns the row duals after an optimal solve.
   *
   * @return the duals
   */
  double[] duals();

  /**
   * Returns the objective value after an optimal solve.
   *
   * @return the objective
   */
  double objective();

  /**
   * Returns the value of a column after a solve.
   *
   * @param j the column
   * @return its value
   */
  double value(int j);

  /**
   * Returns the row of the basis a column is basic in.
   *
   * @param j the column
   * @return the row, or -1 when the column is not basic
   */
  int basicRow(int j);

  /**
   * Returns a row of the basis inverse, scaled so that the row's basic column has coefficient 1.
   *
   * @param r the row
   * @return the multipliers of the rows
   */
  double[] inverseRow(int r);

  /**
   * Adds rows in sparse form.
   *
   * @param columns the columns of each row
   * @param weights the coefficients of each row
   * @param rowLo the lower bounds of the rows
   * @param rowHi the upper bounds of the rows
   */
  void addRows(int[][] columns, double[][] weights, double[] rowLo, double[] rowHi);

  /**
   * Removes rows whose slack is basic.
   *
   * @param rows the rows to remove
   * @return the old index of each kept row, or null when nothing was removed
   */
  int[] removeRows(int[] rows);

  /**
   * Saves the current basis, for {@link #restoreBasis(Object)}.
   *
   * @return the basis, or null when the engine cannot restore one
   */
  default Object saveBasis() {
    return null;
  }

  /**
   * Makes a basis saved by {@link #saveBasis()} of this engine the current one.
   *
   * @param basis the basis
   * @return whether it was restored
   */
  default boolean restoreBasis(Object basis) {
    return false;
  }

  /**
   * Returns an independent copy with the same model, bounds and basis.
   *
   * @return the copy
   */
  SparseLp copy();
}
