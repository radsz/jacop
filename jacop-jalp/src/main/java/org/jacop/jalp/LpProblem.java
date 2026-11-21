/*
 * LpProblem.java
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
 * A linear program {@code min (or max) c x + c0} subject to {@code rowLo <= A x <= rowHi} and
 * {@code colLo <= x <= colHi}, with A stored by rows. Infinite bounds are the double infinities.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LpProblem {

  /** The name of the problem. */
  public final String name;

  /** The names of the columns. */
  public final String[] columnNames;

  /** The names of the rows. */
  public final String[] rowNames;

  /** The columns of the nonzeros of each row. */
  public final int[][] rowColumns;

  /** The nonzeros of each row, matching {@link #rowColumns}. */
  public final double[][] rowValues;

  /** The lower bounds of the rows. */
  public final double[] rowLo;

  /** The upper bounds of the rows. */
  public final double[] rowHi;

  /** The lower bounds of the columns. */
  public final double[] colLo;

  /** The upper bounds of the columns. */
  public final double[] colHi;

  /** The objective over the columns, in the sense of {@link #maximize}. */
  public final double[] cost;

  /** The constant of the objective. */
  public final double costConstant;

  /** Whether the objective is maximized. */
  public final boolean maximize;

  /** Whether each column is marked integer (the LP ignores it). */
  public final boolean[] integer;

  /**
   * Creates a problem.
   *
   * @param name the name
   * @param columnNames the names of the columns
   * @param rowNames the names of the rows
   * @param rowColumns the columns of the nonzeros of each row
   * @param rowValues the nonzeros of each row
   * @param rowLo the lower bounds of the rows
   * @param rowHi the upper bounds of the rows
   * @param colLo the lower bounds of the columns
   * @param colHi the upper bounds of the columns
   * @param cost the objective
   * @param costConstant the constant of the objective
   * @param maximize whether the objective is maximized
   * @param integer whether each column is integer
   */
  @SuppressWarnings("checkstyle:ParameterNumber")
  public LpProblem(
      String name,
      String[] columnNames,
      String[] rowNames,
      int[][] rowColumns,
      double[][] rowValues,
      double[] rowLo,
      double[] rowHi,
      double[] colLo,
      double[] colHi,
      double[] cost,
      double costConstant,
      boolean maximize,
      boolean[] integer) {
    this.name = name;
    this.columnNames = columnNames;
    this.rowNames = rowNames;
    this.rowColumns = rowColumns;
    this.rowValues = rowValues;
    this.rowLo = rowLo;
    this.rowHi = rowHi;
    this.colLo = colLo;
    this.colHi = colHi;
    this.cost = cost;
    this.costConstant = costConstant;
    this.maximize = maximize;
    this.integer = integer;
  }

  /**
   * Returns the number of rows.
   *
   * @return the rows
   */
  public int rows() {
    return rowLo.length;
  }

  /**
   * Returns the number of columns.
   *
   * @return the columns
   */
  public int columns() {
    return colLo.length;
  }

  /**
   * Returns the number of nonzeros of A.
   *
   * @return the nonzeros
   */
  public long nonzeros() {
    long z = 0;
    for (int[] r : rowColumns) {
      z += r.length;
    }
    return z;
  }

  /**
   * Creates a simplex for the problem, minimizing (the objective is negated for a maximization).
   *
   * @param scale whether to scale the problem
   * @return the simplex, with the bounds of the columns set
   */
  public RevisedDualSimplex simplex(boolean scale) {
    double[] c = cost.clone();
    if (maximize) {
      for (int j = 0; j < c.length; j++) {
        c[j] = -c[j];
      }
    }
    RevisedDualSimplex lp = new RevisedDualSimplex(rowColumns, rowValues, rowLo, rowHi, c, scale);
    for (int j = 0; j < colLo.length; j++) {
      lp.setBounds(j, colLo[j], colHi[j]);
    }
    return lp;
  }
}
