/*
 * JalpSimplex.java
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

import org.jacop.jalp.RevisedDualSimplex;

/**
 * The simplex of JaLP ({@link RevisedDualSimplex}, module jacop-jalp) behind the interface of the
 * relaxation: the sparse simplex of {@link LinearRelaxation.Simplex#SPARSE} and {@link
 * LinearRelaxation.Simplex#LAZY}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class JalpSimplex implements LpSolver {

  private final RevisedDualSimplex lp;

  /**
   * Creates the problem with the slack basis.
   *
   * @param columns the columns of each row
   * @param weights the weights of each row, matching its columns
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective over the n columns, minimized
   */
  JalpSimplex(int[][] columns, double[][] weights, double[] rowLo, double[] rowHi, double[] cost) {
    lp = new RevisedDualSimplex(columns, weights, rowLo, rowHi, cost, true);
  }

  private JalpSimplex(RevisedDualSimplex lp) {
    this.lp = lp;
  }

  @Override
  public int rows() {
    return lp.rows();
  }

  @Override
  public int columns() {
    return lp.columns();
  }

  @Override
  public long pivots() {
    return lp.pivots();
  }

  @Override
  public long pivotWork() {
    return lp.pivotWork();
  }

  @Override
  public long work() {
    return lp.work();
  }

  @Override
  public void setBounds(int j, double min, double max) {
    lp.setBounds(j, min, max);
  }

  @Override
  public int solve(int limit) {
    int status = lp.solve(limit);
    // an unbounded relaxation (no finite bound on the objective) prunes nothing, like a limit
    return status == RevisedDualSimplex.UNBOUNDED ? LIMIT : status;
  }

  @Override
  public double[] farkas() {
    return lp.farkas();
  }

  @Override
  public double[] duals() {
    return lp.duals();
  }

  @Override
  public double objective() {
    return lp.objective();
  }

  @Override
  public double value(int j) {
    return lp.value(j);
  }

  @Override
  public int basicRow(int j) {
    return lp.basicRow(j);
  }

  @Override
  public double[] inverseRow(int r) {
    return lp.inverseRow(r);
  }

  @Override
  public void addRows(double[][] rows, double[] rowLo, double[] rowHi) {
    int[][] c = new int[rows.length][];
    double[][] w = new double[rows.length][];
    for (int i = 0; i < rows.length; i++) {
      int nz = 0;
      for (double v : rows[i]) {
        if (v != 0) {
          nz++;
        }
      }
      c[i] = new int[nz];
      w[i] = new double[nz];
      nz = 0;
      for (int j = 0; j < rows[i].length; j++) {
        if (rows[i][j] != 0) {
          c[i][nz] = j;
          w[i][nz++] = rows[i][j];
        }
      }
    }
    lp.addRows(c, w, rowLo, rowHi);
  }

  @Override
  public void addRows(int[][] columns, double[][] weights, double[] rowLo, double[] rowHi) {
    lp.addRows(columns, weights, rowLo, rowHi);
  }

  @Override
  public int[] removeRows(int[] rows) {
    return lp.removeRows(rows);
  }

  @Override
  public Object saveBasis() {
    return lp.saveBasis();
  }

  @Override
  public boolean restoreBasis(Object basis) {
    return basis instanceof RevisedDualSimplex.Basis b && lp.restoreBasis(b);
  }

  @Override
  public LpSolver copy() {
    return new JalpSimplex(lp.copy());
  }
}
