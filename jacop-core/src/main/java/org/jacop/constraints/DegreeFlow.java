/*
 * DegreeFlow.java
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
package org.jacop.constraints;

import org.jacop.core.IntVar;

/**
 * A 0/1 matrix with bounds on its row and column sums: which cells must be 1, which must be 0 and
 * how far each sum can range in some matrix that respects all bounds. It is the flow network of the
 * symmetric cardinality constraint (Kocjan and Kreuger, CPAIOR 2004): a source with an arc to each
 * row bounded by the row sum, an arc from row r to column c with flow 0..1 for a free cell, an arc
 * from each column to a sink bounded by the column sum, and an arc back from the sink to the
 * source. Matrices and feasible circulations correspond one to one, so the answers are exact.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class DegreeFlow {

  /** A cell that is 0 in every matrix. */
  static final int ZERO = 0;

  /** A cell that is 1 in every matrix. */
  static final int ONE = 1;

  /** A cell that is 0 in some matrices and 1 in others. */
  static final int FREE = 2;

  private final BoundedFlow flow = new BoundedFlow();
  private int[] cellArc = new int[0];

  /** The status of each cell (row-major) after {@link #solve}, for the cells passed in as free. */
  int[] cell = new int[0];

  /** The tightened bounds of the sums after {@link #solve}. */
  int[] rowLo = new int[0];

  int[] rowUp = new int[0];
  int[] colLo = new int[0];
  int[] colUp = new int[0];

  /**
   * Computes what every matrix within the bounds has in common.
   *
   * @param n the number of rows
   * @param m the number of columns
   * @param cells the status of each cell, row-major: ZERO, ONE or FREE
   * @param rowMin the least sum of each row
   * @param rowMax the largest sum of each row
   * @param colMin the least sum of each column
   * @param colMax the largest sum of each column
   * @param sums whether the bounds of the sums are wanted (rowLo, rowUp, colLo, colUp)
   * @return false if no matrix is within the bounds
   */
  boolean solve(
      int n,
      int m,
      int[] cells,
      int[] rowMin,
      int[] rowMax,
      int[] colMin,
      int[] colMax,
      boolean sums) {
    int source = n + m;
    int sink = source + 1;
    flow.reset(n + m + 2);
    if (cellArc.length < n * m) {
      cellArc = new int[n * m];
      cell = new int[n * m];
    }
    if (rowLo.length < n) {
      rowLo = new int[n];
      rowUp = new int[n];
    }
    if (colLo.length < m) {
      colLo = new int[m];
      colUp = new int[m];
    }
    int[] rowArc = new int[n];
    int[] colArc = new int[m];
    int fixedTotal = 0;
    int totalMax = 0;
    for (int r = 0; r < n; r++) {
      rowArc[r] = flow.addArc(source, r, Math.max(rowMin[r], 0), Math.max(rowMax[r], 0));
      totalMax += Math.max(rowMax[r], 0);
    }
    for (int c = 0; c < m; c++) {
      colArc[c] = flow.addArc(n + c, sink, Math.max(colMin[c], 0), Math.max(colMax[c], 0));
    }
    for (int r = 0; r < n; r++) {
      for (int c = 0; c < m; c++) {
        int k = r * m + c;
        cell[k] = cells[k];
        if (cells[k] == ZERO) {
          cellArc[k] = -1;
        } else {
          cellArc[k] = flow.addArc(r, n + c, cells[k] == ONE ? 1 : 0, 1);
          fixedTotal += cells[k] == ONE ? 1 : 0;
        }
      }
    }
    flow.addArc(sink, source, fixedTotal, Math.max(totalMax, fixedTotal));
    if (!flow.solve()) {
      return false;
    }
    for (int k = 0; k < n * m; k++) {
      if (cells[k] == FREE && !flow.variable(cellArc[k])) {
        cell[k] = flow.flow(cellArc[k]) == 1 ? ONE : ZERO;
      }
    }
    if (sums) {
      for (int r = 0; r < n; r++) {
        rowUp[r] = flow.maxFlowOn(rowArc[r]);
        rowLo[r] = flow.minFlowOn(rowArc[r]);
      }
      for (int c = 0; c < m; c++) {
        colUp[c] = flow.maxFlowOn(colArc[c]);
        colLo[c] = flow.minFlowOn(colArc[c]);
      }
    }
    return true;
  }

  /** How a reason cites the status of a cell in {@link #explain}. */
  interface CellReason {
    /**
     * Cites that cell k is 0.
     *
     * @param k the cell, row-major
     */
    void zero(int k);

    /**
     * Cites that cell k is 1.
     *
     * @param k the cell, row-major
     */
    void one(int k);
  }

  /**
   * Explains that no matrix is within the bounds, for lazy clause generation: builds the network,
   * with an arc of flow 0 for every cell that is 0 and no bound on the arc back to the source (its
   * bounds are implied), and when it has no feasible circulation cites what bounds the arcs across
   * its cut: the counters' bounds below n or m and above 0, and the cells that are 0 on arcs
   * leaving the cut or 1 on arcs entering it.
   *
   * @param n the number of rows
   * @param m the number of columns
   * @param cells the status of each cell, row-major: ZERO, ONE or FREE
   * @param rowMin the least sum of each row, at least 0
   * @param rowMax the largest sum of each row, at most m
   * @param colMin the least sum of each column, at least 0
   * @param colMax the largest sum of each column, at most n
   * @param rows the counter of each row, whose bounds the reason cites
   * @param cols the counter of each column
   * @param reason the reason
   * @param cellReason how the status of a cell is cited
   * @return true when the network is infeasible and the reason is gathered
   */
  boolean explain(
      int n,
      int m,
      int[] cells,
      int[] rowMin,
      int[] rowMax,
      int[] colMin,
      int[] colMax,
      IntVar[] rows,
      IntVar[] cols,
      FlowReason reason,
      CellReason cellReason) {
    int source = n + m;
    int sink = source + 1;
    flow.reset(n + m + 2);
    for (int r = 0; r < n; r++) {
      if (rowMin[r] > rowMax[r]) {
        return false;
      }
      flow.addArc(source, r, rowMin[r], rowMax[r]);
    }
    for (int c = 0; c < m; c++) {
      if (colMin[c] > colMax[c]) {
        return false;
      }
      flow.addArc(n + c, sink, colMin[c], colMax[c]);
    }
    for (int k = 0; k < n * m; k++) {
      int status = cells[k];
      flow.addArc(k / m, n + k % m, status == ONE ? 1 : 0, status == ZERO ? 0 : 1);
    }
    flow.addArc(sink, source, 0, BoundedFlow.INFINITE);
    if (flow.solve() || !FlowReason.violated(flow)) {
      return false;
    }
    boolean sourceIn = flow.inCut(source);
    boolean sinkIn = flow.inCut(sink);
    for (int r = 0; r < n; r++) {
      boolean in = flow.inCut(r);
      if (sourceIn && !in && rowMax[r] < m) {
        reason.needUpper(rows[r], rowMax[r]);
      } else if (!sourceIn && in && rowMin[r] > 0) {
        reason.needLower(rows[r], rowMin[r]);
      }
    }
    for (int c = 0; c < m; c++) {
      boolean in = flow.inCut(n + c);
      if (in && !sinkIn && colMax[c] < n) {
        reason.needUpper(cols[c], colMax[c]);
      } else if (!in && sinkIn && colMin[c] > 0) {
        reason.needLower(cols[c], colMin[c]);
      }
    }
    for (int k = 0; k < n * m; k++) {
      boolean rowIn = flow.inCut(k / m);
      boolean colIn = flow.inCut(n + k % m);
      if (rowIn && !colIn && cells[k] == ZERO) {
        cellReason.zero(k);
      } else if (!rowIn && colIn && cells[k] == ONE) {
        cellReason.one(k);
      }
    }
    return true;
  }
}
