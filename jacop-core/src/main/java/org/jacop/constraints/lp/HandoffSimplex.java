/*
 * HandoffSimplex.java
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
 * HiGHS for the root, JaLP for the search: the relaxation is solved by HiGHS ({@link HighsSimplex},
 * HiGHS's {@code org.jacop.jalp.HighsLp}) until {@link #afterRoot()}, which the relaxation calls
 * when its first call (the root solve, its extra rows and its cut rounds) is over; then the problem
 * and the basis HiGHS ended with go to JaLP ({@link JalpSimplex}), whose cost per call is lower on
 * the small changes of bounds of the search. Used with {@code -Dorg.jacop.lp.engine=highs-root}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class HandoffSimplex implements LpSolver {

  // the most pivots JaLP may take to settle on the basis it got from HiGHS
  private static final int HANDOFF_PIVOTS = 100_000;

  private HighsSimplex highs;
  private LpSolver lp;
  // the pivots HiGHS made before the hand-off, so that pivots() keeps counting up
  private long highsPivots;
  private long highsWork;

  HandoffSimplex(
      int[][] columns, double[][] weights, double[] rowLo, double[] rowHi, double[] cost) {
    highs = new HighsSimplex(columns, weights, rowLo, rowHi, cost);
    lp = highs;
  }

  private HandoffSimplex(HighsSimplex highs, LpSolver lp, long highsPivots, long highsWork) {
    this.highs = highs;
    this.lp = lp;
    this.highsPivots = highsPivots;
    this.highsWork = highsWork;
  }

  @Override
  public LpSolver afterRoot() {
    if (highs != null) {
      highsPivots = highs.pivots();
      highsWork = highs.work();
      lp = new JalpSimplex(highs.toJalp());
      highs = null;
      // JaLP factorizes the basis of HiGHS and computes its solution now, so that the values,
      // duals and rows of the inverse it answers with are those of the root; from an optimal
      // basis this takes no pivot, or a few to repair the round-off of a basis from another code
      lp.solve(HANDOFF_PIVOTS);
    }
    return this;
  }

  /**
   * Returns whether the problem is still with HiGHS.
   *
   * @return true before {@link #afterRoot()}
   */
  boolean inHighs() {
    return highs != null;
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
    return highsPivots + lp.pivots();
  }

  @Override
  public long pivotWork() {
    return lp.pivotWork();
  }

  @Override
  public long work() {
    return highsWork + lp.work();
  }

  @Override
  public void setBounds(int j, double min, double max) {
    lp.setBounds(j, min, max);
  }

  @Override
  public int solve(int limit) {
    return lp.solve(limit);
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
    lp.addRows(rows, rowLo, rowHi);
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
  public LpSolver copy() {
    LpSolver c = lp.copy();
    return new HandoffSimplex(highs == null ? null : (HighsSimplex) c, c, highsPivots, highsWork);
  }
}
