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

import org.jacop.jalp.HighsLp;

/**
 * HiGHS for the root, JaLP for the search: the relaxation is solved by HiGHS ({@link HighsLp})
 * until {@link #afterRoot()}, which the relaxation calls when its first call (the root solve, its
 * extra rows and its cut rounds) is over; then the problem and the basis HiGHS ended with go to
 * JaLP, whose cost per call is lower on the small changes of bounds of the search. Used with {@code
 * -Dorg.jacop.lp.engine=highs-root}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class HandoffSimplex extends JalpSimplex {

  // the most pivots JaLP may take to settle on the basis it got from HiGHS
  private static final int HANDOFF_PIVOTS = 100_000;

  // the HiGHS engine until the hand-off, then null
  private HighsLp highs;
  // the pivots and work of HiGHS before the hand-off (0 until then), so that pivots() and work()
  // keep counting up
  private long highsPivots;
  private long highsWork;

  /**
   * Creates the problem with the slack basis, in HiGHS.
   *
   * @param columns the columns of each row
   * @param weights the weights of each row, matching its columns
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective over the n columns, minimized
   */
  HandoffSimplex(
      int[][] columns, double[][] weights, double[] rowLo, double[] rowHi, double[] cost) {
    this(new HighsLp(columns, weights, rowLo, rowHi, cost));
  }

  private HandoffSimplex(HighsLp highs) {
    super(highs);
    this.highs = highs;
  }

  @Override
  public LpSolver afterRoot() {
    if (highs != null) {
      highsPivots = highs.pivots();
      highsWork = highs.work();
      engine(highs.toJalp());
      highs = null;
      // JaLP factorizes the basis of HiGHS and computes its solution now, so that the values,
      // duals and rows of the inverse it answers with are those of the root; from an optimal
      // basis this takes no pivot, or a few to repair the round-off of a basis from another code
      solve(HANDOFF_PIVOTS);
    }
    return this;
  }

  @Override
  public long pivots() {
    return highsPivots + super.pivots();
  }

  @Override
  public long work() {
    return highsWork + super.work();
  }

  @Override
  public LpSolver copy() {
    HandoffSimplex c;
    if (highs != null) {
      c = new HandoffSimplex(highs.copy());
    } else {
      c = new HandoffSimplex(null);
      c.engine(engine().copy());
    }
    c.highsPivots = highsPivots;
    c.highsWork = highsWork;
    return c;
  }
}
