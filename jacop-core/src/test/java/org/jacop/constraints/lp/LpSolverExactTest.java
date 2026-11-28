/*
 * LpSolverExactTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Test;

/**
 * Checks the dense simplex and JaLP against an exact rational simplex ({@link LpExactFuzz}): seeded
 * LPs of several families (degenerate, parallel rows and columns, wide scales, equations, big-M
 * rows, knapsacks, infeasible, unbounded) and seeded sequences of chunked solves, branching bound
 * changes and backtracks, row bound changes, cuts added and removed, bases saved and restored, and
 * copies. The dense simplex and JaLP behind {@link JalpSimplex} get bounded columns, as the
 * relaxation's integer columns are; JaLP's own {@code RevisedDualSimplex} also gets infinite
 * bounds, new costs solved by the primal simplex, the exact clean-up, presolve and crash bases.
 * After every solve the status, the objective, the primal point, the Lagrangian bound of the duals
 * and the Farkas row of an infeasibility are checked exactly. The number of seeds is {@code
 * lp.exact.runs} (default 200, about 4 s); the campaign of osolpro benchmarks/jalp-allsolutions ran
 * 40,000.
 */
class LpSolverExactTest {

  private static final int RUNS = Integer.getInteger("lp.exact.runs", 200);

  @Test
  void simplexAnswersAgreeWithExactArithmetic() {
    List<String> findings = new ArrayList<>();
    for (int engine = 0; engine < 3; engine++) {
      for (long seed = 1; seed <= RUNS; seed++) {
        String f = LpExactFuzz.runCase(seed * 7 + engine, engine);
        if (f != null) {
          findings.add("seed " + seed + " engine " + LpExactFuzz.engineName(engine) + ": " + f);
        }
      }
    }
    assertThat(findings).isEmpty();
    // the cases reach optimal and infeasible answers alike
    assertThat(LpExactFuzz.statusCount[LpExactFuzz.R_OPTIMAL]).isGreaterThan(RUNS);
    assertThat(LpExactFuzz.statusCount[LpExactFuzz.R_INFEASIBLE]).isGreaterThan(RUNS);
  }
}
