/*
 * ComplementSymmetryTest.java
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
package org.jacop.jasat.cdcl;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/** Tests of {@link ComplementSymmetry}. */
class ComplementSymmetryTest {

  @Test
  void notAllEqualTriplesFixTheMostFrequentVariable() {
    // the not-all-equal triples (3, 4, 5), (5, 12, 13), (6, 8, 10): 5 occurs most
    List<int[]> clauses = new ArrayList<>();
    for (int[] t : new int[][] {{3, 4, 5}, {5, 12, 13}, {6, 8, 10}}) {
      clauses.add(t);
      clauses.add(new int[] {-t[2], -t[0], -t[1]});
    }
    assertEquals(5, ComplementSymmetry.fixedVariable(clauses, 13));
  }

  @Test
  void aClauseWithoutItsComplementFixesNothing() {
    List<int[]> clauses = new ArrayList<>(List.of(new int[] {1, 2}, new int[] {-1, -2}));
    assertEquals(1, ComplementSymmetry.fixedVariable(clauses, 2));
    clauses.add(new int[] {1, -2});
    assertEquals(0, ComplementSymmetry.fixedVariable(clauses, 2));
    assertEquals(0, ComplementSymmetry.fixedVariable(List.of(), 2));
  }

  @Test
  void repeatedLiteralsCompareAsSets() {
    List<int[]> clauses = List.of(new int[] {1, 1, -2}, new int[] {2, -1});
    assertEquals(1, ComplementSymmetry.fixedVariable(clauses, 2));
  }

  @Test
  void theFixedVariableKeepsSatisfiability() {
    // random not-all-equal formulas: with the unit, the solver answers as without it
    Random random = new Random(20261118);
    for (int run = 0; run < 300; run++) {
      int n = 4 + random.nextInt(8);
      int m = 1 + random.nextInt(4 * n);
      List<int[]> clauses = new ArrayList<>();
      for (int i = 0; i < m; i++) {
        int[] c = new int[2 + random.nextInt(2)];
        for (int k = 0; k < c.length; k++) {
          c[k] = (1 + random.nextInt(n)) * (random.nextBoolean() ? 1 : -1);
        }
        int[] d = new int[c.length];
        for (int k = 0; k < c.length; k++) {
          d[k] = -c[k];
        }
        clauses.add(c);
        clauses.add(d);
      }
      int v = ComplementSymmetry.fixedVariable(clauses, n);
      assertTrue(v > 0, "run " + run);
      int without = solve(clauses, n, 0);
      int with = solve(clauses, n, v);
      assertEquals(without, with, "run " + run);
    }
  }

  private static int solve(List<int[]> clauses, int n, int unit) {
    CdclSolver solver = new CdclSolver();
    solver.ensureVars(n);
    for (int[] c : clauses) {
      solver.addClause(c.clone(), c.length);
    }
    if (unit != 0) {
      solver.addClause(new int[] {unit}, 1);
    }
    return solver.solve();
  }
}
