/*
 * CdclSolverTest.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.cdcl;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link CdclSolver}: answers compared with brute force on random formulas, models
 * checked, assumptions and incremental use, and DIMACS/DRAT input and output.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class CdclSolverTest {

  private static List<int[]> randomFormula(Random rnd, int vars, int clauses, int maxLen) {
    List<int[]> f = new ArrayList<>();
    for (int i = 0; i < clauses; i++) {
      int len = 1 + rnd.nextInt(maxLen);
      int[] c = new int[len];
      for (int k = 0; k < len; k++) {
        int v = 1 + rnd.nextInt(vars);
        c[k] = rnd.nextBoolean() ? v : -v;
      }
      f.add(c);
    }
    return f;
  }

  private static boolean satisfies(List<int[]> f, boolean[] value) {
    for (int[] c : f) {
      boolean sat = false;
      for (int l : c) {
        if (value[Math.abs(l)] == l > 0) {
          sat = true;
          break;
        }
      }
      if (!sat) {
        return false;
      }
    }
    return true;
  }

  private static boolean bruteForce(List<int[]> f, int vars, int[] assumptions) {
    boolean[] value = new boolean[vars + 1];
    for (long m = 0; m < 1L << vars; m++) {
      for (int v = 1; v <= vars; v++) {
        value[v] = (m >> (v - 1) & 1) != 0;
      }
      boolean ok = true;
      for (int a : assumptions) {
        ok &= value[Math.abs(a)] == a > 0;
      }
      if (ok && satisfies(f, value)) {
        return true;
      }
    }
    return false;
  }

  private static boolean[] model(CdclSolver s, int vars) {
    boolean[] value = new boolean[vars + 1];
    for (int v = 1; v <= vars; v++) {
      value[v] = s.modelValue(v);
    }
    return value;
  }

  @Test
  void randomFormulasAgreeWithBruteForce() {
    Random rnd = new Random(42);
    for (int run = 0; run < 3000; run++) {
      int vars = 3 + rnd.nextInt(10);
      List<int[]> f = randomFormula(rnd, vars, 1 + rnd.nextInt(5 * vars), 1 + rnd.nextInt(4));
      CdclSolver s = new CdclSolver();
      s.ensureVars(vars);
      for (int[] c : f) {
        s.addClause(c);
      }
      int result = s.solve();
      boolean expected = bruteForce(f, vars, new int[0]);
      assertEquals(expected ? CdclSolver.SAT : CdclSolver.UNSAT, result, "run " + run);
      if (expected) {
        assertTrue(satisfies(f, model(s, vars)), "model of run " + run);
      }
    }
  }

  @Test
  void assumptionsAndFailedCores() {
    Random rnd = new Random(7);
    for (int run = 0; run < 1000; run++) {
      int vars = 4 + rnd.nextInt(8);
      List<int[]> f = randomFormula(rnd, vars, vars + rnd.nextInt(3 * vars), 3);
      CdclSolver s = new CdclSolver();
      s.ensureVars(vars);
      for (int[] c : f) {
        s.addClause(c);
      }
      // several calls on the same solver: learnt clauses must stay valid across assumptions
      for (int call = 0; call < 4; call++) {
        int k = 1 + rnd.nextInt(3);
        int[] assumed = new int[k];
        for (int i = 0; i < k; i++) {
          int v = 1 + rnd.nextInt(vars);
          assumed[i] = rnd.nextBoolean() ? v : -v;
        }
        int result = s.solve(assumed);
        boolean expected = bruteForce(f, vars, assumed);
        assertEquals(expected ? CdclSolver.SAT : CdclSolver.UNSAT, result, "run " + run);
        if (expected) {
          boolean[] value = model(s, vars);
          assertTrue(satisfies(f, value));
          for (int a : assumed) {
            assertEquals(a > 0, value[Math.abs(a)]);
          }
        } else if (s.isOk()) {
          int[] core = s.failedAssumptions();
          Set<Integer> given = new HashSet<>();
          for (int a : assumed) {
            given.add(a);
          }
          for (int a : core) {
            assertTrue(given.contains(a), "core literal " + a + " is an assumption");
          }
          assertFalse(bruteForce(f, vars, core), "core of run " + run + " is unsatisfiable");
        }
      }
    }
  }

  @Test
  void incrementalClauseAddition() {
    Random rnd = new Random(11);
    for (int run = 0; run < 500; run++) {
      int vars = 5 + rnd.nextInt(7);
      List<int[]> f = new ArrayList<>();
      CdclSolver s = new CdclSolver();
      for (int step = 0; step < 6; step++) {
        for (int[] c : randomFormula(rnd, vars, 2 + rnd.nextInt(vars), 3)) {
          f.add(c);
          s.addClause(c);
        }
        s.ensureVars(vars);
        int result = s.solve();
        boolean expected = bruteForce(f, vars, new int[0]);
        assertEquals(expected ? CdclSolver.SAT : CdclSolver.UNSAT, result, "run " + run);
        if (!expected) {
          break;
        }
        assertTrue(satisfies(f, model(s, vars)));
      }
    }
  }

  private static void pigeonhole(CdclSolver s, int holes) {
    int pigeons = holes + 1;
    for (int p = 0; p < pigeons; p++) {
      int[] c = new int[holes];
      for (int h = 0; h < holes; h++) {
        c[h] = p * holes + h + 1;
      }
      s.addClause(c);
    }
    for (int h = 0; h < holes; h++) {
      for (int p = 0; p < pigeons; p++) {
        for (int q = p + 1; q < pigeons; q++) {
          s.addClause(-(p * holes + h + 1), -(q * holes + h + 1));
        }
      }
    }
  }

  @Test
  void pigeonholeIsUnsatisfiable() {
    CdclSolver s = new CdclSolver();
    pigeonhole(s, 7);
    assertEquals(CdclSolver.UNSAT, s.solve());
    assertFalse(s.isOk());
  }

  @Test
  void conflictLimitStopsTheSearch() {
    CdclSolver s = new CdclSolver();
    pigeonhole(s, 10);
    s.setConflictLimit(100);
    assertEquals(CdclSolver.UNKNOWN, s.solve());
  }

  @Test
  void lubySequence() {
    long[] expected = {1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8};
    for (int i = 0; i < expected.length; i++) {
      assertEquals(expected[i], CdclSolver.luby(i + 1));
    }
  }

  @Test
  void readsDimacsAndWritesDrat() throws IOException {
    String cnf = "c example\np cnf 3 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
    CdclSolver s = new CdclSolver();
    ByteArrayOutputStream proof = new ByteArrayOutputStream();
    DratWriter drat = new DratWriter(proof);
    s.setProof(drat);
    DimacsReader.read(new ByteArrayInputStream(cnf.getBytes(StandardCharsets.US_ASCII)), s);
    assertEquals(3, s.numVars());
    assertEquals(CdclSolver.UNSAT, s.solve());
    drat.close();
    String text = proof.toString(StandardCharsets.US_ASCII);
    assertTrue(text.endsWith("0\n") && text.lines().anyMatch("0"::equals), text);
  }
}
