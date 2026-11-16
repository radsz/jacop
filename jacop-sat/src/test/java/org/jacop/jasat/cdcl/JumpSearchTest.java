/*
 * JumpSearchTest.java
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

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Random;
import org.junit.jupiter.api.Test;

/** Tests of the feasibility-jump local search and of its use in {@link CdclSolver}. */
class JumpSearchTest {

  // a random k-SAT formula with a planted model: every clause has a literal true in it
  private static int[][] planted(Random rnd, int vars, int clauses, int k, boolean[] model) {
    for (int v = 0; v < vars; v++) {
      model[v] = rnd.nextBoolean();
    }
    int[][] f = new int[clauses][];
    for (int c = 0; c < clauses; c++) {
      int[] clause = new int[k];
      boolean sat = false;
      while (!sat) {
        for (int i = 0; i < k; i++) {
          int v = rnd.nextInt(vars);
          clause[i] = rnd.nextBoolean() ? v + 1 : -(v + 1);
          sat |= clause[i] > 0 == model[v];
        }
      }
      f[c] = clause;
    }
    return f;
  }

  private static boolean satisfies(int[][] f, byte[] signs) {
    for (int[] c : f) {
      boolean sat = false;
      for (int l : c) {
        sat |= signs[Math.abs(l) - 1] == (l > 0 ? 0 : 1);
      }
      if (!sat) {
        return false;
      }
    }
    return true;
  }

  private static JumpSearch search(int vars, int[][] f, long seed) {
    int size = 0;
    for (int[] c : f) {
      size += c.length;
    }
    int[] lits = new int[size];
    int[] start = new int[f.length + 1];
    int k = 0;
    for (int c = 0; c < f.length; c++) {
      start[c] = k;
      for (int l : f[c]) {
        lits[k++] = l > 0 ? 2 * (l - 1) : 2 * (-l - 1) + 1;
      }
    }
    start[f.length] = k;
    return new JumpSearch(vars, lits, start, f.length, new byte[vars], seed);
  }

  @Test
  void lubySequence() {
    long[] expected = {1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1};
    long[] got = new long[expected.length];
    for (int i = 0; i < got.length; i++) {
      got[i] = JumpSearch.luby(i);
    }
    assertArrayEquals(expected, got);
  }

  @Test
  void findsModelsOfPlantedFormulas() {
    Random rnd = new Random(7);
    for (int run = 0; run < 20; run++) {
      int vars = 50 + rnd.nextInt(200);
      int[][] f = planted(rnd, vars, (int) (4.0 * vars), 3, new boolean[vars]);
      JumpSearch s = search(vars, f, run);
      assertTrue(s.run(Long.MAX_VALUE, () -> false), "run " + run);
      assertTrue(satisfies(f, s.signs()), "run " + run);
      assertEquals(0, s.bestUnsat());
    }
  }

  @Test
  void stopsOnAnUnsatisfiableFormula() {
    // all four clauses over two variables: no model, the search must stop at its tick limit
    int[][] f = {{1, 2}, {1, -2}, {-1, 2}, {-1, -2}};
    JumpSearch s = search(2, f, 1);
    assertFalse(s.run(1_000_000, () -> false));
    assertTrue(s.ticks() >= 1_000_000);
    assertTrue(s.restarts() > 0);
    assertEquals(1, s.bestUnsat());
    int[] calls = {0};
    assertFalse(s.run(Long.MAX_VALUE, () -> ++calls[0] > 3));
    assertEquals(4, calls[0]);
  }

  @Test
  void solverHandsTheModelOfTheLocalSearchToTheSearch() {
    // planted 3-SAT near the threshold: CDCL needs thousands of conflicts, the local search a few
    // thousand flips; with most of the (virtual, so repeatable) clock given to it, the local search
    // finds a model at the second rephasing and the decisions descend to it
    for (int vars : new int[] {600, 1000, 2000}) {
      Random rnd = new Random(3);
      int[][] f = planted(rnd, vars, (int) (4.2 * vars), 3, new boolean[vars]);
      CdclSolver s = new CdclSolver();
      s.setJumpShare(0.9);
      s.setVirtualClock(true);
      for (int[] c : f) {
        s.addClause(c);
      }
      assertEquals(CdclSolver.SAT, s.solve());
      assertEquals(1, s.jumpModels(), "vars " + vars);
      assertTrue(s.jumpSolved(), "vars " + vars);
      byte[] signs = new byte[vars];
      for (int v = 0; v < vars; v++) {
        signs[v] = (byte) (s.modelValue(v + 1) ? 0 : 1);
      }
      assertTrue(satisfies(f, signs), "vars " + vars);
      // the search alone solves it too, without a model of the local search
      CdclSolver plain = new CdclSolver();
      plain.setJumpShare(0);
      for (int[] c : f) {
        plain.addClause(c);
      }
      assertEquals(CdclSolver.SAT, plain.solve());
      assertFalse(plain.jumpSolved());
      assertEquals(0, plain.jumpModels());
    }
  }

  @Test
  void shareOutsideZeroToOneIsRefused() {
    CdclSolver s = new CdclSolver();
    assertThrows(IllegalArgumentException.class, () -> s.setJumpShare(1));
    assertThrows(IllegalArgumentException.class, () -> s.setJumpShare(-0.1));
    assertThrows(IllegalArgumentException.class, () -> s.setJumpShare(Double.NaN));
    s.setJumpShare(0);
    assertEquals(0, s.jumpModels());
  }

  @Test
  void factoredVariablesAreResolvedAwayAndExtended() {
    // x5 v a, x5 v b, -x5 v c, -x5 v d (the form bounded variable addition gives (a & b) | (c &
    // d)),
    // plus -a v -c: the local search sees a v c, a v d, b v c, b v d, -a v -c over a..d only
    int[][] f = {{5, 1}, {5, 2}, {-5, 3}, {-5, 4}, {-1, -3}};
    int[] lits = new int[11];
    int[] start = new int[f.length + 1];
    int k = 0;
    for (int c = 0; c < f.length; c++) {
      start[c] = k;
      for (int l : f[c]) {
        lits[k++] = l > 0 ? 2 * (l - 1) : 2 * (-l - 1) + 1;
      }
    }
    start[f.length] = k;
    JumpSearch.Unfactored u = JumpSearch.unfactor(lits, start, f.length, 4, 5, 1000);
    assertEquals(5, u.numClauses);
    for (int i = 0; i < u.start[u.numClauses]; i++) {
      assertTrue(u.lits[i] >> 1 < 4);
    }
    for (int seed = 0; seed < 20; seed++) {
      JumpSearch s = new JumpSearch(5, u.lits, u.start, u.numClauses, new byte[5], seed);
      assertTrue(s.run(Long.MAX_VALUE, () -> false));
      byte[] signs = s.signs().clone();
      signs[4] = (byte) (seed & 1);
      u.extend(signs);
      assertTrue(satisfies(f, signs), "seed " + seed);
    }
    // a limit below the size of the resolvents gives up
    assertNull(JumpSearch.unfactor(lits, start, f.length, 4, 5, 5));
  }
}
