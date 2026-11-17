/*
 * GateExtractorTest.java
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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests {@link GateExtractor}: each gate kind on its defining clauses, and on random formulas that
 * every gate found is implied by the clauses it names.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class GateExtractorTest {

  private static int lit(int dimacs) {
    return dimacs > 0 ? 2 * (dimacs - 1) : 2 * (-dimacs - 1) + 1;
  }

  private static GateExtractor extractor(int numVars, int[][] dimacs) {
    int[][] clauses = new int[dimacs.length][];
    int[][] occ = new int[2 * numVars][];
    int[] occSize = new int[2 * numVars];
    for (int l = 0; l < 2 * numVars; l++) {
      occ[l] = new int[dimacs.length];
    }
    for (int i = 0; i < dimacs.length; i++) {
      clauses[i] = Arrays.stream(dimacs[i]).map(GateExtractorTest::lit).toArray();
      for (int l : clauses[i]) {
        occ[l][occSize[l]++] = i;
      }
    }
    return new GateExtractor(clauses, occ, occSize, numVars);
  }

  @Test
  void equivalence() {
    GateExtractor x = extractor(3, new int[][] {{-1, 2}, {1, -2}, {2, 3}});
    GateExtractor.Gate g = x.find(lit(1));
    assertNotNull(g);
    assertEquals(GateExtractor.EQUIV, g.kind);
    assertArrayEquals(new int[] {lit(2)}, g.inputs);
  }

  @Test
  void andAndOr() {
    // 1 = 2 & -3 & 4
    int[][] cnf = {{-1, 2}, {-1, -3}, {-1, 4}, {1, -2, 3, -4}};
    GateExtractor x = extractor(4, cnf);
    GateExtractor.Gate g = x.find(lit(1));
    assertNotNull(g);
    assertEquals(GateExtractor.AND, g.kind);
    int[] inputs = {lit(2), lit(-3), lit(4)};
    Arrays.sort(inputs);
    assertArrayEquals(inputs, g.inputs);
    assertEquals(4, g.clauses.length);
    // -1 = -2 | 3 | -4 is the same gate as an OR gate: not found on -1
    assertNull(x.findAnd(lit(-1)));
  }

  @Test
  void ite() {
    // 1 = -2 ? 3 : 4, normalised to 2 ? 4 : 3
    int[][] cnf = {{-1, 2, 3}, {-1, -2, 4}, {1, 2, -3}, {1, -2, -4}};
    GateExtractor.Gate g = extractor(4, cnf).find(lit(1));
    assertNotNull(g);
    assertEquals(GateExtractor.ITE, g.kind);
    assertArrayEquals(new int[] {lit(2), lit(4), lit(3)}, g.inputs);
  }

  @Test
  void xor() {
    // 1 = 2 ^ 3: the clauses forbid assignments with 1 != 2 ^ 3
    int[][] cnf = {{-1, 2, 3}, {-1, -2, -3}, {1, -2, 3}, {1, 2, -3}};
    GateExtractor.Gate g = extractor(3, cnf).find(lit(1));
    assertNotNull(g);
    assertEquals(GateExtractor.XOR, g.kind);
    assertEquals(lit(1), g.output);
    // the negated output gives the same gate
    GateExtractor.Gate h = extractor(3, cnf).find(lit(-1));
    assertEquals(GateExtractor.XOR, h.kind);
    assertEquals(lit(1), h.output);
    // 1 = -(2 ^ 3)
    int[][] neg = {{1, 2, 3}, {1, -2, -3}, {-1, -2, 3}, {-1, 2, -3}};
    assertEquals(lit(-1), extractor(3, neg).find(lit(1)).output);
  }

  @Test
  void missingClauseNoGate() {
    int[][] cnf = {{-1, 2, 3}, {-1, -2, -3}, {1, -2, 3}};
    assertNull(extractor(3, cnf).find(lit(1)));
  }

  /** On random formulas, every gate found holds in every assignment of its clauses. */
  @Test
  void randomGatesAreImplied() {
    Random rnd = new Random(7);
    int gates = 0;
    for (int run = 0; run < 3000; run++) {
      int n = 3 + rnd.nextInt(4);
      List<int[]> cnf = new ArrayList<>();
      int m = 2 + rnd.nextInt(14);
      for (int i = 0; i < m; i++) {
        int size = 2 + rnd.nextInt(3);
        int[] vars = rnd.ints(1, n + 1).distinct().limit(Math.min(size, n)).toArray();
        cnf.add(Arrays.stream(vars).map(v -> rnd.nextBoolean() ? v : -v).toArray());
      }
      int[][] f = cnf.toArray(new int[0][]);
      GateExtractor x = extractor(n, f);
      for (int l = 0; l < 2 * n; l++) {
        GateExtractor.Gate g = x.find(l);
        if (g != null) {
          gates++;
          assertTrue(implied(n, f, g), g + " on " + Arrays.deepToString(f));
        }
      }
    }
    assertTrue(gates > 100, "too few gates: " + gates);
  }

  private static boolean value(int lit, int assignment) {
    return ((assignment >> (lit >> 1)) & 1) != (lit & 1);
  }

  private static boolean implied(int n, int[][] f, GateExtractor.Gate g) {
    for (int asg = 0; asg < 1 << n; asg++) {
      final int a = asg;
      boolean sat = true;
      for (int i : g.clauses) {
        boolean c = false;
        for (int l : f[i]) {
          c |= value(lit(l), a);
        }
        sat &= c;
      }
      if (!sat) {
        continue;
      }
      boolean expected;
      int[] in = g.inputs;
      switch (g.kind) {
        case GateExtractor.EQUIV -> expected = value(in[0], a);
        case GateExtractor.AND -> expected = Arrays.stream(in).allMatch(l -> value(l, a));
        case GateExtractor.ITE -> expected = value(in[0], a) ? value(in[1], a) : value(in[2], a);
        default -> {
          boolean x = false;
          for (int l : in) {
            x ^= value(l, a);
          }
          expected = x;
        }
      }
      if (value(g.output, a) != expected) {
        return false;
      }
    }
    return true;
  }
}
