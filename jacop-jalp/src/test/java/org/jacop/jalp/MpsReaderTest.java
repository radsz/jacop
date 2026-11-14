/*
 * MpsReaderTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import org.assertj.core.data.Offset;
import org.junit.jupiter.api.Test;

/**
 * Tests {@link MpsReader} on small files that use every section and bound type, in free and fixed
 * format, and solves them.
 */
class MpsReaderTest {

  private static LpProblem read(String text) throws IOException {
    return MpsReader.read(
        new ByteArrayInputStream(text.getBytes(StandardCharsets.US_ASCII)), "test");
  }

  // max x + 2y + 3z - w + 10 subject to
  //   c1: x + y + z <= 4,  c2: x - y >= -2,  c3: y + z = 3 with range 1 (so 3 <= y + z <= 4),
  //   c4: z - w in [1, 3] (L row 3 with range 2), x in [0, 3], y free, z <= 2.5, w fixed 1
  private static final String FREE =
      String.join(
          "\n",
          "* a comment",
          "NAME          SMALL",
          "OBJSENSE",
          "    MAX",
          "ROWS",
          " N  obj",
          " L  c1",
          " G  c2",
          " E  c3",
          " L  c4",
          " N  other",
          "COLUMNS",
          "    x  obj 1  c1 1",
          "    x  c2 1",
          "    MARKER  'MARKER'  'INTORG'",
          "    y  obj 2  c1 1",
          "    y  c2 -1  c3 1",
          "    MARKER  'MARKER'  'INTEND'",
          "    z  obj 3  c1 1",
          "    z  c3 1  c4 1",
          "    z  other 7",
          "    w  obj -1  c4 -1",
          "RHS",
          "    rhs  c1 4  c2 -2",
          "    rhs  c3 3  c4 3",
          "    rhs  obj -10",
          "RANGES",
          "    rng  c3 1  c4 2",
          "BOUNDS",
          " UP bnd x 3",
          " FR bnd y",
          " UP bnd z 2.5",
          " FX bnd w 1",
          "ENDATA",
          "");

  @Test
  void readsEverySection() throws IOException {
    LpProblem p = read(FREE);
    assertThat(p.name).isEqualTo("SMALL");
    assertThat(p.maximize).isTrue();
    assertThat(p.rows()).isEqualTo(4);
    assertThat(p.columns()).isEqualTo(4);
    assertThat(p.columnNames).containsExactly("x", "y", "z", "w");
    assertThat(p.integer).containsExactly(false, true, false, false);
    assertThat(p.cost).containsExactly(1, 2, 3, -1);
    assertThat(p.costConstant).isEqualTo(10);
    assertThat(p.rowLo).containsExactly(Double.NEGATIVE_INFINITY, -2, 3, 1);
    assertThat(p.rowHi).containsExactly(4, Double.POSITIVE_INFINITY, 4, 3);
    assertThat(p.colLo).containsExactly(0, Double.NEGATIVE_INFINITY, 0, 1);
    assertThat(p.colHi).containsExactly(3, Double.POSITIVE_INFINITY, 2.5, 1);
    assertThat(p.nonzeros()).isEqualTo(9);
  }

  @Test
  void solvesTheProblemRead() throws IOException {
    LpProblem p = read(FREE);
    for (boolean scale : new boolean[] {false, true}) {
      RevisedDualSimplex lp = p.simplex(scale);
      lp.setExact(true);
      assertThat(lp.solve(1000)).isEqualTo(RevisedDualSimplex.OPTIMAL);
      // x + y + z <= 4 with y + z <= 4, z <= 2.5: the best is z = 2.5, y = 1.5 and x = 0 (value
      // 2 * 1.5 + 3 * 2.5 - 1 = 9.5), against x = 1, y = 0.5 (value 1 + 1 + 7.5 - 1 = 8.5)
      double z = -lp.objective() + p.costConstant;
      assertThat(z).isCloseTo(19.5, Offset.offset(1e-9));
      assertThat(lp.value(2)).isCloseTo(2.5, Offset.offset(1e-9));
    }
  }

  // a data line of fixed MPS: fields in columns 2-3, 5-12, 15-22, 25-36, 40-47 and 50-61
  private static String fields(String f1, String f2, String f3, String f4, String f5, String f6) {
    return String.format(" %-2s %-8s  %-8s  %-12s   %-8s  %s", f1, f2, f3, f4, f5, f6)
        .stripTrailing();
  }

  @Test
  void readsFixedFormatWithSpacesInNames() throws IOException {
    String fixed =
        String.join(
            "\n",
            "NAME          FIXED",
            "ROWS",
            fields("N", "COST", "", "", "", ""),
            fields("G", "ROW 1", "", "", "", ""),
            fields("L", "ROW 2", "", "", "", ""),
            "COLUMNS",
            fields("", "X 1", "COST", "1.0", "ROW 1", "1.0"),
            fields("", "X 1", "ROW 2", "1.0", "", ""),
            fields("", "X 2", "COST", "2.0", "ROW 1", "1.0"),
            "RHS",
            fields("", "", "ROW 1", "2.0", "ROW 2", "1.5"),
            "BOUNDS",
            fields("MI", "BND", "X 2", "", "", ""),
            fields("UP", "BND", "X 2", "5.0", "", ""),
            "ENDATA",
            "");
    LpProblem p = read(fixed);
    assertThat(p.rowNames).containsExactly("ROW 1", "ROW 2");
    assertThat(p.columnNames).containsExactly("X 1", "X 2");
    assertThat(p.colLo).containsExactly(0, Double.NEGATIVE_INFINITY);
    assertThat(p.colHi).containsExactly(Double.POSITIVE_INFINITY, 5);
    RevisedDualSimplex lp = p.simplex(true);
    lp.setExact(true);
    // min x1 + 2 x2 with x1 + x2 >= 2, x1 <= 1.5: x1 = 1.5, x2 = 0.5
    assertThat(lp.solve(100)).isEqualTo(RevisedDualSimplex.OPTIMAL);
    assertThat(lp.objective()).isCloseTo(2.5, Offset.offset(1e-9));
  }

  @Test
  void negativeUpperBoundWithoutLowerMakesTheColumnFree() throws IOException {
    String text =
        String.join(
            "\n",
            "NAME NEG",
            "ROWS",
            " N obj",
            " G r",
            "COLUMNS",
            " x obj 1 r 1",
            "RHS",
            " rhs r -10",
            "BOUNDS",
            " UP b x -1",
            "ENDATA");
    LpProblem p = read(text);
    assertThat(p.colLo[0]).isEqualTo(Double.NEGATIVE_INFINITY);
    assertThat(p.colHi[0]).isEqualTo(-1);
    RevisedDualSimplex lp = p.simplex(true);
    lp.setExact(true);
    assertThat(lp.solve(100)).isEqualTo(RevisedDualSimplex.OPTIMAL);
    assertThat(lp.objective()).isCloseTo(-10, Offset.offset(1e-9));
  }
}
