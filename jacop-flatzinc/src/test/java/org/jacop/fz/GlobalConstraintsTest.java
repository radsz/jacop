/*
 * GlobalConstraintsTest.java
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
package org.jacop.fz;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Stream;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Small FlatZinc models, as MiniZinc 2.9 produces them with the JaCoP library, whose global
 * constraints used to be posted incorrectly. The expected number of solutions was checked against
 * Chuffed with the decompositions of the MiniZinc standard library, or by enumeration.
 */
class GlobalConstraintsTest {

  private static final int TIMEOUT_MS = 15_000;

  @TempDir Path tmp;

  static Stream<Arguments> models() {
    return Stream.of(
        Arguments.of(
            "among with a repeated variable",
            """
            var 0..4: v1:: output_var;
            var 1..3: v2:: output_var;
            var 0..3: v3:: output_var;
            var {0,1,3}: v4:: output_var;
            array [1..4] of var int: x = [v2,v3,v3,v4];
            constraint jacop_among(x,2..3,v1);
            solve satisfy;
            """,
            36),
        Arguments.of(
            "circuit with a repeated constant",
            """
            var 0..1: v1:: output_var;
            array [1..3] of var int: x = [2,2,2];
            constraint jacop_circuit(x);
            solve satisfy;
            """,
            0),
        Arguments.of(
            "subcircuit with a repeated constant",
            """
            var 0..1: v1:: output_var;
            array [1..2] of var int: x = [1,1];
            constraint jacop_subcircuit(x);
            solve satisfy;
            """,
            0),
        Arguments.of(
            "table without tuples",
            """
            var 0..1: v1:: output_var;
            array [1..1] of var int: x = [v1];
            constraint jacop_table_int(x,[]);
            solve satisfy;
            """,
            0),
        Arguments.of(
            "global_cardinality with a repeated cover value",
            """
            array [1..3] of int: cover = [1,0,1];
            var 0..3: v1:: output_var;
            var 0..3: v2:: output_var;
            var 1..3: v3:: output_var;
            var 0..2: v4:: output_var;
            var 1..2: v5:: output_var;
            array [1..3] of var int: counts = [v3,v4,v5];
            array [1..4] of var int: x = [v1,v2,v1,1];
            constraint jacop_count_values(x,cover,counts);
            solve satisfy;
            """,
            11),
        Arguments.of(
            "strictly_increasing that is unsatisfiable",
            """
            var 1..2: v2:: output_var;
            array [1..2] of var int: x = [2,v2];
            constraint jacop_strictly_increasing(x);
            solve satisfy;
            """,
            0),
        Arguments.of(
            "member over Booleans",
            """
            var bool: b1:: output_var;
            var bool: b2:: output_var;
            var bool: b3:: output_var;
            var bool: b4:: output_var;
            var 0..1: y:: is_defined_var;
            array [1..3] of var bool: x = [b1,b2,b3];
            constraint jacop_member_bool(x,y);
            constraint bool2int(b4,y):: defines_var(y);
            solve satisfy;
            """,
            14));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("models")
  @Timeout(TIMEOUT_MS)
  void solutionCountMatches(String name, String model, int expected) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);

    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try {
      System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
      new Fz2jacop().callMain(new String[] {"-a", fzn.toString()});
    } finally {
      System.setOut(originalOut);
    }

    List<String> lines = captured.toString(StandardCharsets.UTF_8).lines().toList();
    if (expected == 0) {
      assertTrue(lines.contains("=====UNSATISFIABLE====="), "expected no solution:\n" + lines);
    } else {
      assertTrue(lines.contains("=========="), "search did not complete:\n" + lines);
      assertEquals(expected, lines.stream().filter("----------"::equals).count(), lines.toString());
    }
  }
}
