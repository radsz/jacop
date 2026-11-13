/*
 * RootProbingFlatzincTest.java
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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of root probing under --lcg (-Djacop.lcg.probe), which may only add facts: a model with a
 * solution keeps it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Timeout(60)
class RootProbingFlatzincTest {

  @TempDir Path tmp;

  /**
   * Two element constraints over one set variable: x = 2 gives {1, 3}, which no value of w gives.
   * Early probing (before the linear relaxation) ran before the set variables were mirrored for
   * LCG, so the failure of the second element constraint on x = 2 had the empty explanation and
   * refuted the model (as on MiniZinc Challenge 2024 harmony canon).
   */
  private static final String TWO_SET_ELEMENTS =
      """
      var 1..3: x :: output_var;
      var 1..3: w :: output_var;
      var set of 1..4: s :: output_var;
      constraint array_set_element(x, [{1,2},{1,3},{3,4}], s);
      constraint array_set_element(w, [{1,2},{3,4},{2,3}], s);
      solve satisfy;
      """;

  @Test
  void earlyProbingKeepsTheSolutionOfASetModel() throws IOException {
    String out = solveWith(TWO_SET_ELEMENTS, "jacop.lcg.probe.early", "true");
    assertTrue(out.contains("----------"), out);
    assertFalse(out.contains("UNSATISFIABLE"), out);
  }

  @Test
  void probingKeepsTheSolutionOfASetModel() throws IOException {
    String out = solveWith(TWO_SET_ELEMENTS, "jacop.lcg.probe.early", "false");
    assertTrue(out.contains("----------"), out);
    assertFalse(out.contains("UNSATISFIABLE"), out);
  }

  private String solveWith(String model, String property, String value) throws IOException {
    System.setProperty("jacop.lcg.probe", "0.5");
    System.setProperty(property, value);
    try {
      return solve(model, "--lcg", "-s");
    } finally {
      System.clearProperty("jacop.lcg.probe");
      System.clearProperty(property);
    }
  }

  private String solve(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = new String[options.length + 1];
    System.arraycopy(options, 0, args, 0, options.length);
    args[options.length] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
