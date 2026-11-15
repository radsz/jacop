/*
 * FloatOptimizationFlatzincTest.java
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
import java.io.InputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Float objectives solved to optimality: by bisection of the objective (branch and bound improved
 * the 3-variable linear program mip1 by a few ulps per solution, 16 million solutions in 60 s),
 * with the safe linear relaxation of the float rows and products (Ibex's ex2_1_1, a concave
 * quadratic program) and its point probe (Ibex's ex2_1_10, whose search found nothing better than
 * 547,663 against the optimum 49,318). Each model timed out before.
 */
class FloatOptimizationFlatzincTest {

  @TempDir Path tmp;

  @Test
  void bisectionProvesTheLinearProgramMip1() throws IOException {
    String out = solve("mip1.fzn");
    assertTrue(out.contains("=========="), out);
    // maximise C + 3B + 3D
    double b = value(out, "B");
    double c = value(out, "C");
    double d = value(out, "D");
    assertEquals(39.0, c + 3 * b + 3 * d, 1e-6, out);
  }

  @Test
  void relaxationProvesTheConcaveProgramEx211() throws IOException {
    String out = solve("ex2_1_1.fzn");
    assertTrue(out.contains("=========="), out);
    assertEquals(-17.0, value(out, "objective"), 1e-3, out);
  }

  @Test
  void pointProbeFindsTheOptimumOfEx2110() throws IOException {
    // under free search: the annotated input_order split proves it too, in about 70 s
    String out = solve("ex2_1_10.fzn", "-f");
    assertTrue(out.contains("=========="), out);
    // Ibex 2.8.9: f* in [49317.9686, 49318.0180]; the optimum is proved to a relative 1e-6
    assertEquals(49318.0, value(out, "objective"), 0.1, out);
  }

  private static double value(String out, String name) {
    Matcher m = Pattern.compile("(?m)^" + name + " = ([-0-9.eE]+);").matcher(out);
    double v = Double.NaN;
    while (m.find()) {
      v = Double.parseDouble(m.group(1));
    }
    return v;
  }

  private String solve(String name, String... options) throws IOException {
    Path fzn = tmp.resolve(name);
    try (InputStream in = getClass().getResourceAsStream("floats/" + name)) {
      Files.copy(in, fzn);
    }
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      String[] args = new String[options.length + 3];
      System.arraycopy(options, 0, args, 0, options.length);
      args[options.length] = "-t";
      args[options.length + 1] = "30000";
      args[options.length + 2] = fzn.toString();
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
