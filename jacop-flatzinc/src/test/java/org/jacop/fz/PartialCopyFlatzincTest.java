/*
 * PartialCopyFlatzincTest.java
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
import java.util.Arrays;
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the merging of the copies MiniZinc makes of a partial function result (b -&gt; z = x, c
 * -&gt; z = k, not b -&gt; c): the copies with the same x, b and k become one variable and the
 * solutions stay the same.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class PartialCopyFlatzincTest {

  @TempDir Path tmp;

  private static String copy(String z, String c, String x, String b, int k) {
    return "constraint int_eq_imp("
        + z
        + ","
        + x
        + ","
        + b
        + ");\nconstraint int_eq_imp("
        + z
        + ","
        + k
        + ","
        + c
        + ");\nconstraint bool_clause(["
        + c
        + ","
        + b
        + "],[]);\n";
  }

  private static final String MODEL =
      """
      var 1..4: x:: output_var;
      var bool: b:: output_var;
      var 1..4: z1;
      var 1..4: z2;
      var 1..3: z3;
      var 1..4: z4;
      var bool: c1;
      var bool: c2;
      var bool: c3;
      var bool: c4;
      var bool: e1:: output_var;
      var bool: e2:: output_var;
      var bool: e3:: output_var;
      var bool: e4:: output_var;
      constraint int_le_reif(z1,2,e1);
      constraint int_eq_reif(z2,3,e2);
      constraint int_eq_reif(z3,1,e3);
      constraint int_eq_reif(z4,2,e4);
      constraint bool_clause([c4],[]);
      """
          // z1, z2 and z3 are copies of one result (z3 with a smaller domain), z4 has a different
          // default value and its c4 occurs elsewhere
          + copy("z1", "c1", "x", "b", 1)
          + copy("z2", "c2", "x", "b", 1)
          + copy("z3", "c3", "x", "b", 1)
          + copy("z4", "c4", "x", "b", 2)
          + "solve satisfy;\n";

  @Test
  void copiesAreMergedWithTheSameSolutions() throws IOException {
    String merged = run(MODEL, "-a", "-debug");
    assertTrue(merged.contains("partial function copies merged: 2"), merged);
    String separate;
    System.setProperty("org.jacop.fz.partialCopies", "false");
    try {
      separate = run(MODEL, "-a");
    } finally {
      System.clearProperty("org.jacop.fz.partialCopies");
    }
    assertEquals(solutions(separate), solutions(merged));
  }

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    new TreeSet<>(
                        Arrays.stream(s.strip().split("\\R"))
                            .filter(l -> !l.isBlank() && !l.startsWith("%"))
                            .toList())))
        .filter(s -> !s.isEmpty() && !s.startsWith("=========="))
        .forEach(solutions::add);
    return solutions;
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
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
