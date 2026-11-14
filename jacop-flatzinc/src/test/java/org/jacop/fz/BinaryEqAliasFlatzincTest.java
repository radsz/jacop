/*
 * BinaryEqAliasFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
 * Checks the alias of a 0..1 integer x channelled to a Boolean b by int_eq_reif(x, 1, b) (flag
 * org.jacop.fz.binaryEqAlias): the solutions stay the same with the default search, all-solutions
 * search and LCG, including an aliased output variable.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class BinaryEqAliasFlatzincTest {

  @TempDir Path tmp;

  // two agents on three cells, a time-expanded grid in miniature: cell indicators as 0..1 integers
  // channelled to Booleans, used in sums
  private static final String MODEL =
      """
      var 1..3: p:: output_var;
      var 1..3: q:: output_var;
      var 0..1: P1:: output_var;
      var 0..1: P2;
      var 0..1: P3;
      var 0..1: Q1;
      var 0..1: Q2;
      var 0..1: Q3;
      var bool: p1;
      var bool: p2;
      var bool: p3;
      var bool: q1;
      var bool: q2;
      var bool: q3;
      var 0..6: cost:: output_var;
      constraint int_eq_reif(p,1,p1);
      constraint int_eq_reif(p,2,p2);
      constraint int_eq_reif(p,3,p3);
      constraint int_eq_reif(q,1,q1);
      constraint int_eq_reif(q,2,q2);
      constraint int_eq_reif(q,3,q3);
      constraint int_eq_reif(P1,1,p1);
      constraint int_eq_reif(P2,1,p2);
      constraint int_eq_reif(P3,1,p3);
      constraint int_eq_reif(Q1,1,q1);
      constraint int_eq_reif(Q2,1,q2);
      constraint int_eq_reif(Q3,1,q3);
      constraint int_lin_le([1,1],[P1,Q1],1);
      constraint int_lin_le([1,1],[P2,Q2],1);
      constraint int_lin_le([1,1],[P3,Q3],1);
      constraint int_lin_le([1,1],[P3,Q2],1);
      constraint int_lin_eq([1,2,3,-1],[P1,P2,Q3,cost],0);
      """;

  @Test
  void aliasKeepsTheSolutions() throws IOException {
    String satisfy = MODEL + "solve satisfy;\n";
    Set<String> reference = solutions(run(false, satisfy, "-a"));
    assertEquals(5, reference.size(), reference.toString());
    String aliased = run(true, satisfy, "-a", "-debug");
    assertTrue(aliased.contains("% Alias: p1::{0..1} == P1::{0..1}"), aliased);
    assertEquals(reference, solutions(aliased));
    assertEquals(reference, solutions(run(true, satisfy, "-a", "--lcg")));
  }

  @Test
  void aliasKeepsTheOptimum() throws IOException {
    String minimize = MODEL + "solve minimize cost;\n";
    String reference = optimum(run(false, minimize));
    assertFalse(reference.isEmpty());
    assertEquals(reference, optimum(run(true, minimize)));
    assertEquals(reference, optimum(run(true, minimize, "--lcg")));
    assertEquals(reference, optimum(run(true, minimize, "--lcg", "-f")));
  }

  private static String optimum(String out) {
    String[] parts = out.split("----------");
    assertTrue(out.contains("=========="), out);
    return Arrays.stream(parts[parts.length - 2].strip().split("\\R"))
        .filter(l -> l.startsWith("cost"))
        .findFirst()
        .orElse("");
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

  private String run(boolean alias, String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty("org.jacop.fz.binaryEqAlias", Boolean.toString(alias));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty("org.jacop.fz.binaryEqAlias");
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
