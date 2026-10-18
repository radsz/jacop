/*
 * FlatzincFrontEndTest.java
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
 * Regression tests for the translation of FlatZinc constraints to JaCoP constraints.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class FlatzincFrontEndTest {

  @TempDir Path tmp;

  @Test
  void boolEqReifWithConstantNextToChanneledIntEqReif() throws IOException {
    // x has two int_eq_reif with constants on its 0/1 view, which are collected into one
    // channeling constraint. bool_eq_reif(x, false, r) was skipped as if it had been collected
    // too, which left r unconstrained.
    String fzn =
        """
        var bool: x:: output_var;
        var 0..1: xi;
        var bool: a;
        var bool: c;
        var bool: r:: output_var;
        constraint bool2int(x,xi);
        constraint int_eq_reif(xi,1,a);
        constraint int_eq_reif(xi,0,c);
        constraint bool_eq_reif(x,false,r);
        solve satisfy;
        """;

    assertEquals(Set.of("r = false; x = true;", "r = true; x = false;"), solveAll(fzn));
  }

  @Test
  void searchOnOutputVariablesAssignsTheOtherVariablesToo() throws IOException {
    // The annotated search labels only x and then the output variables, also only x. For x = 1
    // y, z and w must be pairwise different values in 1..2, which propagation of int_ne does not
    // detect, so x = 1 was reported as a solution without y, z and w having values.
    String fzn =
        """
        var 1..2: x:: output_var;
        var 2..3: x1;
        var 1..3: y;
        var 1..3: z;
        var 1..3: w;
        constraint int_lin_eq([1,-1],[x1,x],1);
        constraint int_le(y,x1);
        constraint int_le(z,x1);
        constraint int_le(w,x1);
        constraint int_ne(y,z);
        constraint int_ne(y,w);
        constraint int_ne(z,w);
        solve :: int_search([x], input_order, indomain_min, complete) satisfy;
        """;

    assertEquals(Set.of("x = 2;"), solveAll(fzn));
  }

  @Test
  void outputFileGetsEverySolutionWhenAllAreRequested() throws IOException {
    // With -a the output file kept only the last solution, so golden files of the MiniZinc
    // based tests could not record all solutions.
    Path fzn = tmp.resolve("all.fzn");
    Path out = tmp.resolve("all.out");
    Files.writeString(fzn, "var 1..3: x:: output_var;\nsolve satisfy;\n", StandardCharsets.UTF_8);
    new Fz2jacop().callMain(new String[] {"-a", "--outputfile", out.toString(), fzn.toString()});

    assertEquals(
        "x = 1;\n----------\nx = 2;\n----------\nx = 3;\n----------\n",
        Files.readString(out, StandardCharsets.UTF_8));
  }

  private Set<String> solveAll(String model) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(new String[] {"-a", fzn.toString()});
    } finally {
      System.setOut(originalOut);
    }
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(buffer.toString(StandardCharsets.UTF_8).split("----------"))
        .map(s -> String.join(" ", new TreeSet<>(Arrays.asList(s.strip().split("\\R")))))
        .filter(s -> !s.isEmpty() && !s.startsWith("=========="))
        .forEach(solutions::add);
    return solutions;
  }
}
