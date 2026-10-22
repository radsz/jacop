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
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
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
  void mddWithRepeatedVariableAndNonDeterministicEdges() throws IOException {
    // jacop_mdd is the native mdd and mdd_nondet. The diagram over [x1, x2, x1] has two edges
    // leaving the root with the value 1, labels given as sets and ranges, and x1 twice, which the
    // front end replaces by a copy. Allowed words: (0,0,0..1), (1,0,0..1), (1,2,0..1), so with the
    // repeated x1 the solutions are x1 = 0, x2 = 0; x1 = 1, x2 = 0 and x1 = 1, x2 = 2.
    String fzn =
        """
        var 0..2: x1:: output_var;
        var 0..2: x2:: output_var;
        constraint jacop_mdd([x1,x2,x1],[1,2,2,3],[1,1,2,3,4],[0..1,{1},{0},{2},0..1],[2,3,4,4,0]);
        solve satisfy;
        """;

    assertEquals(Set.of("x1 = 0; x2 = 0;", "x1 = 1; x2 = 0;", "x1 = 1; x2 = 2;"), solveAll(fzn));
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

  @Test
  void allSolutionsAreReportedOncePerAssignmentOfOutputVariables() throws IOException {
    // The default search labelled every variable, so with -a x = 0 was reported twice: once for
    // each value of b, which x = 0 leaves free and which is not an output variable.
    String fzn =
        """
        var 0..1: x:: output_var;
        var bool: b;
        constraint int_eq_imp(x,0,b);
        solve satisfy;
        """;

    assertEquals(List.of("x = 0;", "x = 1;"), solveAllInOrder(fzn));
  }

  @Test
  void seqSearchOfIgnoredAnnotationsFallsBackToDefaultSearch() throws IOException {
    // A seq_search whose annotations were all ignored had no search, which ended in a
    // NullPointerException, both nested (MiniZinc regression test_bug53) and at the top level.
    String nested =
        """
        var 1..2: x:: output_var;
        solve :: seq_search([seq_search([simpleann,simpleann]),seq_search([simpleann])]) satisfy;
        """;
    String top =
        """
        var 1..2: x:: output_var;
        solve :: seq_search([simpleann]) satisfy;
        """;

    assertEquals(List.of("x = 1;", "x = 2;"), solveAllInOrder(nested));
    assertEquals(List.of("x = 1;", "x = 2;"), solveAllInOrder(top));
  }

  @Test
  void defaultSearchReachesValuesOfUnboundedVariables() throws IOException {
    // MiniZinc test tuple_if_then_else: x and y are unbounded and only x = 3 has a support. The
    // default search tried x = min, x != min one value after another, nesting one choice per
    // value, which overflowed the stack.
    String fzn =
        """
        var bool: b:: output_var;
        var int: x:: output_var;
        var int: y:: output_var;
        var bool: e3;
        var bool: e4;
        var bool: c4;
        var bool: e5;
        var bool: c5;
        constraint jacop_if_then_else_bool([b,true],[c4,c5],true);
        constraint int_eq_reif(x,3,e3);
        constraint int_eq_reif(y,4,e4);
        constraint array_bool_and([e3,e4],c4);
        constraint int_eq_reif(y,5,e5);
        constraint array_bool_and([e3,e5],c5);
        solve satisfy;
        """;

    assertEquals(Set.of("b = true; x = 3; y = 4;", "b = false; x = 3; y = 5;"), solveAll(fzn));
  }

  @Test
  void listDomainsKeepExactlyTheListedValues() throws IOException {
    // Value lists spanning at most 64 values become small dense domains, wider ones stay
    // interval domains; both must hold exactly the listed values, also at the 64 value boundary.
    String fzn =
        """
        var {-3,0,1,2,60}: x:: output_var;
        var {5,68}: y:: output_var;
        var {7,71}: z:: output_var;
        array [1..2] of var {1,5,9}: a:: output_array([1..2]);
        solve satisfy;
        """;

    Set<String> expected = new TreeSet<>();
    for (int x : new int[] {-3, 0, 1, 2, 60}) {
      for (int y : new int[] {5, 68}) {
        for (int z : new int[] {7, 71}) {
          for (int a1 : new int[] {1, 5, 9}) {
            for (int a2 : new int[] {1, 5, 9}) {
              expected.add(
                  String.join(
                      " ",
                      new TreeSet<>(
                          Set.of(
                              "x = " + x + ";",
                              "y = " + y + ";",
                              "z = " + z + ";",
                              "a = array1d(1..2, [" + a1 + ", " + a2 + "]);"))));
            }
          }
        }
      }
    }
    assertEquals(expected, solveAll(fzn));
  }

  @Test
  void strictFloatLinearRejectsASumEqualToTheBound() throws IOException {
    // -0.5 * x < 1 accepted x = -2: the product was rounded outward to [prev(1), next(1)], which
    // the strict check min >= 1 never rejects.
    String fzn =
        """
        var -2..2: i:: output_var;
        var -2.0..2.0: x;
        constraint int2float(i,x);
        constraint float_lin_lt([-0.5],[x],1.0);
        solve satisfy;
        """;
    String reified =
        """
        var -2..2: i:: output_var;
        var bool: b:: output_var;
        var -2.0..2.0: x;
        constraint int2float(i,x);
        constraint float_lin_lt_reif([-0.5],[x],1.0,b);
        solve satisfy;
        """;

    assertEquals(Set.of("i = -1;", "i = 0;", "i = 1;", "i = 2;"), solveAll(fzn));
    assertEquals(
        Set.of(
            "b = false; i = -2;",
            "b = true; i = -1;",
            "b = true; i = 0;",
            "b = true; i = 1;",
            "b = true; i = 2;"),
        solveAll(reified));
  }

  @Test
  void boolClauseWithConstantLiterals() throws IOException {
    // MiniZinc conformance test fcts/builtins/bool/bool_clause.fzn: the clause with true on both
    // sides was taken for a reified one and its missing third argument was read, which ended in an
    // ArrayIndexOutOfBoundsException.
    String fzn =
        """
        var bool: x1 :: output_var;
        var bool: x2 :: output_var;
        constraint bool_clause([true], []);
        constraint bool_clause([], [false]);
        constraint bool_clause([true], [true]);
        constraint bool_clause([true], [false]);
        constraint bool_clause([false], [false]);
        constraint bool_clause([x1], [x2]);
        solve satisfy;
        """;

    assertEquals(
        Set.of("x1 = false; x2 = false;", "x1 = true; x2 = false;", "x1 = true; x2 = true;"),
        solveAll(fzn));
  }

  @Test
  void boolClauseReifiedAndImpliedConstantClauses() throws IOException {
    // An empty clause is false, so its reification and implication variables are false; they
    // were set to true. A clause that always holds leaves the implication variable free; it was
    // set to true. A bool_clause after a bool_clause_imp was treated as an implication too.
    String fzn =
        """
        var bool: r1 :: output_var;
        var bool: r2 :: output_var;
        var bool: r3 :: output_var;
        var bool: r4 :: output_var;
        var bool: x :: output_var;
        constraint bool_clause_reif([], [], r1);
        constraint bool_clause_imp([], [], r2);
        constraint bool_clause_imp([true], [], r3);
        constraint bool_clause_imp([x], [x], r4);
        constraint bool_clause([x], []);
        solve satisfy;
        """;

    assertEquals(
        Set.of(
            "r1 = false; r2 = false; r3 = false; r4 = false; x = true;",
            "r1 = false; r2 = false; r3 = false; r4 = true; x = true;",
            "r1 = false; r2 = false; r3 = true; r4 = false; x = true;",
            "r1 = false; r2 = false; r3 = true; r4 = true; x = true;"),
        solveAll(fzn));
  }

  @Test
  void debugOptionPrintsConstraints() throws IOException {
    // -debug printed the constraints through a logger that has no appender, so only the search
    // was printed.
    String fzn =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
        constraint int_ne(x, y);
        solve satisfy;
        """;

    String stdout = run(fzn, "-debug")[0];
    assertTrue(
        stdout.lines().anyMatch(line -> line.startsWith("% XneqY")),
        "constraints missing from -debug output:\n" + stdout);
  }

  /** Runs the model with the given options and returns its stdout and stderr. */
  private String[] run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ByteArrayOutputStream err = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    PrintStream originalErr = System.err;
    try (PrintStream captureOut = new PrintStream(out, true, StandardCharsets.UTF_8);
        PrintStream captureErr = new PrintStream(err, true, StandardCharsets.UTF_8)) {
      System.setOut(captureOut);
      System.setErr(captureErr);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.setErr(originalErr);
    }
    return new String[] {
      out.toString(StandardCharsets.UTF_8), err.toString(StandardCharsets.UTF_8)
    };
  }

  private Set<String> solveAll(String model) throws IOException {
    return new TreeSet<>(solveAllInOrder(model));
  }

  private List<String> solveAllInOrder(String model) throws IOException {
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
    return Arrays.stream(buffer.toString(StandardCharsets.UTF_8).split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    Arrays.stream(s.strip().split("\\R"))
                        .filter(line -> !line.startsWith("%"))
                        .collect(Collectors.toCollection(TreeSet::new))))
        .filter(s -> !s.isEmpty() && !s.startsWith("=========="))
        .toList();
  }
}
