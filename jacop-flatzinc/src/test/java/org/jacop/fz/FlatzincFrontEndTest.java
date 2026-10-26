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
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
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
  void valuePrecedeChainIsDomainConsistentForTheWholeChain() throws IOException {
    // Walsh's example with values 5, 3, 8, 9: each pair of consecutive values is consistent but
    // the chain forbids x2 = 5. Pairwise ValuePrecede needed a failed decision to find it.
    String fzn =
        """
        var 5..5: x1;
        var {3,5}: x2:: output_var;
        var {5,8}: x3;
        var {8,9}: x4;
        constraint jacop_value_precede_chain_int([5,3,8,9],[x1,x2,x3,x4,x2]);
        solve :: int_search([x2],input_order,indomain_max,complete) satisfy;
        """;

    String out = run(fzn, "-s")[0];
    assertTrue(out.contains("x2 = 3;"), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
  }

  @Test
  void reifiedAllEqualOfThreeFindsNoCommonValueWithoutSearch() throws IOException {
    // x1 and x3 have no common value, so b must be false before any search. Three variables
    // were posted as b <-> (x1 = x2 /\ x2 = x3), which only looks at neighbouring pairs and
    // needed a failed decision b = true.
    String fzn =
        """
        var 1..1: x1;
        var 1..2: x2;
        var 2..2: x3;
        var bool: b:: output_var;
        constraint jacop_all_equal_int_reif([x1,x2,x3],b);
        solve :: bool_search([b],input_order,indomain_max,complete) satisfy;
        """;

    String out = run(fzn, "-s")[0];
    assertTrue(out.contains("b = false;"), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
  }

  @Test
  void strictlyIncreasingOfARepeatedVariableIsUnsatisfiable() throws IOException {
    // strictly_increasing([x, x]) was posted as XltY(x, x), which throws, so the model was
    // reported as an error instead of unsatisfiable
    String fzn =
        """
        var 1..3: x:: output_var;
        constraint jacop_strictly_increasing([x,x]);
        solve satisfy;
        """;

    String[] out = run(fzn);
    assertTrue(out[0].contains("=====UNSATISFIABLE====="), out[0] + out[1]);

    String nonStrict =
        """
        var 1..3: x:: output_var;
        constraint jacop_decreasing([x,x]);
        solve satisfy;
        """;
    assertEquals(Set.of("x = 1;", "x = 2;", "x = 3;"), solveAll(nonStrict));
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
  void invalidModelReportsErrorOnStderrOnly() throws IOException {
    // MiniZinc's *-bad tests expect no output and an error message; the message of the Java
    // exception, with its class name, was printed to stdout.
    String fzn =
        """
        array [1..3] of int: a = [1,2,3,4];
        var 1..3: x :: output_var;
        solve satisfy;
        """;

    String[] out = run(fzn);
    assertEquals("", out[0]);
    assertEquals(
        "%% Error: Different size declaration and initialization of int array;"
            + " compilation aborted.",
        out[1].strip());
  }

  @Test
  void allSolutionsOptionPrintsImprovingSolutionsOfRestartSearch() throws IOException {
    // For optimization -a asks for the intermediate solutions; it was rejected together with
    // restart search, where it is only meaningless for satisfaction problems.
    String model =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
        constraint int_ne(x, y);
        solve :: int_search([x,y],input_order,indomain_min,complete) :: restart_constant(10) %s;
        """;

    assertEquals(
        List.of("x = 1; y = 2;", "x = 2; y = 1;", "x = 3; y = 1;"),
        solveAllInOrder(model.formatted("maximize x")));

    String[] out = run(model.formatted("satisfy"), "-a");
    assertEquals("", out[0]);
    assertTrue(out[1].contains("cannot be used in restart search of a satisfaction problem"));
  }

  @Test
  void allSolutionsSearchStoppedByTimeOutIsNotReportedComplete() throws IOException {
    // An all-solutions satisfaction search that hit the time limit after finding solutions
    // printed ========== as if all 13! circuits had been enumerated.
    String model =
        """
        array [1..14] of var 1..14: x;
        constraint jacop_circuit(x);
        solve :: int_search(x,input_order,indomain_min,complete) satisfy;
        """;
    String out = run(model, "-a", "-t", "100")[0];
    assertTrue(out.contains("----------"), out.lines().limit(5).toList().toString());
    assertTrue(!out.contains("=========="), "search reported complete after a time-out");
    assertTrue(out.contains("=====TIME-OUT====="), "no time-out reported");
  }

  @Test
  void circuitPostsAlldistinctUnderDomainAnnotation() throws IOException {
    // x1 and x2 take 3 and 4 between them (a Hall set), so x5 cannot be 3 or 4. Circuit alone
    // propagates all-different on fixed values only and needs two failed decisions on x5; the
    // Alldistinct posted with it under ::domain removes them at the root.
    String fzn =
        """
        var {3,4}: x1:: output_var;
        var {3,4}: x2:: output_var;
        var {1,2,4,5}: x3:: output_var;
        var {1,2,3,5}: x4:: output_var;
        var {1,2,3,4}: x5:: output_var;
        array [1..5] of var int: x = [x1,x2,x3,x4,x5];
        constraint jacop_circuit(x)%s;
        solve :: int_search([x5,x4,x3,x2,x1],input_order,indomain_max,complete) satisfy;
        """;

    String domain = run(fzn.formatted(" :: domain"), "-s")[0];
    assertTrue(domain.contains("x5 = 2;"), domain);
    assertTrue(domain.contains("%%%mzn-stat: failures=0"), domain);
    // a circuit of 5 nodes gets no Alldistinct by default
    String plain = run(fzn.formatted(""), "-s")[0];
    assertTrue(plain.contains("x5 = 2;"), plain);
    assertTrue(plain.contains("%%%mzn-stat: failures=2"), plain);
  }

  @Test
  void circuitPostsAlldistinctByDefaultFromThirtyNodes() throws IOException {
    // The Hall set {x1, x2} on {3, 4} in a circuit of 30 nodes, 30 -> 2 -> 4 -> 5 -> ... -> 29
    // -> 1 -> 3 -> 30: the Alldistinct posted by default removes 3 and 4 from x30 at the root.
    // Option -b leaves it out.
    String fzn = hallSetSuccessors(30) + "constraint jacop_circuit(x);\n" + hallSetSearch(30);

    String out = run(fzn, "-s")[0];
    assertTrue(out.contains("x30 = 2;"), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
    String bounds = run(fzn, "-s", "-b")[0];
    assertTrue(bounds.contains("x30 = 2;"), bounds);
    assertTrue(bounds.contains("%%%mzn-stat: failures=2"), bounds);
  }

  @Test
  void subcircuitPostsAlldistinctByDefaultFromThirtyNodes() throws IOException {
    // The same Hall set: Subcircuit alone tries x30 = 4 and x30 = 3 first.
    String fzn = hallSetSuccessors(30) + "constraint jacop_subcircuit(x);\n" + hallSetSearch(30);

    String out = run(fzn, "-s")[0];
    assertTrue(out.contains("x30 = 2;"), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
    String bounds = run(fzn, "-s", "-b")[0];
    assertTrue(bounds.contains("x30 = 2;"), bounds);
    assertTrue(!bounds.contains("%%%mzn-stat: failures=0"), bounds);
  }

  /** Successors of n nodes with the Hall set {x1, x2} on {3, 4} and x_n in 1..4. */
  private static String hallSetSuccessors(int n) {
    StringBuilder fzn = new StringBuilder();
    fzn.append("var {3,4}: x1:: output_var;\n").append("var {3,4}: x2:: output_var;\n");
    fzn.append("var {5,").append(n).append("}: x3:: output_var;\n");
    for (int i = 4; i < n; i++) {
      fzn.append("var {1,").append(i + 1).append("}: x").append(i).append(":: output_var;\n");
    }
    fzn.append("var 1..4: x").append(n).append(":: output_var;\n");
    fzn.append("array [1..").append(n).append("] of var int: x = [");
    for (int i = 1; i <= n; i++) {
      fzn.append(i > 1 ? "," : "").append('x').append(i);
    }
    return fzn.append("];\n").toString();
  }

  /** Search on x_n first, largest value first. */
  private static String hallSetSearch(int n) {
    StringBuilder order = new StringBuilder();
    for (int i = n; i >= 1; i--) {
      order.append(i < n ? "," : "").append('x').append(i);
    }
    return "solve :: int_search([" + order + "],input_order,indomain_max,complete) satisfy;\n";
  }

  @Test
  void sequenceSearchStatisticsCountReportedSolutions() throws IOException {
    // Each search of a seq_search counted the solutions of its own phase and the statistics
    // summed them: 4 solutions were reported as solutions=22.
    String model =
        """
        array [1..2] of var 1..2: x;
        array [1..2] of var bool: b;
        constraint int_ne(x[1],x[2]);
        constraint bool_xor(b[1],b[2],true);
        solve :: seq_search([int_search(x,input_order,indomain_min,complete),bool_search(b,input_order,indomain_min,complete)]) satisfy;
        """;
    String out = run(model, "-a", "-s")[0];
    assertEquals(4, out.lines().filter(l -> l.equals("----------")).count(), out);
    assertTrue(out.contains("%%%mzn-stat: solutions=4\n"), out);
  }

  @Test
  void restartSearchFindsTheOptimumAfterRestartsWithoutABetterSolution() throws IOException {
    // Restart search stopped after the first restart that found no better solution and printed
    // ========== for the last solution (c = 1 here) as if it were optimal.
    String model =
        """
        array [1..6] of var 1..6: x :: output_array([1..6]);
        var -100..100: c :: output_var;
        constraint int_ne(x[1], x[2]);
        constraint int_ne(x[1], x[3]);
        constraint int_ne(x[2], x[3]);
        constraint int_ne(x[3], x[4]);
        constraint int_ne(x[4], x[5]);
        constraint int_ne(x[5], x[6]);
        constraint int_ne(x[4], x[6]);
        constraint int_ne(x[1], x[6]);
        constraint int_lin_eq([-3,2,-1,4,-2,1,-1],[x[1],x[2],x[3],x[4],x[5],x[6],c],0);
        solve :: int_search(x,input_order,indomain_min,complete) :: %s minimize c;
        """;

    for (String restart : List.of("restart_luby(1)", "restart_geometric(1.5,1)")) {
      List<String> lines = run(model.formatted(restart))[0].lines().toList();
      assertTrue(lines.contains("c = -27;"), restart + ":\n" + lines);
      assertTrue(lines.contains("=========="), restart + ":\n" + lines);
    }

    // With a limit on the number of restarts the search is not complete.
    String limited = run(model.formatted("restart_luby(1)"), "--restart-limit", "1")[0];
    assertTrue(limited.contains("----------"), limited);
    assertTrue(!limited.contains("=========="), limited);
  }

  @Test
  void relaxAndReconstructPrintsImprovingSolutionsAndAProvedOptimum() throws IOException {
    // Relaxed runs lost the bound on the cost and printed worse solutions, and the end of the
    // search was never reported, even when a run that fixed no variable had explored everything.
    String model =
        """
        array [1..6] of var 1..6: x :: output_array([1..6]);
        var -100..100: c :: output_var;
        constraint int_ne(x[1], x[2]);
        constraint int_ne(x[1], x[3]);
        constraint int_ne(x[2], x[3]);
        constraint int_ne(x[3], x[4]);
        constraint int_ne(x[4], x[5]);
        constraint int_ne(x[5], x[6]);
        constraint int_ne(x[4], x[6]);
        constraint int_ne(x[1], x[6]);
        constraint int_lin_eq([-3,2,-1,4,-2,1,-1],[x[1],x[2],x[3],x[4],x[5],x[6],c],0);
        solve :: int_search(x,input_order,indomain_min,complete)
          :: restart_geometric(1.5,1) :: relax_and_reconstruct(x, 50) minimize c;
        """;

    for (String seed : List.of("1", "2", "3")) {
      List<String> lines = run(model, "-a", "-r", seed)[0].lines().toList();
      List<Integer> costs =
          lines.stream()
              .filter(l -> l.startsWith("c = "))
              .map(l -> Integer.parseInt(l.substring(4, l.length() - 1)))
              .toList();
      for (int i = 1; i < costs.size(); i++) {
        assertTrue(costs.get(i) < costs.get(i - 1), "seed " + seed + ": " + costs);
      }
      assertEquals(-27, costs.getLast(), "seed " + seed + ":\n" + lines);
      assertTrue(lines.contains("=========="), "seed " + seed + ":\n" + lines);
    }
  }

  private static List<Integer> distances(String stdout) {
    return stdout
        .lines()
        .filter(l -> l.startsWith("distance = "))
        .map(l -> Integer.parseInt(l.substring(11, l.length() - 1)))
        .toList();
  }

  private static String annotationModel(String name) throws IOException {
    return Files.readString(Path.of("src/test/fz/annotations", name + ".fzn"));
  }

  @Test
  void relaxAndReconstructTspKeepsImproving() throws IOException {
    // tsp-relax (16 cities, relax_and_reconstruct(d, 60), restart_luby(3000)) improved to 6875 and
    // then printed worse and worse tours, up to 9257, because the bound on the distance was lost
    // after the first relaxed restart. The optimum is 6859 (proved by tsp-restart and by Gecode).
    String model = annotationModel("tsp-relax");
    for (String seed : List.of("1", "4")) {
      String out = run(model, "-a", "-r", seed, "--restart-limit", "1200")[0];
      List<Integer> distances = distances(out);
      for (int i = 1; i < distances.size(); i++) {
        assertTrue(distances.get(i) < distances.get(i - 1), "seed " + seed + ": " + distances);
      }
      assertEquals(6859, distances.getLast(), "seed " + seed + ": " + distances);
    }
  }

  @Test
  void restartAndWarmStartAnnotationModels() throws IOException {
    for (String name : List.of("tsp-restart", "tsp-warm-restart")) {
      String out = run(annotationModel(name), "-a")[0];
      List<Integer> distances = distances(out);
      for (int i = 1; i < distances.size(); i++) {
        assertTrue(distances.get(i) < distances.get(i - 1), name + ": " + distances);
      }
      assertEquals(6859, distances.getLast(), name + ": " + distances);
      assertTrue(out.contains("=========="), name + ":\n" + out);
    }
    // warm_start puts its values first: all six permutations, starting with [3,2,1]
    List<String> warm =
        run(annotationModel("warm"), "-a")[0].lines().filter(l -> l.startsWith("x = ")).toList();
    assertEquals(6, new TreeSet<>(warm).size(), warm.toString());
    assertEquals(6, warm.size(), warm.toString());
    assertTrue(warm.getFirst().contains("[3, 2, 1]"), warm.toString());
  }

  @Test
  void restartSearchReportsUnsatisfiableModels() throws IOException {
    // Restart search printed ========== without any solution for an unsatisfiable optimization
    // model, and nothing at all for an unsatisfiable satisfaction model.
    String model =
        """
        array [1..4] of var 1..3: x :: output_array([1..4]);
        var 0..20: c :: output_var;
        constraint int_ne(x[1], x[2]);
        constraint int_ne(x[1], x[3]);
        constraint int_ne(x[1], x[4]);
        constraint int_ne(x[2], x[3]);
        constraint int_ne(x[2], x[4]);
        constraint int_ne(x[3], x[4]);
        constraint int_lin_eq([1,1,1,1,-1],[x[1],x[2],x[3],x[4],c],0);
        solve :: int_search(x,input_order,indomain_min,complete) :: restart_luby(1) %s;
        """;

    for (String kind : List.of("minimize c", "satisfy")) {
      String stdout = run(model.formatted(kind))[0];
      assertEquals(List.of("=====UNSATISFIABLE====="), stdout.lines().toList(), kind);
    }
  }

  @Test
  void memberOfEmptyBoolArrayIsUnsatisfiable() throws IOException {
    // member on an empty array restricted y to an empty domain. For a 0/1 variable that threw a
    // NullPointerException in BoundDomain.in instead of failing.
    String fzn =
        """
        var bool: y :: output_var;
        var 0..1: yi;
        constraint jacop_member_bool([],yi);
        constraint bool2int(y,yi);
        solve satisfy;
        """;

    String stdout = run(fzn)[0];
    assertTrue(stdout.contains("=====UNSATISFIABLE====="), stdout);
  }

  @Test
  void inverseWithIndexSetsOfDifferentSizeIsUnsatisfiable() throws IOException {
    // jacop_assignment with arrays of different length threw ArrayIndexOutOfBoundsException when
    // posting (invf shorter) or NullPointerException during propagation (invf longer).
    String model =
        """
        array [1..%d] of var 1..%d: f :: output_array([1..%1$d]);
        array [1..%2$d] of var 1..%1$d: g :: output_array([1..%2$d]);
        constraint jacop_assignment(f,g,1,1);
        solve satisfy;
        """;
    for (int[] size : new int[][] {{2, 3}, {3, 2}}) {
      String[] out = run(model.formatted(size[0], size[1]), "-a");
      List<String> lines = out[0].lines().filter(l -> !l.startsWith("%%")).toList();
      assertEquals(List.of("=====UNSATISFIABLE====="), lines, out[0] + out[1]);
    }
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

  @Test
  void freeSearchIgnoresSeveralSearchAnnotations() throws IOException {
    // With two or more search annotations -f followed them instead of using free search.
    String fzn =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
        constraint int_ne(x, y);
        solve :: int_search([x], input_order, indomain_max, complete)
              :: int_search([y], input_order, indomain_max, complete) satisfy;
        """;

    assertEquals("x = 3;\ny = 2;", solutionLines(run(fzn)[0]));
    assertEquals("x = 1;\ny = 2;", solutionLines(run(fzn, "-f", "--free-engine", "legacy")[0]));
    // the new engine follows the annotations only on the runs it interleaves them on
    assertEquals(
        "x = 1;\ny = 2;", solutionLines(run(fzn, "-f", "--free-config", "interleave=none")[0]));
  }

  @Test
  void freeSearchReportsAllSolutionsOncePerAssignmentOfOutputVariables() throws IOException {
    // Free search labelled every variable, so with -a x = 0 was reported once for each value of
    // b, which x = 0 leaves free and which is not an output variable, and the set s, which is not
    // an output variable either, gave every solution again for each of its values.
    String fzn =
        """
        var 0..1: x:: output_var;
        var bool: b;
        var set of 1..2: s;
        constraint int_eq_imp(x,0,b);
        solve satisfy;
        """;

    String stdout = run(fzn, "-f", "-a")[0];
    List<String> solutions =
        Arrays.stream(stdout.split("----------\\R"))
            .map(FlatzincFrontEndTest::solutionLines)
            .filter(b -> !b.isBlank())
            .sorted()
            .toList();
    assertEquals(List.of("x = 0;", "x = 1;"), solutions, stdout);
    assertTrue(stdout.contains("=========="), stdout);
  }

  @Test
  void newFreeSearchEngineGivesTheResultsOfTheLegacyOne() throws IOException {
    String[] models = {
      // satisfaction with integers and Booleans
      """
      var 1..4: x :: output_var;
      var 1..4: y :: output_var;
      var bool: b :: output_var;
      constraint int_ne(x, y);
      constraint int_le_reif(x, y, b);
      constraint int_lin_le([1, 1], [x, y], 6);
      solve satisfy;
      """,
      // optimisation
      """
      var 1..4: x :: output_var;
      var 1..4: y :: output_var;
      var bool: b :: output_var;
      var -20..20: c :: output_var;
      constraint int_ne(x, y);
      constraint int_le_reif(x, y, b);
      constraint int_lin_eq([3, -2, 5, -1], [x, y, b, c], 0);
      solve minimize c;
      """,
      """
      var 1..4: x :: output_var;
      var 1..4: y :: output_var;
      constraint int_lin_le([1, 1], [x, y], 6);
      solve maximize x;
      """,
      // no solution
      """
      var 1..2: x :: output_var;
      var 1..2: y :: output_var;
      var 1..2: z :: output_var;
      constraint int_ne(x, y);
      constraint int_ne(y, z);
      constraint int_ne(x, z);
      solve satisfy;
      """,
      // annotated searches, interleaved with free search
      """
      var 1..4: x :: output_var;
      var 1..4: y :: output_var;
      var bool: b :: output_var;
      var -20..20: c :: output_var;
      constraint int_ne(x, y);
      constraint int_le_reif(x, y, b);
      constraint int_lin_eq([3, -2, 5, -1], [x, y, b, c], 0);
      solve :: int_search([y, x], input_order, indomain_max, complete) maximize c;
      """,
      """
      var 1..4: x :: output_var;
      var 1..4: y :: output_var;
      var bool: b :: output_var;
      constraint int_ne(x, y);
      constraint int_le_reif(x, y, b);
      solve :: seq_search([bool_search([b], input_order, indomain_max, complete),
                           int_search([y], input_order, indomain_max, complete)]) satisfy;
      """,
      // sets
      """
      var set of 1..3: s :: output_var;
      var 1..3: x :: output_var;
      constraint set_card(s, 2);
      constraint set_in(x, s);
      solve satisfy;
      """
    };
    String[][] engines = {
      {"--free-engine", "new"},
      {"--free-engine", "new", "--restart", "luby", "--restart-scale", "1"},
      {"--free-engine", "new", "--restart-scale", "1", "--free-config", "interleave=solution"},
      {
        "--free-engine",
        "new",
        "--free-config",
        "heuristic=afc,lc=0,phase=0,restarts=none,interleave=none"
      }
    };
    for (String model : models) {
      boolean optimisation = model.contains("minimize") || model.contains("maximize");
      String legacy =
          normalised(run(model, "-f", "--free-engine", "legacy", "-a")[0], optimisation);
      for (String[] engine : engines) {
        String[] options = Arrays.copyOf(new String[] {"-f", "-a"}, 2 + engine.length);
        System.arraycopy(engine, 0, options, 2, engine.length);
        assertEquals(
            legacy,
            normalised(run(model, options)[0], optimisation),
            model + Arrays.toString(engine));
      }
    }
  }

  /** The solution lines of an output, without comments. */
  private static String solutionLines(String stdout) {
    return stdout
        .lines()
        .filter(line -> !line.startsWith("%") && !line.startsWith("-") && !line.startsWith("="))
        .collect(Collectors.joining("\n"));
  }

  /**
   * An output reduced to what free search engines must agree on: for satisfaction the set of
   * solutions, for optimisation the last one, and the final status lines.
   */
  private static String normalised(String stdout, boolean optimisation) {
    List<String> blocks =
        Arrays.stream(stdout.split("----------\\R"))
            .map(b -> b.lines().filter(l -> !l.startsWith("%")).collect(Collectors.joining(" ")))
            .filter(b -> !b.isBlank())
            .toList();
    List<String> solutions = blocks.stream().filter(b -> !b.startsWith("=")).toList();
    String status = blocks.stream().filter(b -> b.startsWith("=")).collect(Collectors.joining());
    return (optimisation ? solutions.getLast() : new TreeSet<>(solutions).toString())
        + " "
        + status;
  }

  private static final String PRIORITY_WITH_SEQ_SEARCH_ROW =
      """
      var 1..2: a:: output_var;
      var 1..2: b:: output_var;
      var 1..2: c:: output_var;
      solve :: priority_search([c,a],[int_search([c],input_order,indomain_min,complete),\
      seq_search([int_search([a],input_order,indomain_max,complete),\
      int_search([b],input_order,indomain_min,complete)])],input_order,complete) satisfy;
      """;

  @Test
  void seqSearchInPrioritySearchKeepsTheHeuristicsOfItsSearches() throws IOException {
    // The first search of a seq_search under priority_search got the heuristic of the last one, so
    // b was labelled first and a was left to the completion search (indomain_min).
    assertEquals(
        List.of(
            "a = 2; b = 1; c = 1;",
            "a = 2; b = 2; c = 1;",
            "a = 1; b = 1; c = 1;",
            "a = 1; b = 2; c = 1;",
            "a = 2; b = 1; c = 2;",
            "a = 2; b = 2; c = 2;",
            "a = 1; b = 1; c = 2;",
            "a = 1; b = 2; c = 2;"),
        solveAllInOrder(PRIORITY_WITH_SEQ_SEARCH_ROW));
  }

  @Test
  void prioritySearchStopsAtTheRequestedNumberOfSolutions() throws IOException {
    // The priority search stopped at its own count of solutions, taken from the listeners of its
    // child searches, which count each other's solutions: -n 3 stopped after 2 solutions and
    // reported the search complete.
    String out = run(PRIORITY_WITH_SEQ_SEARCH_ROW, "-n", "3")[0];
    assertEquals(3, out.split("----------", -1).length - 1, out);
    assertTrue(!out.contains("=========="), out);
  }

  @Test
  void prioritySearchSkipsASearchWithNoVariables() throws IOException {
    // An empty search was dropped from the list of searches, so the priority variables and the
    // searches no longer matched and the solver stopped with a RuntimeException.
    String fzn =
        """
        var 1..2: a:: output_var;
        var 1..2: b:: output_var;
        solve :: priority_search([a,b],[int_search([],input_order,indomain_min,complete),\
        int_search([b],input_order,indomain_max,complete)],input_order,complete) satisfy;
        """;

    assertEquals(
        List.of("a = 1; b = 2;", "a = 2; b = 2;", "a = 1; b = 1;", "a = 2; b = 1;"),
        solveAllInOrder(fzn));
  }

  @Test
  void prioritySearchBreaksTiesWithTheTieBreakingMetric() throws IOException {
    // most_constrained: smallest domain, ties broken by the larger number of constraints. The tie
    // was decided by comparing the domain size of p1 (2) with the constraint count of p2 (3), so
    // p2 was searched first although p1 has 4 constraints.
    String fzn =
        """
        var 0..1: p1:: output_var;
        var 0..1: p2:: output_var;
        var 0..9: y1;
        var 0..9: y2;
        var 0..9: y3;
        var 0..9: y4;
        constraint int_ne(y1,p1);
        constraint int_ne(y2,p1);
        constraint int_ne(y3,p1);
        constraint int_ne(y4,p1);
        constraint int_ne(y1,p2);
        constraint int_ne(y2,p2);
        constraint int_ne(y3,p2);
        solve :: priority_search([p1,p2],[int_search([p1],input_order,indomain_min,complete),\
        int_search([p2],input_order,indomain_min,complete)],most_constrained,complete) satisfy;
        """;

    assertEquals(
        List.of("p1 = 0; p2 = 0;", "p1 = 0; p2 = 1;", "p1 = 1; p2 = 0;", "p1 = 1; p2 = 1;"),
        solveAllInOrder(fzn));
  }

  @Test
  void maxRegretRanksAFixedPriorityVariableLast() throws IOException {
    // A fixed variable has no second value; its regret was computed against MAX_INT, so the
    // priority search chose the row of the constant 2 before the row of a (regret 2), unlike
    // Chuffed, which gives a fixed variable regret 0.
    String fzn =
        """
        var {1,3}: a:: output_var;
        var 1..2: b:: output_var;
        solve :: priority_search([2,a],[int_search([b],input_order,indomain_min,complete),\
        int_search([a],input_order,indomain_min,complete)],max_regret,complete) satisfy;
        """;

    assertEquals(
        List.of("a = 1; b = 1;", "a = 1; b = 2;", "a = 3; b = 1;", "a = 3; b = 2;"),
        solveAllInOrder(fzn));
  }

  /** Runs the model with the given options and returns its stdout and stderr. */
  @Test
  void warmStartOnFloatAndSetVariablesIsIgnored() throws IOException {
    // a hint is only a preference, but float and set hints aborted the run (float values) or
    // crashed the parser (set values)
    String sets =
        """
        var set of 1..4: s:: output_var;
        var 1..4: y:: output_var;
        array [1..1] of var set of int: hs = [s];
        constraint set_card(s,y);
        constraint set_in(y,s);
        solve %s satisfy;
        """;
    Set<String> noHint = solveAll(sets.formatted(""));
    assertEquals(8, noHint.size());
    assertEquals(noHint, solveAll(sets.formatted(":: warm_start(hs,[{1,3}])")));

    String floats =
        """
        var 0.0..10.0: f:: output_var;
        var 2..5: y:: output_var;
        var 2.0..5.0: yf;
        array [1..1] of var float: hf = [f];
        array [1..1] of var int: hy = [y];
        constraint float_lin_le([-1.0,1.0],[f,yf],-0.5);
        constraint int2float(y,yf);
        solve :: warm_start(hy,[4]) :: warm_start(hf,[3.0]) minimize f;
        """;
    String[] out = run(floats);
    assertTrue(out[0].contains("y = 2;") && out[0].contains("=========="), out[0] + out[1]);
  }

  @Test
  void emptyWarmStartIsIgnored() throws IOException {
    // warm_start(x, [<>, <>, <>]) is flattened to warm_start([], []), which crashed the parser
    String fzn =
        """
        var 1..3: x:: output_var;
        var 1..3: y:: output_var;
        constraint int_ne(x,y);
        solve %s satisfy;
        """;
    assertEquals(solveAll(fzn.formatted("")), solveAll(fzn.formatted(":: warm_start([],[])")));
  }

  @Test
  void warmStartWithMoreValuesThanVariablesUsesTheCommonPart() throws IOException {
    // the values were read up to their own length, past the end of the variables
    String fzn =
        """
        var 1..3: x:: output_var;
        var 1..3: y:: output_var;
        constraint int_ne(x,y);
        solve :: warm_start([x],[2,3]) satisfy;
        """;
    String out = run(fzn)[0];
    assertTrue(out.contains("x = 2;"), out);
    assertEquals(6, solveAll(fzn).size());
  }

  @Test
  void warmStartArrayIsUsed() throws IOException {
    // warm_start_array, which MiniZinc makes for a set hint without set support and which users
    // write to group hints, was ignored
    String fzn =
        """
        var 1..3: x:: output_var;
        var 1..3: y:: output_var;
        var bool: b:: output_var;
        constraint int_ne(x,y);
        constraint int_eq_imp(x,3,b);
        solve %s satisfy;
        """;
    String hint =
        ":: warm_start_array([warm_start([x,y],[3,1]),warm_start_array([warm_start([b],[true])])])";
    String out = run(fzn.formatted(hint))[0];
    assertTrue(out.contains("x = 3;") && out.contains("y = 1;") && out.contains("b = true;"), out);
    assertEquals(solveAll(fzn.formatted("")), solveAll(fzn.formatted(hint)));
  }

  @Test
  void warmStartInSequenceSearchStopsAtTheTimeLimit() {
    // a warm_start inside seq_search (or next to another search annotation) was not in the list of
    // searches that get the time limit, so a long search under it ignored -t; 13 pigeons in 12
    // holes take hours without the limit
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < 13; i++) {
      fzn.append("var 1..12: x").append(i).append(";\n");
    }
    StringBuilder vars = new StringBuilder();
    StringBuilder hint = new StringBuilder();
    for (int i = 0; i < 13; i++) {
      vars.append(i == 0 ? "" : ",").append("x").append(i);
      hint.append(i == 0 ? "" : ",").append(i % 12 + 1);
    }
    fzn.append("array [1..13] of var int: x = [").append(vars).append("];\n");
    for (int i = 0; i < 13; i++) {
      for (int j = i + 1; j < 13; j++) {
        fzn.append("constraint int_ne(x").append(i).append(",x").append(j).append(");\n");
      }
    }
    fzn.append("solve :: seq_search([warm_start(x,[")
        .append(hint)
        .append("]),int_search(x,input_order,indomain_min,complete)]) satisfy;\n");

    // the disequalities would become an all-different, which proves at once that the pigeons do
    // not fit
    System.setProperty("org.jacop.fz.alldifferent", "false");
    try {
      String out =
          assertTimeoutPreemptively(Duration.ofSeconds(60), () -> run(fzn.toString(), "-t", "500"))[
              0];
      assertTrue(out.contains("=====UNKNOWN====="), out);
    } finally {
      System.clearProperty("org.jacop.fz.alldifferent");
    }
  }

  @Test
  void intComparisonWithConstantAndFixedBooleanKeepsExactlyTheSolutions() throws IOException {
    // int_ne_reif(x, c, false) left x unconstrained instead of fixing it to c, and the half-reified
    // comparisons with the constant first (int_eq_imp(c, x, b), int_lt_imp(c, x, b), ...) set b
    // when the comparison held or removed x = c when b was false, which loses solutions.
    // Every comparison, argument order, Boolean (false, true, free) and domain is checked
    // against enumeration.
    String[] ops = {"eq", "ne", "lt", "le"};
    int c = 2;
    int[][] domains = {{0, 3}, {2, 2}, {0, 1}, {3, 5}, {1, 2}, {2, 3}};
    for (String op : ops) {
      for (String kind : new String[] {"reif", "imp"}) {
        for (boolean constantFirst : new boolean[] {false, true}) {
          for (String b : new String[] {"false", "true", "free"}) {
            for (int[] d : domains) {
              String args = constantFirst ? c + ",x" : "x," + c;
              String fzn =
                  "var "
                      + d[0]
                      + ".."
                      + d[1]
                      + ": x:: output_var;\n"
                      + ("free".equals(b)
                          ? "var bool: b:: output_var;\n"
                          : "var bool: b = " + b + ";\n")
                      + "constraint int_"
                      + op
                      + "_"
                      + kind
                      + "("
                      + args
                      + ",b);\nsolve satisfy;\n";
              Set<String> expected = new TreeSet<>();
              for (int x = d[0]; x <= d[1]; x++) {
                int l = constantFirst ? c : x;
                int r = constantFirst ? x : c;
                boolean holds =
                    switch (op) {
                      case "eq" -> l == r;
                      case "ne" -> l != r;
                      case "lt" -> l < r;
                      default -> l <= r;
                    };
                for (boolean bv : new boolean[] {false, true}) {
                  if (!"free".equals(b) && bv != "true".equals(b)) {
                    continue;
                  }
                  if ("reif".equals(kind) ? holds == bv : !bv || holds) {
                    expected.add(
                        "free".equals(b) ? "b = " + bv + "; x = " + x + ";" : "x = " + x + ";");
                  }
                }
              }
              Set<String> actual = solveAll(fzn);
              actual.remove("=====UNSATISFIABLE=====");
              assertEquals(expected, actual, fzn);
            }
          }
        }
      }
    }
  }

  @Test
  void lcgSolvesOptimisationWithClauses() throws IOException {
    // --lcg: bool_clause and array_bool_or go to JaSAT as clauses, the rest propagates as
    // constraints; every improving solution is printed, then the optimum.
    String model =
        """
        var 0..5: x :: output_var;
        var 0..5: y :: output_var;
        var bool: a :: output_var;
        var bool: b :: output_var;
        var bool: c;
        constraint bool_clause([a, b], []);
        constraint array_bool_or([a, c], b);
        constraint int_le_reif(x, 2, a);
        constraint int_le_reif(y, 1, b);
        constraint int_lin_le([1, 1], [x, y], 7);
        constraint int_ne(x, y);
        solve maximize x;
        """;
    String out = run(model, "--lcg", "-s")[0];
    assertTrue(out.contains("x = 5;"), out);
    assertTrue(out.strip().contains("=========="), out);
    assertTrue(out.contains("lcgExplanations"), out);
    String last = out.substring(out.lastIndexOf("x = "));
    assertTrue(last.startsWith("x = 5;") && last.contains("b = true;"), last);
  }

  @Test
  void lcgReportsUnsatisfiable() throws IOException {
    String model =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
        var bool: a;
        constraint bool_clause([a], []);
        constraint int_eq_reif(x, y, a);
        constraint int_ne(x, y);
        solve satisfy;
        """;
    String out = run(model, "--lcg")[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
  }

  @Test
  void lcgTimeOutIsNotReportedComplete() throws IOException {
    // 13 pigeons in 12 holes, as clauses, is far beyond 100 ms of LCG: resolution proofs of the
    // pigeonhole principle are exponential, and no global constraint is detected in clauses (the
    // disequalities of the first version became an alldifferent, whose Hall set explanations
    // prove it at once); an interrupted LCG search printed ========== or =====UNSATISFIABLE=====
    // on the sequence-search path.
    StringBuilder model =
        new StringBuilder("array [1..156] of var bool: p :: output_array([1..13, 1..12]);\n");
    for (int i = 0; i < 13; i++) {
      StringBuilder holes = new StringBuilder();
      for (int k = 0; k < 12; k++) {
        holes.append(k == 0 ? "" : ", ").append("p[%d]".formatted(i * 12 + k + 1));
      }
      model.append("constraint bool_clause([%s], []);\n".formatted(holes));
    }
    for (int k = 0; k < 12; k++) {
      for (int i = 0; i < 13; i++) {
        for (int j = i + 1; j < 13; j++) {
          model.append(
              "constraint bool_clause([], [p[%d], p[%d]]);\n"
                  .formatted(i * 12 + k + 1, j * 12 + k + 1));
        }
      }
    }
    model.append("solve satisfy;\n");
    String out = run(model.toString(), "--lcg", "-t", "100")[0];
    assertTrue(!out.contains("==========") && !out.contains("UNSATISFIABLE"), out);
    assertTrue(out.contains("=====UNKNOWN=====") || out.contains("TIME-OUT"), out);
  }

  @Test
  void lcgFallsBackToSearchForFloatModels() throws IOException {
    String model =
        """
        var 1..3: x :: output_var;
        var 0.0..3.0: f :: output_var;
        constraint int_le(2, x);
        constraint float_le(1.5, f);
        solve satisfy;
        """;
    String out = run(model, "--lcg")[0];
    assertTrue(out.contains("--lcg ignored"), out);
    assertTrue(out.contains("x = 2;"), out);
  }

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
