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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.StringJoiner;
import java.util.TreeSet;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.fz.constraints.AlldifferentDetector;
import org.jacop.fz.constraints.CommonSubexpressions;
import org.jacop.fz.constraints.PartialCopyDetector;
import org.jacop.fz.constraints.Support;
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

  /** The exit status of the last {@link #run} call. */
  private int lastStatus;

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
  void valueChoiceIndomainIsAscendingOrderWithoutWarning() throws IOException {
    // indomain is the MiniZinc value choice "assign values in ascending order"; it was searched as
    // indomain_min but reported on stderr as a not implemented value choice
    String fzn =
        """
        array [1..2] of var 1..3: x:: output_array([1..2]);
        constraint int_ne(x[1],x[2]);
        solve :: int_search(x,input_order,indomain,complete) satisfy;
        """;
    ByteArrayOutputStream errors = new ByteArrayOutputStream();
    PrintStream originalErr = System.err;
    List<String> solutions;
    try (PrintStream capture = new PrintStream(errors, true, StandardCharsets.UTF_8)) {
      System.setErr(capture);
      solutions = solveAllInOrder(fzn);
    } finally {
      System.setErr(originalErr);
    }
    assertEquals("x = array1d(1..2, [1, 2]);", solutions.get(0));
    assertEquals(6, solutions.size());
    assertFalse(errors.toString(StandardCharsets.UTF_8).contains("indomain"), errors::toString);
  }

  @Test
  void secondBool2IntOfAnIntegerJoinsTheTwoBooleans() throws IOException {
    // x is the alias of a after the first bool2int; the second one, which makes b equal to a, was
    // dropped with "Double int var alias for bool var", so a != b was accepted
    String fzn =
        """
        var bool: a:: output_var;
        var bool: b:: output_var;
        var 0..1: x:: output_var;
        constraint bool2int(a,x);
        constraint bool2int(b,x);
        solve satisfy;
        """;

    assertEquals(
        Set.of("a = false; b = false; x = 0;", "a = true; b = true; x = 1;"), solveAll(fzn));
  }

  /**
   * Four variables in 1..3 that must differ pairwise, after eight free variables, all left out of
   * the search annotation. int_ne finds no conflict until three of them are fixed.
   */
  private static String pigeonsAfterFreeVariables(int lastMax) {
    StringBuilder fzn = new StringBuilder("var 1..2: s:: output_var;\n");
    for (int i = 1; i <= 8; i++) {
      fzn.append("var 1..2: a").append(i).append(":: output_var;\n");
    }
    for (int i = 1; i <= 4; i++) {
      fzn.append("var 1..").append(i == 4 ? lastMax : 3).append(": z").append(i);
      fzn.append(":: output_var;\n");
    }
    for (int i = 1; i <= 4; i++) {
      for (int j = i + 1; j <= 4; j++) {
        fzn.append("constraint int_ne(z").append(i).append(",z").append(j).append(");\n");
      }
    }
    return fzn.append("solve :: int_search([s],input_order,indomain_min,complete) satisfy;\n")
        .toString();
  }

  /** Five tasks using 500,000,000 each: their sum wrapped below the capacity in int. */
  @Test
  void aCumulativeWhoseResourceSumPassesIntIsStillPosted() throws IOException {
    String model =
        """
        var 0..7: s0 :: output_var;
        var 0..7: s1 :: output_var;
        var 0..7: s2 :: output_var;
        var 0..7: s3 :: output_var;
        var 0..7: s4 :: output_var;
        constraint jacop_cumulative([s0,s1,s2,s3,s4],[2,2,2,2,2],
          [500000000,500000000,500000000,500000000,500000000],500000000);
        solve satisfy;
        """;
    String out = run(model)[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
  }

  /** The empty word is accepted only when the start state is final. */
  @Test
  void aRegularOverNoVariableFailsWhenTheStartStateIsNotFinal() throws IOException {
    String head = "var 0..1: y :: output_var;\n";
    String tail = "solve satisfy;\n";
    for (String call :
        new String[] {
          "jacop_regular([],2,2,[1,2,2,2],1,%s,1)", "jacop_regular_set([],2,3..4,[1,2,2,2],1,%s,3)"
        }) {
      String rejected = head + "constraint " + String.format(call, "{2}") + ";\n" + tail;
      assertTrue(run(rejected, "-a")[0].contains("=====UNSATISFIABLE====="), rejected);
      String accepted = head + "constraint " + String.format(call, "{1}") + ";\n" + tail;
      assertEquals(Set.of("y = 0;", "y = 1;"), solveAll(accepted), accepted);
    }
  }

  /** x repeated three times with weights of 1,500,000,000 each: the merged item passed an int. */
  @Test
  void aKnapsackWhoseRepeatedItemPassesIntIsPostedAsSums() throws IOException {
    String model =
        """
        var 0..1: x :: output_var;
        var 0..536870000: W :: output_var;
        var 0..10: P :: output_var;
        constraint jacop_knapsack([1500000000,1500000000,1500000000],[1,1,1],W,P,[x,x,x]);
        solve satisfy;
        """;
    assertEquals(Set.of("P = 0; W = 0; x = 0;"), solveAll(model));
  }

  /** Five elements of weight 500,000,000: the sum of the possible elements wrapped in int. */
  @Test
  void aSetSumWhoseWeightsPassIntKeepsItsSolutions() throws IOException {
    String model =
        """
        var set of 1..5: s :: output_var;
        var 0..536870000: t :: output_var;
        constraint jacop_sum_set([1,2,3,4,5],
          [500000000,500000000,500000000,500000000,500000000], s, t);
        solve satisfy;
        """;
    assertEquals(6, solveAll(model).size());
  }

  @Test
  void completionSearchBacktracksToTheLastConflict() throws IOException {
    // The variables the annotation leaves out are labelled by a search JaCoP adds. Without last
    // conflict it tried every assignment of a1..a8 before finding that z1..z4 never fit (3072
    // failures); with it z is branched on first again after each failure (kidney-exchange,
    // MiniZinc Challenge 2023: 4.7 million nodes against Choco's 22 thousand).
    String out = run(pigeonsAfterFreeVariables(3), "-s")[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    Matcher fm = Pattern.compile("%%%mzn-stat: failures=(\\d+)").matcher(out);
    assertTrue(fm.find(), out);
    int failures = Integer.parseInt(fm.group(1));
    assertTrue(failures < 200, out);
  }

  @Test
  void completionSearchWithLastConflictFindsAllSolutions() throws IOException {
    // z4 = 4 and z1..z3 a permutation of 1..3: 6 solutions for each of the 2^9 values of s and a.
    assertEquals(512 * 6, solveAll(pigeonsAfterFreeVariables(4)).size());
  }

  @Test
  void floatSettingsOfAnEarlierRunDoNotCarryOver() throws IOException {
    // FloatDomain keeps precision and print format in static fields. The FlatZinc tests run many
    // models in one JVM, and a float_search precision or --format of one model changed the output
    // of the next (upTo5min/arbitrage_loops5 printed other digits after a float_search model).
    String first =
        """
        var 0.0..10.0: y:: output_var;
        constraint float_lin_eq([3.0],[y],1.0);
        solve :: float_search([y],0.5,input_order,indomain_split,complete) satisfy;
        """;
    String second =
        """
        var 0.0..2.0: x:: output_var;
        constraint float_times(x,x,2.0);
        solve satisfy;
        """;

    assertTrue(run(first, "--format", "0.01")[0].contains("y = 0.33;"));
    String out = run(second)[0];
    // the solution is one of the two doubles around sqrt(2), not an interval of precision 0.5
    assertTrue(
        out.contains("x = 1.4142135623730951;") || out.contains("x = 1.414213562373095;"), out);
    assertEquals(FloatDomain.DEFAULT_PRECISION, FloatDomain.precision());
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
  void productOfZeroOneVariableAndConstantHasOnlyTwoValues() throws IOException {
    // y2 = 7 * b2 cannot be 5, so only y1 = 5 * b1 can give the 5 the count needs and b1 = 1.
    // XmulCeqZ is bounds consistent and left y2 in 0..7, which needed a failed decision b1 = 0
    // (vaccine, fixed search).
    String fzn =
        """
        var 0..1: b1:: output_var;
        var 0..1: b2:: output_var;
        var 0..5: y1;
        var 0..7: y2;
        constraint int_lin_eq([5,-1],[b1,y1],0);
        constraint int_lin_eq([7,-1],[b2,y2],0);
        constraint jacop_count_values_bounds([y1,y2],[5],[1],[2]);
        solve :: int_search([b1,b2],input_order,indomain_min,complete) satisfy;
        """;

    String out = run(fzn, "-s")[0];
    assertTrue(out.contains("b1 = 1;"), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
  }

  @Test
  void allDifferentOverSmallDenseDomainsIsDomainConsistent() throws IOException {
    // a and b take 1 and 3, so c = 2. A dense all_different was bounds consistent, which does not
    // see the hole in a and b and needed a failed decision c = 1 (sudoku_opt, fixed search).
    String fzn =
        """
        var {1,3}: a;
        var {1,3}: b;
        var 1..3: c:: output_var;
        constraint jacop_alldiff([a,b,c]);
        solve :: int_search([c],input_order,indomain_min,complete) satisfy;
        """;

    String out = run(fzn, "-s")[0];
    assertTrue(out.contains("c = 2;"), out);
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
  void searchAnnotationsAcceptConstants() throws IOException {
    // MiniZinc's -O3 and above fix variables before writing the FlatZinc, so a search annotation
    // can list Boolean constants; they were rejected with "Wrong parameter"
    String fzn =
        """
        var bool: b:: output_var;
        var 0..1: x:: output_var;
        constraint bool2int(b, x);
        solve :: seq_search([bool_search([true, b, false], input_order, indomain_min, complete),\
         int_search([3, x], input_order, indomain_min, complete)]) satisfy;
        """;

    String[] out = run(fzn);
    assertTrue(out[0].contains("b = false;") && out[0].contains("x = 0;"), out[0] + out[1]);
  }

  @Test
  void intSearchAcceptsBool2intOfBooleans() throws IOException {
    // MiniZinc 2.8 writes the Booleans of an int_search as bool2int(b) (rel2onto); the annotation
    // was rejected with a ClassCastException
    String fzn =
        """
        var bool: a:: output_var;
        var bool: b:: output_var;
        var 0..2: x:: output_var;
        constraint bool_clause([a, b], []);
        solve :: seq_search([int_search([bool2int(b), bool2int(a)], input_order, indomain_min,\
         complete), int_search([x], input_order, indomain_max, complete)]) satisfy;
        """;

    for (String[] options : new String[][] {{}, {"--lcg"}}) {
      String[] out = run(fzn, options);
      assertTrue(
          out[0].contains("a = true;")
              && out[0].contains("b = false;")
              && out[0].contains("x = 2;"),
          out[0] + out[1]);
    }
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
  void equalLongSetArraysAreKeptOnceAndDifferentOnesApart() throws IOException {
    // Set arrays of 1024 or more sets are kept once for each content (MiniZinc repeats the label
    // sets of an MDD for every constraint). S1 and S2 are equal, S3 differs in its last set only:
    // x and y may take 0..2 and z 0..3.
    int n = 1024;
    StringBuilder sets = new StringBuilder();
    StringBuilder other = new StringBuilder();
    StringBuilder from = new StringBuilder();
    StringBuilder to = new StringBuilder();
    for (int i = 0; i < n; i++) {
      String sep = i == 0 ? "" : ",";
      sets.append(sep).append('{').append(i % 3).append('}');
      other.append(sep).append('{').append(i == n - 1 ? 3 : i % 3).append('}');
      from.append(sep).append(1);
      to.append(sep).append(0);
    }
    String fzn =
        "array [1..%d] of set of int: S1 = [%s];%n".formatted(n, sets)
            + "array [1..%d] of set of int: S2 = [%s];%n".formatted(n, sets)
            + "array [1..%d] of set of int: S3 = [%s];%n".formatted(n, other)
            + "array [1..%d] of int: F = [%s];%n".formatted(n, from)
            + "array [1..%d] of int: T = [%s];%n".formatted(n, to)
            + """
            var 0..5: x:: output_var;
            var 0..5: y:: output_var;
            var 0..5: z:: output_var;
            constraint jacop_mdd([x],[1],F,S1,T);
            constraint jacop_mdd([y],[1],F,S2,T);
            constraint jacop_mdd([z],[1],F,S3,T);
            solve satisfy;
            """;
    Set<String> expected = new HashSet<>();
    for (int x = 0; x <= 2; x++) {
      for (int y = 0; y <= 2; y++) {
        for (int z = 0; z <= 3; z++) {
          expected.add("x = " + x + "; y = " + y + "; z = " + z + ";");
        }
      }
    }
    assertEquals(expected, solveAll(fzn));
  }

  @Test
  void equalSetsOfLongSetArraysAreKeptOnce(@TempDir Path dir) throws IOException {
    // The label sets of an MDD repeat a few sets millions of times (31 million sets, 4.2 GB while
    // MagicSquare-mdd-16 of XCSP 2023 was read). Sets of arrays of 1024 or more sets are kept once
    // for each content; shorter arrays keep their own sets. z may take 0..3, x and y 0..2.
    int n = 1024;
    StringBuilder sets = new StringBuilder();
    StringBuilder other = new StringBuilder();
    StringBuilder from = new StringBuilder();
    StringBuilder to = new StringBuilder();
    for (int i = 0; i < n; i++) {
      String sep = i == 0 ? "" : ",";
      sets.append(sep).append('{').append(i % 3).append('}');
      other.append(sep).append(i == n - 1 ? "1..3" : "{" + i % 3 + "}");
      from.append(sep).append(1);
      to.append(sep).append(0);
    }
    String model =
        "array [1..%d] of set of int: S1 = [%s];%n".formatted(n, sets)
            + "array [1..%d] of set of int: S2 = [%s];%n".formatted(n, other)
            + "array [1..3] of set of int: S3 = [{0},{1},{0}];\n"
            + "array [1..%d] of int: F = [%s];%n".formatted(n, from)
            + "array [1..%d] of int: T = [%s];%n".formatted(n, to)
            + """
            var 0..5: x:: output_var;
            var 0..5: y:: output_var;
            var 0..5: z:: output_var;
            constraint jacop_mdd([x],[1],F,S1,T);
            constraint jacop_mdd([y],[1],[1,1,1],S3,[0,0,0]);
            constraint jacop_mdd([z],[1],F,S2,T);
            solve satisfy;
            """;
    Path fzn = dir.resolve("sets.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    PrintStream out = System.out;
    Tables tables;
    try (PrintStream quiet = new PrintStream(OutputStream.nullOutputStream())) {
      System.setOut(quiet);
      FlatzincLoader loader = new FlatzincLoader(new String[] {fzn.toString()});
      loader.load();
      tables = loader.getTables();
    } finally {
      System.setOut(out);
    }
    IntDomain[] s1 = tables.getSetArray("S1");
    IntDomain[] s2 = tables.getSetArray("S2");
    IntDomain[] s3 = tables.getSetArray("S3");
    assertSame(s1[0], s1[3]);
    assertSame(s1[1], s2[1]);
    assertNotSame(s1[0], s1[1]);
    assertNotSame(s2[n - 2], s2[n - 1]);
    assertTrue(new IntervalDomain(1, 3).eq(s2[n - 1]));
    assertNotSame(s3[0], s3[2]);

    Set<String> expected = new HashSet<>();
    for (int x = 0; x <= 2; x++) {
      for (int y = 0; y <= 1; y++) {
        for (int z = 0; z <= 3; z++) {
          expected.add("x = " + x + "; y = " + y + "; z = " + z + ";");
        }
      }
    }
    assertEquals(expected, solveAll(model));
  }

  @Test
  void mddLibraryPassesTheDiagramArraysAsTheyAre() throws IOException {
    // array1d makes a new array at each call and MiniZinc keeps only a few for reuse: with it,
    // WordDesign2-words-mdd-025 (XCSP 2023) got 31 copies of its diagram of 1.8 million edges in
    // the FlatZinc (1.1 GB, 7 GB to flatten) and the larger sizes did not flatten at all.
    Path lib = Path.of("src/main/minizinc/org/jacop/minizinc");
    for (String file : List.of("fzn_mdd.mzn", "fzn_mdd_nondet.mzn", "fzn_cost_mdd.mzn")) {
      String text = Files.readString(lib.resolve(file), StandardCharsets.UTF_8);
      for (String array : List.of("level", "from", "label", "cost", "to")) {
        assertFalse(text.contains("array1d(" + array + ")"), file + " copies " + array);
      }
    }
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
  void allSolutionsAreReportedOnceWhenProbingFixesTheOutputVariables() throws IOException {
    // Root probing of presolve fixes x (x = 1 forces y = 2 > x). With every output variable fixed
    // the front end labelled every variable instead, so x = 2 was reported once for each
    // assignment of z, b1 and b2, which are not output variables (hakank_kaprekars_constant2).
    String fzn =
        """
        var 1..2: x:: output_var;
        var 1..2: y;
        var 1..3: z;
        var bool: b1;
        var bool: b2;
        constraint int_ne(x,y);
        constraint int_le(y,x);
        constraint int_le_imp(z,1,b1);
        constraint int_ge_imp(z,3,b2);
        constraint bool_clause([b1,b2],[]);
        solve :: int_search([x], input_order, indomain_min, complete) satisfy;
        """;

    assertEquals(List.of("x = 2;"), solveAllInOrder(fzn, "--presolve", "on"));
    assertEquals(List.of("x = 2;"), solveAllInOrder(fzn, "--presolve", "off"));
  }

  @Test
  void presolveDoesNotEliminateABooleanDefinedBySetMembership() throws IOException {
    // b occurs only in set_in_reif(1,s,b), so variable elimination took the reification as its
    // definition; the postsolve copies only integer variables and failed on s with a
    // ClassCastException (submultisetsum, superset_package_deps)
    String fzn =
        """
        var set of 1..2: s:: output_var;
        var bool: b;
        constraint set_in_reif(1,s,b);
        solve satisfy;
        """;

    List<String> all = List.of("s = 1..1;", "s = 1..2;", "s = 2..2;", "s = {};");
    assertEquals(new TreeSet<>(all), new TreeSet<>(solveAllInOrder(fzn, "--presolve", "on")));
    assertEquals(new TreeSet<>(all), new TreeSet<>(solveAllInOrder(fzn, "--presolve", "off")));
  }

  @Test
  void linearDisequalityOfTwoVariablesWithOppositeUnitWeightsKeepsItsSign() throws IOException {
    // int_lin_ne_reif/_imp([-1,1],[x,y],c,b) was posted as x - y != c, the sign of c lost when the
    // variables were reordered by coefficient (fuzz model 700463: 170 solutions instead of 180)
    for (String kind : List.of("reif", "imp")) {
      for (int[] w : new int[][] {{-1, 1}, {1, -1}}) {
        String fzn =
            """
            var 0..3: x:: output_var;
            var 0..3: y:: output_var;
            var bool: b:: output_var;
            constraint int_lin_ne_%s([%d,%d],[x,y],2,b);
            solve satisfy;
            """
                .formatted(kind, w[0], w[1]);
        Set<String> expected = new TreeSet<>();
        for (int x = 0; x <= 3; x++) {
          for (int y = 0; y <= 3; y++) {
            boolean ne = w[0] * x + w[1] * y != 2;
            for (boolean b : new boolean[] {false, true}) {
              if (kind.equals("reif") ? b == ne : !b || ne) {
                expected.add("b = " + b + "; x = " + x + "; y = " + y + ";");
              }
            }
          }
        }
        assertEquals(
            expected, new TreeSet<>(solveAllInOrder(fzn)), kind + " " + Arrays.toString(w));
      }
    }
  }

  // The front end maps each builtin to one of many special cases (by weights, constants, aliasing
  // and annotations); a slip in one of them, such as the sign of int_lin_ne_imp([-1,1],...), only
  // shows on the inputs that reach it. Random small calls of each builtin, under several option
  // sets, must give exactly the solutions of enumeration.
  @Test
  void builtinsAgreeWithEnumeration() throws IOException {
    int trials = Integer.getInteger("builtins.trials", 300);
    String[][] options = {{}, {"--presolve", "on"}, {"--lcg"}, {"-sat"}};
    Random rnd = new Random(20261030);
    List<Builtin> calls = new ArrayList<>();
    // every comparison of one or two unit-weight terms, the shapes with their own special cases
    int[][] unitWeights = {{1}, {-1}, {1, 1}, {1, -1}, {-1, 1}, {-1, -1}};
    for (String op : new String[] {"eq", "ne", "le", "lt"}) {
      for (String kind : new String[] {"", "_reif", "_imp"}) {
        for (int[] w : unitWeights) {
          calls.add(randomBuiltin(rnd, "int_lin_" + op + kind, w));
        }
      }
    }
    for (int t = 0; t < trials; t++) {
      calls.add(randomBuiltin(rnd, null, null));
    }
    for (int t = 0; t < calls.size(); t++) {
      Builtin b = calls.get(t);
      String[] opts = options[t % options.length];
      Set<String> found = new TreeSet<>(solveAllInOrder(b.fzn, opts));
      found.remove("=====UNSATISFIABLE=====");
      assertEquals(b.expected, found, b.fzn + String.join(" ", opts));
    }
  }

  private record Builtin(String fzn, Set<String> expected) {}

  /**
   * A random call of a random builtin, or of the given int_lin_* builtin with the given weights.
   */
  private static Builtin randomBuiltin(Random rnd, String linear, int[] weights) {
    String[] cmp = {"eq", "ne", "le", "lt"};
    String[] kinds = {"", "_reif", "_imp"};
    String op = cmp[rnd.nextInt(cmp.length)];
    String kind = kinds[rnd.nextInt(kinds.length)];
    int k;
    int[] w;
    String name;
    boolean bools = false;
    switch (linear != null ? -1 : rnd.nextInt(4)) {
      case -1 -> {
        k = weights.length;
        w = weights;
        name = linear;
        op = linear.split("_")[2];
        kind = linear.substring(("int_lin_" + op).length());
      }
      case 0 -> {
        // int_lin_*: weights of both unit signs and larger, with a repeated variable at times
        k = 1 + rnd.nextInt(4);
        w = new int[k];
        for (int i = 0; i < k; i++) {
          w[i] = rnd.nextBoolean() ? (rnd.nextBoolean() ? 1 : -1) : rnd.nextInt(7) - 3;
          w[i] = w[i] == 0 ? 2 : w[i];
        }
        name = "int_lin_" + op + kind;
      }
      case 1 -> {
        k = 2;
        w = new int[] {1, -1};
        name = "int_" + op + kind;
      }
      case 2 -> {
        k = 2;
        w = new int[] {1, -1};
        bools = true;
        name = "bool_" + op + kind;
      }
      default -> {
        String[] ar = {"int_plus", "int_times", "int_div", "int_mod", "int_min", "int_max"};
        name = ar[rnd.nextInt(ar.length)];
        k = 3;
        w = null;
        kind = "";
      }
    }
    int c = rnd.nextInt(9) - 4;
    int[] lo = new int[k];
    int[] hi = new int[k];
    int[] aVar = new int[k];
    for (int i = 0; i < k; i++) {
      lo[i] = bools ? 0 : rnd.nextInt(7) - 3;
      hi[i] = bools ? 1 : lo[i] + rnd.nextInt(4);
      aVar[i] = i > 0 && rnd.nextInt(5) == 0 ? aVar[rnd.nextInt(i)] : i;
    }
    StringBuilder fzn = new StringBuilder();
    StringJoiner args = new StringJoiner(",");
    for (int i = 0; i < k; i++) {
      if (aVar[i] == i) {
        fzn.append(bools ? "var bool" : "var " + lo[i] + ".." + hi[i]).append(": x").append(i);
        fzn.append(":: output_var;\n");
      }
      args.add("x" + aVar[i]);
    }
    boolean reif = !kind.isEmpty();
    if (reif) {
      fzn.append("var bool: b:: output_var;\n");
    }
    String call;
    if (name.startsWith("int_lin_")) {
      StringJoiner ws = new StringJoiner(",");
      for (int x : w) {
        ws.add(Integer.toString(x));
      }
      call = name + "([" + ws + "],[" + args + "]," + c + (reif ? ",b" : "") + ")";
    } else {
      call = name + "(" + args + (reif ? ",b" : "") + ")";
    }
    fzn.append("constraint ").append(call).append(";\nsolve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] v = new int[k];
    int[] value = new int[k];
    String fName = name;
    String fKind = kind;
    String fOp = op;
    boolean fBools = bools;
    enumerateBuiltin(
        0,
        v,
        lo,
        hi,
        aVar,
        () -> {
          for (int i = 0; i < k; i++) {
            value[i] = v[aVar[i]];
          }
          Boolean holds;
          if (fName.startsWith("int_lin_") || w != null) {
            int s = 0;
            for (int i = 0; i < k; i++) {
              s += w[i] * value[i];
            }
            int rhs = fName.startsWith("int_lin_") ? c : 0;
            holds =
                switch (fOp) {
                  case "eq" -> s == rhs;
                  case "ne" -> s != rhs;
                  case "le" -> s <= rhs;
                  default -> s < rhs;
                };
          } else {
            int x = value[0];
            int y = value[1];
            int z = value[2];
            holds =
                switch (fName) {
                  case "int_plus" -> x + y == z;
                  case "int_times" -> x * y == z;
                  case "int_div" -> y != 0 && x / y == z;
                  case "int_mod" -> y != 0 && x % y == z;
                  case "int_min" -> Math.min(x, y) == z;
                  default -> Math.max(x, y) == z;
                };
          }
          StringJoiner sol = new StringJoiner(" ");
          for (int i = 0; i < k; i++) {
            if (aVar[i] == i) {
              sol.add(
                  "x"
                      + i
                      + " = "
                      + (fBools ? Boolean.toString(v[i] == 1) : Integer.toString(v[i]))
                      + ";");
            }
          }
          if (fKind.isEmpty()) {
            if (holds) {
              expected.add(sol.toString());
            }
          } else {
            for (boolean b : new boolean[] {false, true}) {
              if (fKind.equals("_reif") ? b == holds : !b || holds) {
                expected.add("b = " + b + "; " + sol);
              }
            }
          }
        });
    return new Builtin(fzn.toString(), expected);
  }

  private static void enumerateBuiltin(
      int i, int[] v, int[] lo, int[] hi, int[] aVar, Runnable check) {
    if (i == v.length) {
      check.run();
      return;
    }
    if (aVar[i] != i) {
      enumerateBuiltin(i + 1, v, lo, hi, aVar, check);
      return;
    }
    for (v[i] = lo[i]; v[i] <= hi[i]; v[i]++) {
      enumerateBuiltin(i + 1, v, lo, hi, aVar, check);
    }
  }

  @Test
  void twoImplicationsOfTheSameEqualityKeepTheirBooleansIndependent() throws IOException {
    // int_eq_imp(x,0,a) and int_eq_imp(x,0,b) were collected as one channel and a = b was posted,
    // as for reifications; with a false and the clause a \/ b the 2021 Challenge model
    // flowshop-workers failed at the root on all its instances
    String fzn =
        """
        var bool: a:: output_var;
        var bool: b:: output_var;
        var 0..2: x:: output_var;
        constraint int_eq_imp(x,0,a);
        constraint int_eq_imp(x,0,b);
        solve satisfy;
        """;

    assertEquals(
        List.of(
            "a = false; b = false; x = 0;",
            "a = false; b = false; x = 1;",
            "a = false; b = false; x = 2;",
            "a = false; b = true; x = 0;",
            "a = true; b = false; x = 0;",
            "a = true; b = true; x = 0;"),
        solveAllInOrder(fzn).stream().sorted().toList());
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
  void modelWithoutSearchAnnotationIsSolvedAsWithFreeSearch() throws IOException {
    // Without annotation the variables were labelled in input order with domain splitting, which
    // found no solution of queens n = 50 in 60 s; free search (-f) finds one in under a second.
    String model = queens(12, "");
    String free = searchStatistics(run(model, "-s", "-f")[0]);

    assertEquals(free, searchStatistics(run(model, "-s")[0]));
    assertNotEquals(free, searchStatistics(run(model, "-s", "--default-search", "input")[0]));
    // an annotation is still followed
    String annotated = queens(12, ":: int_search(q,input_order,indomain_min,complete)");
    assertEquals(
        searchStatistics(run(annotated, "-s", "--default-search", "input")[0]),
        searchStatistics(run(annotated, "-s")[0]));
  }

  /** FlatZinc of n queens on q, with the given search annotation. */
  private static String queens(int n, String annotation) {
    StringBuilder fzn = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      fzn.append("var 1..%d: q%d;%n".formatted(n, i));
    }
    fzn.append("array [1..%d] of var int: q:: output_array([1..%d]) = [".formatted(n, n));
    for (int i = 1; i <= n; i++) {
      fzn.append(i > 1 ? "," : "").append('q').append(i);
    }
    fzn.append("];\n");
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        fzn.append("constraint int_ne(q%d,q%d);%n".formatted(i, j));
        fzn.append("constraint int_lin_ne([1,-1],[q%d,q%d],%d);%n".formatted(i, j, j - i));
        fzn.append("constraint int_lin_ne([1,-1],[q%d,q%d],%d);%n".formatted(i, j, i - j));
      }
    }
    fzn.append("solve %s satisfy;%n".formatted(annotation));
    return fzn.toString();
  }

  /**
   * The detectors that skip a model without the constraint kinds they rewrite leave the model and
   * the search as they are: a weighted clause model (the shape of the MaxSAT models, whose 2
   * million clauses each detector pass read for seconds) and a model with a cyclic distance, whose
   * detector still runs, give the same model and optimum with the gates on and off.
   */
  @Test
  void detectorGatesKeepTheModelAndTheSearch() throws IOException {
    StringBuilder clauses = new StringBuilder();
    for (int i = 1; i <= 12; i++) {
      clauses.append("var bool: x").append(i).append(";\n");
    }
    StringBuilder body = new StringBuilder();
    Random random = new Random(7);
    for (int c = 0; c < 30; c++) {
      int a = 1 + random.nextInt(12);
      int b = 1 + random.nextInt(12);
      int d = 1 + random.nextInt(12);
      body.append("constraint bool_clause([x").append(a).append(",x").append(b);
      body.append("],[x").append(d).append("]);\n");
    }
    StringBuilder terms = new StringBuilder();
    StringBuilder weights = new StringBuilder();
    for (int i = 1; i <= 12; i++) {
      clauses.append("var 0..1: b").append(i).append(":: is_defined_var;\n");
      body.append("constraint bool2int(x").append(i).append(",b").append(i);
      body.append("):: defines_var(b").append(i).append(");\n");
      terms.append(i > 1 ? "," : "").append("b").append(i);
      weights.append(i > 1 ? "," : "").append(1 + i % 4);
    }
    String clauseModel =
        clauses
            + "var 0..100: objective:: output_var:: is_defined_var;\n"
            + body
            + "constraint int_lin_eq(["
            + weights
            + ",-1],["
            + terms
            + ",objective],0):: defines_var(objective);\n"
            + "solve minimize objective;\n";
    String cyclic =
        """
        array [1..3] of var 0..9: x:: output_array([1..3]);
        var -9..9: e1;
        var -9..9: e2;
        var 0..9: a1;
        var 0..9: a2;
        var 0..9: c1;
        var 0..9: c2;
        var 0..9: m1;
        var 0..9: m2;
        var 0..18: objective:: output_var;
        constraint int_lin_eq([1,-1,-1],[x[1],x[2],e1],0);
        constraint int_lin_eq([1,-1,-1],[x[2],x[3],e2],0);
        constraint int_abs(e1,a1);
        constraint int_abs(e2,a2);
        constraint int_lin_eq([1,1],[a1,c1],10);
        constraint int_lin_eq([1,1],[a2,c2],10);
        constraint int_min(a1,c1,m1);
        constraint int_min(a2,c2,m2);
        constraint int_lin_eq([1,1,-1],[m1,m2,objective],0);
        constraint int_ne(x[1],x[3]);
        solve maximize objective;
        """;
    String gates = System.getProperty("org.jacop.fz.detectorGates");
    try {
      for (String model : List.of(clauseModel, cyclic)) {
        System.clearProperty("org.jacop.fz.detectorGates");
        String[] on = run(model, "-s", "-a");
        System.setProperty("org.jacop.fz.detectorGates", "false");
        String[] off = run(model, "-s", "-a");
        // the search of a second run in one JVM may differ (static random, clocks): the model and
        // the optimum are compared
        assertEquals(modelStatistics(off[0]), modelStatistics(on[0]), model);
        assertEquals(optimum(off[0]), optimum(on[0]), model);
      }
    } finally {
      restoreProperty("org.jacop.fz.detectorGates", gates);
    }
  }

  /** The last objective line of a run. */
  private static String optimum(String out) {
    int at = out.lastIndexOf("objective = ");
    assertTrue(at >= 0, out);
    return out.substring(at, out.indexOf(';', at));
  }

  /** The variables and propagators of the model of a run with -s. */
  private static String modelStatistics(String out) {
    return out.lines()
        .filter(
            l ->
                l.startsWith("%%%mzn-stat: variables=")
                    || l.startsWith("%%%mzn-stat: propagators="))
        .collect(Collectors.joining("\n"));
  }

  /** The search statistics of a run with -s, without the times and the memory. */
  private static String searchStatistics(String out) {
    return out.lines()
        .filter(
            l ->
                l.startsWith("%%%mzn-stat: ")
                    && !l.contains("Time=")
                    && !l.contains("time=")
                    && !l.contains("peakMem="))
        .collect(Collectors.joining("\n"));
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
    assertEquals(1, lastStatus, "a rejected model must not exit with status 0");
  }

  @Test
  void integerLiteralBeyond32BitsIsRejectedWithErrorStatus() throws IOException {
    // hakank's hardy_1729 and others: the bare NumberFormatException message was printed and
    // Fz2jacop exited with status 0, so scripts took the run for a success.
    String fzn =
        """
        var 1..10: x :: output_var;
        constraint int_le(x, 10000000000);
        solve satisfy;
        """;

    String[] out = run(fzn);
    assertEquals("", out[0]);
    assertTrue(out[1].contains("integer literal 10000000000 at line 2"), out[1]);
    assertTrue(out[1].contains("outside the 32-bit integer range"), out[1]);
    assertEquals(1, lastStatus);

    run("var 1..10: x :: output_var;\nconstraint int_le(x, 1000000);\nsolve satisfy;\n");
    assertEquals(0, lastStatus);
  }

  @Test
  void domainBeyondIntegerRangeIsNarrowedWithoutClaimingCompleteness() throws IOException {
    // MiniZinc writes computed bounds such as 0..4722438400 for a product (2022
    // arithmetic-target); they were rejected as 32-bit overflows, and 0..1687566400 was taken
    // silently beyond IntDomain.MAX_INT. The domain is narrowed to JaCoP's range, so a completed
    // search proves nothing about the values cut off, unless the model's linear rows bound them
    // (here x <= 3)
    String fzn =
        """
        var 0..4722438400: x :: output_var;
        constraint int_le(x, 3);
        solve maximize x;
        """;
    String[] out = run(fzn);
    assertEquals(0, lastStatus, out[1]);
    assertEquals("x = 3;\n----------\n==========\n", out[0]);
    assertTrue(out[1].contains("1 variable domain reaches beyond"), out[1]);
    assertTrue(out[1].contains("(first: x 0..4722438400)"), out[1]);
    // bounded through a function of a bounded variable: still optimal
    out =
        run(
            """
            var 0..4722438400: x :: output_var;
            var 0..3: y;
            constraint int_abs(y, x);
            solve maximize x;
            """);
    assertTrue(out[0].endsWith("x = 3;\n----------\n==========\n"), out[0]);
    // bounded only through a constraint the bounds of the rows do not read: no claim
    out =
        run(
            """
            var 0..4722438400: x :: output_var;
            var 0..3: y;
            constraint set_in(x, {0, 1, 4, 9});
            constraint int_le(y, x);
            solve maximize x;
            """);
    assertTrue(out[0].endsWith("x = 9;\n----------\n"), out[0]);

    // no claim of unsatisfiability: the solutions may lie in the values cut off
    out =
        run("var -10..1687566400: x :: output_var;\nconstraint int_le(x, -11);\nsolve satisfy;\n");
    assertTrue(out[0].endsWith("=====UNKNOWN=====\n"), out[0]);
    out =
        run(
            """
            var 0..1687566400: x :: output_var;
            var 0..9: y :: output_var;
            constraint int_lin_eq([1, -1], [x, y], 600000000);
            solve satisfy;
            """);
    assertTrue(out[0].endsWith("=====UNKNOWN=====\n"), out[0]);

    // the same model without the narrowing: a domain within the range is taken as declared
    out = run("var 0..536870909: x :: output_var;\nconstraint int_le(x, 3);\nsolve maximize x;\n");
    assertEquals("x = 3;\n----------\n==========\n", out[0]);
    assertEquals("", out[1]);
  }

  @Test
  void objectiveNarrowedOnItsWorseSideKeepsOptimality() throws IOException {
    // 2020 code-generator: "var 0..2014326920: objective" is minimised; the values cut off are
    // worse than any solution found, so the optimum is still proved
    String[] out =
        run(
            """
            var 0..2014326920: c :: output_var;
            var 1..5: y :: output_var;
            constraint int_lin_eq([1, -2], [c, y], 0);
            solve minimize c;
            """);
    assertEquals("c = 2;\ny = 1;\n----------\n==========\n", out[0]);
    // maximised, the values cut off are the better ones, but c = 2 * y <= 10 bounds them
    out =
        run(
            """
            var 0..2014326920: c :: output_var;
            var 1..5: y :: output_var;
            constraint int_lin_eq([1, -2], [c, y], 0);
            solve maximize c;
            """);
    assertEquals("c = 10;\ny = 5;\n----------\n==========\n", out[0]);
    // without a row or a function the bounds read: no claim
    out =
        run(
            """
            var 0..2014326920: c :: output_var;
            var 1..5: y :: output_var;
            constraint set_in(c, {1, 4, 9, 16, 25});
            constraint int_le(y, c);
            solve maximize c;
            """);
    assertTrue(out[0].endsWith("c = 25;\ny = 1;\n----------\n"), out[0]);
    // an array element of the objective's array narrowed too; a[2] <= 4 bounds it
    out =
        run(
            """
            array [1..2] of var 0..2014326920: a :: output_array([1..2]);
            constraint int_le(a[2], 4);
            solve minimize a[1];
            """);
    assertTrue(out[0].endsWith("----------\n==========\n"), out[0]);
  }

  @Test
  void costCapWithWeightsBeyondIntFixesTheHeavyVariables() throws IOException {
    // PB competition wcsp instances (spot5-28, satellite02cc, zenotravel04ac): the cost cap
    // sum w * x <= top - 1 weighs each hard violation top, more than the cap, and the weights add
    // up beyond an int; LinearBool rejected the cap and then the objective row ("problem detected")
    String cap =
        "constraint int_lin_le([1000000000, 1000000000, 1000000000, 3, 4], [a, b, c, d, e], 5);\n";
    String objective =
        "constraint int_lin_eq([1000000000, 1000000000, 1000000000, 3, 4, -1], [a, b, c, d, e, cost], 0);\n";
    String head =
        """
        var 0..1: a :: output_var;
        var 0..1: b :: output_var;
        var 0..1: c :: output_var;
        var 0..1: d :: output_var;
        var 0..1: e :: output_var;
        var 0..3000000007: cost :: output_var;
        constraint int_lin_le([-1, -1], [d, e], -1);
        """;
    String expected = "a = 0;\nb = 0;\nc = 0;\nd = 1;\ne = 0;\ncost = 3;\n----------\n==========\n";
    for (String rows : new String[] {cap + objective, objective + cap}) {
      String[] out = run(head + rows + "solve minimize cost;\n");
      assertEquals(0, lastStatus, out[1]);
      assertEquals(expected, tail(out[0]), out[1]);
    }
    // without the cap the heavy variables stay free, the objective row still posts
    String[] out = run(head + objective + "solve minimize cost;\n");
    assertEquals(0, lastStatus, out[1]);
    assertEquals(expected, tail(out[0]), out[1]);
  }

  @Test
  void objectiveBeyondTheRangeDividedByItsDivisor() throws IOException {
    // 2023 unit-commitment: obj 0..2147483646 is a sum of costs that are multiples of 5, and the
    // solutions of the fixed search all lie beyond 536870909; narrowed, L12 and L15 got no
    // solution in 1200 s. Here obj = 1000000 * x >= 600000000: narrowed, no solution at all
    String model =
        """
        var 0..2147483646: obj :: is_defined_var;
        var 0..2147483646: _objective :: output_var = obj;
        var 600..2000: x :: output_var;
        array [1..2] of int: c = [1000000, -1];
        constraint int_lin_eq(c, [x, obj], 0) :: defines_var(obj);
        constraint int_lin_le([1, 1], [x, obj], 2100000000);
        solve :: int_search([obj], input_order, indomain_max, complete) minimize obj;
        """;
    String[] out = run(model, "-a");
    assertEquals(0, lastStatus, out[1]);
    assertTrue(out[0].startsWith("_objective = 2000000000;\nx = 2000;\n----------\n"), out[0]);
    assertTrue(
        out[0].endsWith("_objective = 600000000;\nx = 600;\n----------\n==========\n"), out[0]);
    assertFalse(out[1].contains("narrowed"), out[1]);
    // the threads of a portfolio share the model tree, whose rows are rewritten once
    out = run(model, "-p", "2");
    assertTrue(
        out[0].endsWith("_objective = 600000000;\nx = 600;\n----------\n==========\n"), out[0]);
    // maximised, with the objective's coefficient -2: c * obj is a multiple of 2000000, so obj of
    // 1000000
    out =
        run(
            """
            var -2147483646..0: obj :: output_var;
            var 300..1000: x :: output_var;
            constraint int_lin_eq([-2000000, -2], [x, obj], 0);
            solve maximize obj;
            """);
    assertEquals("obj = -300000000;\nx = 300;\n----------\n==========\n", tail(out[0]));
    // the objective in a constraint other than a linear row keeps its narrowed domain
    out =
        run(
            """
            var 0..2147483646: obj :: output_var;
            var 600..2000: x :: output_var;
            var 0..2147483646: y;
            constraint int_lin_eq([1000000, -1], [x, obj], 0);
            constraint int_abs(obj, y);
            solve minimize obj;
            """);
    assertTrue(out[0].contains("=====UNKNOWN====="), out[0]);
    // without a divisor that brings the domain into the range
    out =
        run(
            """
            var 0..2147483646: obj :: output_var;
            var 0..2000: x :: output_var;
            constraint int_lin_eq([3, -1], [x, obj], 1);
            solve minimize obj;
            """);
    assertTrue(out[0].endsWith("obj = 2;\nx = 1;\n----------\n==========\n"), out[0]);
    assertTrue(out[1].contains("narrowed"), out[1]);
  }

  @Test
  void narrowingShownHarmlessByTheModelsRows() throws IOException {
    // 2021 connect 0086_02: 325 domains 0..1000000000, bounded through the linear rows with the
    // objective below the best solution, unused, or only bounded from below as s >= -y / 1000. The
    // search completed in 15 s at the optimum and could not claim it
    String[] out =
        run(
            """
            var 0..1000000000: f :: output_var;
            var 0..1000000000: unused;
            var 0..1000000000: s;
            var 0..20: y :: output_var;
            var 0..1000000000: cost :: output_var;
            constraint int_le(3, y);
            constraint int_lin_le([-1, -1000], [y, s], 0);
            constraint int_lin_le([1, -1], [y, f], 0);
            constraint int_lin_eq([1, -2, -1], [cost, f, y], 0);
            solve minimize cost;
            """);
    assertEquals("f = 3;\ny = 3;\ncost = 9;\n----------\n==========\n", tail(out[0]));
    // y = 0 needs s >= 600000000, beyond the narrowed domain: no claim of the optimum 0 cut off
    out =
        run(
            """
            var 0..2000000000: s :: output_var;
            var 0..1: y :: output_var;
            constraint int_lin_le([-1, -600000000], [s, y], -600000000);
            solve minimize y;
            """);
    assertTrue(out[0].endsWith("y = 1;\n----------\n"), out[0]);
    // four pigeons in three holes, which the search proves, and the narrowed variable unused
    out =
        run(
            """
            var 0..2000000000: s :: output_var;
            array [1..4] of var 1..3: p :: output_array([1..4]);
            constraint int_ne(p[1], p[2]);
            constraint int_ne(p[1], p[3]);
            constraint int_ne(p[1], p[4]);
            constraint int_ne(p[2], p[3]);
            constraint int_ne(p[2], p[4]);
            constraint int_ne(p[3], p[4]);
            solve satisfy;
            """);
    assertTrue(out[0].endsWith("=====UNSATISFIABLE=====\n"), out[0]);
  }

  @Test
  void narrowedProductComparedInsideTheRangeIsSaturated() throws IOException {
    // 2022 arithmetic-target: tree_vals[i] = tree_vals[l] * tree_vals[r] only for a Mul node, a
    // product declared 0..4722438400 and used only in int_eq_imp. Narrowed, int_times removed the
    // pairs whose product does not fit, also at nodes that are no products, and the completed
    // search claimed nothing. Saturated at the end of the range it keeps them: here the optimum
    // x = y = 30000 has x * y = 900000000
    String product =
        """
        var 1..30000: x :: output_var;
        var 1..30000: y :: output_var;
        var 0..60000: s :: output_var;
        var 0..900000000: p;
        var 0..10: v;
        var bool: b;
        constraint int_times(x, y, p);
        constraint int_eq_imp(v, p, b);
        constraint int_lin_eq([1, 1, -1], [x, y, s], 0);
        """;
    String[] out = run(product + "solve maximize s;\n");
    assertEquals("x = 30000;\ny = 30000;\ns = 60000;\n----------\n==========\n", tail(out[0]));
    // the comparison holds: b forces the product into 0..10
    out = run(product + "constraint bool_eq(b, true);\nsolve maximize s;\n");
    assertTrue(tail(out[0]).endsWith("s = 11;\n----------\n==========\n"), out[0]);
    // compared with a variable that reaches the end of the range: narrowed as before, no claim
    out = run(product.replace("var 0..10: v;", "var 0..536870909: v;") + "solve maximize s;\n");
    assertFalse(out[0].endsWith("==========\n"), out[0]);
    // printed: narrowed as before, no claim
    out =
        run(
            product.replace("var 0..900000000: p;", "var 0..900000000: p :: output_var;")
                + "solve maximize s;\n");
    assertFalse(out[0].endsWith("==========\n"), out[0]);
  }

  // the last solution and the status lines
  private static String tail(String out) {
    int end = out.lastIndexOf("----------");
    int start = out.lastIndexOf("----------", end - 1);
    return out.substring(start < 0 ? 0 : start + "----------\n".length());
  }

  @Test
  void domainWhollyOutsideIntegerRangeIsRejected() throws IOException {
    String[] out = run("var 600000000..700000000: x :: output_var;\nsolve satisfy;\n");
    assertEquals("", out[0]);
    assertTrue(out[1].contains("domain 600000000..700000000 at line 1"), out[1]);
    assertTrue(out[1].contains("lies outside the integer range"), out[1]);
    assertEquals(1, lastStatus);
  }

  /**
   * A linear row over fixed variables is decided when it is posted; its sum was taken in int, so
   * 2147483647 * 1 - 2147483647 * 3 wrapped to 2 and the row failed.
   */
  @Test
  void linearRowOverFixedVariablesIsSummedWithoutOverflow() throws IOException {
    String row = "[2147483647, -2147483647], [x, y], -2147483647";
    String fixed = "var 1..1: x :: output_var;\nvar 3..3: y :: output_var;\n";
    String[] out = run(fixed + "constraint int_lin_le(" + row + ");\nsolve satisfy;\n");
    assertEquals("x = 1;\ny = 3;\n----------\n", out[0]);
    out = run(fixed + "constraint int_lin_eq(" + row + ");\nsolve satisfy;\n");
    assertTrue(out[0].endsWith("=====UNSATISFIABLE=====\n"), out[0]);
    for (String[] reified :
        new String[][] {{"eq", "false"}, {"ne", "true"}, {"lt", "true"}, {"le", "true"}}) {
      out =
          run(
              fixed
                  + "var bool: b :: output_var;\nconstraint int_lin_"
                  + reified[0]
                  + "_reif("
                  + row
                  + ", b);\nsolve satisfy;\n");
      assertEquals("x = 1;\ny = 3;\nb = " + reified[1] + ";\n----------\n", out[0], reified[0]);
    }
  }

  /**
   * A variable named twice in a linear row, as merged aliases leave it, has its coefficients added;
   * a sum beyond int wrapped around: 2^31 * i <= 2^30 accepted i = 1.
   */
  @Test
  void repeatedVariableWithCoefficientsSummingBeyondIntKeepsTheRow() throws IOException {
    String[] out =
        run(
            """
            var 0..1: i :: output_var;
            constraint int_lin_le([1073741824, 1073741824], [i, i], 1073741824);
            solve satisfy;
            """,
            "-a");
    assertEquals("i = 0;\n----------\n==========\n", out[0]);
    // the same row reached through equal subexpressions: x = y makes b1 and b2 one variable
    assertEquals(
        12,
        solveAll(
                """
                var 0..3: x :: output_var;
                var 0..3: y :: output_var;
                var bool: b1;
                var bool: b2;
                var 0..1: i1;
                var 0..1: i2;
                constraint int_eq_reif(x, y, b1);
                constraint int_eq_reif(y, x, b2);
                constraint bool2int(b1, i1);
                constraint bool2int(b2, i2);
                constraint int_lin_le([2147483647, 2147483647], [i1, i2], 2147483647);
                solve satisfy;
                """)
            .size());
  }

  /**
   * A variable declared without bounds (var int) is created over JaCoP's integer range, so a value
   * beyond the range, which MiniZinc's 64-bit integers allow, is cut off as for a narrowed domain:
   * no unsatisfiability or optimality is claimed unless the rows of the model keep the variable
   * within the range.
   */
  @Test
  void unboundedVariableBeyondTheRangeClaimsNothing() throws IOException {
    // m = 1000000000 * x is a solution of the model; JaCoP's range cuts it off
    String[] out =
        run(
            """
            var int: m :: output_var;
            var 1..2: x :: output_var;
            constraint int_lin_eq([1, -1000000000], [m, x], 0);
            solve satisfy;
            """);
    assertTrue(out[0].endsWith("=====UNKNOWN=====\n"), out[0]);
    out =
        run(
            """
            var int: m;
            var 0..2000: x :: output_var;
            constraint int_lin_eq([1, -1000000], [m, x], 0);
            constraint int_le(600, x);
            solve maximize x;
            """);
    assertTrue(out[0].contains("=====UNKNOWN====="), out[0]);
    // an array declared without bounds
    out =
        run(
            """
            array [1..2] of var int: a;
            var 1..2: x :: output_var;
            constraint int_lin_eq([1, -1000000000], [a[1], x], 0);
            solve satisfy;
            """);
    assertTrue(out[0].endsWith("=====UNKNOWN=====\n"), out[0]);

    // kept within the range by the rows and the functions of the model: the claims stand
    out =
        run(
            """
            var int: m :: output_var;
            var 0..5: x :: output_var;
            constraint int_lin_eq([1, -1], [m, x], 10);
            constraint int_le(m, 3);
            solve satisfy;
            """);
    assertEquals("=====UNSATISFIABLE=====\n", out[0]);
    out =
        run(
            """
            var int: m :: output_var;
            var 0..2: x :: output_var;
            constraint int_lin_eq([1, -1], [m, x], 10);
            solve satisfy;
            """,
            "-a");
    assertTrue(out[0].endsWith("----------\n==========\n"), out[0]);
    out =
        run(
            """
            array [1..3] of int: c = [4, 9, 2];
            var int: m :: output_var;
            var int: e;
            var int: p;
            var 1..3: i;
            var 0..5: x;
            constraint array_int_element(i, c, e);
            constraint int_times(x, x, p);
            constraint jacop_maximum(m, [e, p]);
            solve maximize m;
            """);
    assertTrue(out[0].endsWith("m = 25;\n----------\n==========\n"), out[0]);
    // a table bounds each variable by its column: -a ends with ==========
    out =
        run(
            """
            var 1..3: k :: output_var;
            var int: c :: output_var;
            constraint jacop_table_int([k, c], [1, 12000, 2, 8000, 3, 10000]);
            solve satisfy;
            """,
            "-a");
    assertEquals(3, out[0].split("----------", -1).length - 1, out[0]);
    assertTrue(out[0].endsWith("----------\n==========\n"), out[0]);
  }

  /**
   * An unbounded variable that an if-then-else makes equal to one of several values (MZNC 2025
   * work-task-variation: jacop_if_then_else_bool over int_eq_reif) lies in their hull, so the
   * optimality claim stands.
   */
  @Test
  void unboundedVariableChosenByAnIfThenElseIsBoundedByItsValues() throws IOException {
    String model =
        """
        var int: m;
        var int: cost :: output_var;
        var 0..7: y;
        var bool: c;
        var bool: b1;
        var bool: b2;
        constraint int_eq_reif(m, 0, b1);
        constraint int_eq_reif(m, y, b2);
        constraint jacop_if_then_else_bool([c, %s], [b1, b2], true);
        constraint int_lin_eq([1, -1], [cost, m], 0);
        solve maximize cost;
        """;
    String[] out = run(model.formatted("true"));
    assertTrue(out[0].endsWith("cost = 7;\n----------\n==========\n"), out[0]);
    // no condition is fixed true: when none holds, m is free, and nothing is claimed
    out = run(model.formatted("c"));
    assertTrue(out[0].contains("----------\n") && !out[0].contains("=========="), out[0]);
  }

  @Test
  void timeOutOfTheCompletionSearchIsNotReportedUnsatisfiable() throws IOException {
    // hakank's farmer_and_cows: the annotated search labels x, and the search that completes the
    // assignment of the other variables timed out below its only node. The annotated search had no
    // node left to see the time-out, so =====UNSATISFIABLE===== was printed.
    StringBuilder fzn = new StringBuilder();
    StringBuilder ys = new StringBuilder();
    StringBuilder weights = new StringBuilder();
    for (int i = 0; i < 24; i++) {
      fzn.append("var 0..1: y").append(i).append(";\n");
      ys.append("y").append(i).append(',');
      weights.append("2,");
    }
    fzn.append("var 0..0: x :: output_var;\n")
        .append("constraint int_lin_eq([")
        .append(weights)
        .append("2],[")
        .append(ys)
        .append("x],25);\n")
        .append("solve :: int_search([x],input_order,indomain_min,complete) satisfy;\n");

    // the GCD of the equality's coefficients (2) does not divide 25, which the linear system
    // detector and the parity of the equation (XorSystemDetector) prove at the root: switch both
    // off to keep the search that times out
    String out;
    System.setProperty("org.jacop.fz.lattice", "false");
    System.setProperty("org.jacop.fz.xorSystem", "false");
    try {
      out = run(fzn.toString(), "-t", "300")[0];
    } finally {
      System.clearProperty("org.jacop.fz.lattice");
      System.clearProperty("org.jacop.fz.xorSystem");
    }
    assertTrue(!out.contains("=====UNSATISFIABLE====="), out);
    assertTrue(out.contains("=====UNKNOWN====="), out);
    assertTrue(run(fzn.toString(), "-t", "300")[0].contains("=====UNSATISFIABLE====="));
  }

  @Test
  void timeOutCountsFromTheStartOfTheRun() throws InterruptedException {
    // find_missing_number_1000_380 spent minutes building the model; the time-out counted from the
    // start of the search only, so -t did not stop it.
    Options opt = new Options(new String[] {"-t", "50", "model.fzn"});
    assertTrue(!opt.timeOutPassed());
    Thread.sleep(100);
    assertTrue(opt.timeOutPassed());
    assertEquals(1, opt.getRemainingTimeOut());
    assertEquals(0, new Options(new String[] {"-s", "model.fzn"}).getRemainingTimeOut());
  }

  @Test
  void lcgSearchStopsAtTheTimeOutOfTheRun() throws IOException, ParseException {
    // LCG's deadline was the whole -t counted from the start of LCG search, so a run whose model
    // took long to read and set up overran -t by that long (nside, rcpsp-wet-diverse, the
    // ma-path-finding instances, by 1 to 3 s at 60 s); with -p every LCG thread did, and the
    // portfolio answered at -t + 2 s. Random 3-SAT just above the threshold (ratio 4.6,
    // unsatisfiable
    // with high probability) keeps LCG busy for more than 60 s. At ratio 4.3 the formula is
    // satisfiable: found after 25 s on one machine, but in under 2 s on the CI runners (and 400
    // variables were solved in 2 s once activity bumped every analysed variable).
    Random r = new Random(1);
    int n = 600;
    StringBuilder model = new StringBuilder();
    for (int i = 0; i < n; i++) {
      model.append("var bool: x").append(i).append(";\n");
    }
    for (int c = 0; c < 2760; c++) {
      StringJoiner pos = new StringJoiner(",");
      StringJoiner neg = new StringJoiner(",");
      Set<Integer> vars = new TreeSet<>();
      while (vars.size() < 3) {
        vars.add(r.nextInt(n));
      }
      for (int v : vars) {
        (r.nextBoolean() ? pos : neg).add("x" + v);
      }
      model.append("constraint bool_clause([%s],[%s]);\n".formatted(pos, neg));
    }
    model.append("solve satisfy;\n");
    Path fzn = tmp.resolve("sat3.fzn");
    Files.writeString(fzn, model.toString(), StandardCharsets.UTF_8);
    // reading the model took 6 s of the 8 s
    Options opt = new Options(new String[] {"--lcg", "-f", "-t", "8000", fzn.toString()});
    opt.startedEarlier(6000);
    long start = System.nanoTime();
    String out = runInThisJvm(opt, fzn);
    long millis = (System.nanoTime() - start) / 1_000_000;
    assertTrue(out.contains("=====UNKNOWN====="), out);
    assertTrue(millis < 5000, "the run took " + millis + " ms with 2 s left");
  }

  @Test
  void portfolioAnswersByTheTimeOutOfTheRun() {
    Options opt = new Options(new String[] {"-p", "4", "-t", "8000", "model.fzn"});
    opt.startedEarlier(6000);
    long now = System.currentTimeMillis();
    long at = Portfolio.timeOutAt(opt, now);
    assertTrue(at > now && at <= now + 2000, "time-out in " + (at - now) + " ms");
    assertEquals(0, Portfolio.timeOutAt(new Options(new String[] {"-p", "4", "model.fzn"}), now));
  }

  @Test
  void freeSearchDoesNotTakeOverFromLcgAtTheEndOfTheTimeOut() throws IOException, ParseException {
    // free search without learning took over from slow LCG free search even after the time-out:
    // the check was that some time was left, which always held. nside MEDIUM_1000_100 gave way
    // 0.5 s before -t 20 s and ended 2.9 s after it, setting up free search on 169,000 variables
    StringBuilder model = new StringBuilder();
    model.append("array[1..10] of var 1..10: x :: output_array([1..10]);\n");
    model.append("var 0..1000: o :: output_var;\n");
    for (int i = 1; i <= 10; i++) {
      for (int j = i + 1; j <= 10; j++) {
        model.append("constraint int_ne(x[%d],x[%d]);\n".formatted(i, j));
      }
    }
    model.append(
        "constraint int_lin_eq([1,2,3,4,5,6,7,8,9,10,-1],[x[1],x[2],x[3],x[4],x[5],x[6],x[7],"
            + "x[8],x[9],x[10],o],0);\nsolve minimize o;\n");
    Path fzn = tmp.resolve("late.fzn");
    Files.writeString(fzn, model.toString(), StandardCharsets.UTF_8);
    String[] args = {
      "--lcg", "-f", "-debug", "--free-config", "lcg-slow-at=0", "-t", "20000", fzn.toString()
    };
    // lcg-slow-at=0 gives way at once, after LCG's root propagation
    assertTrue(runInThisJvm(new Options(args), fzn).contains("free search without learning"));
    // with 5 % of the time-out left it is too late
    Options late = new Options(args);
    late.startedEarlier(19_000);
    String out = runInThisJvm(late, fzn);
    assertFalse(out.contains("free search without learning"), out);
  }

  @Test
  void theParseTreeIsReleasedBeforeTheSearch() throws IOException, ParseException {
    // the parser keeps the root of the parse tree on its stack while the search runs, so the
    // variable and constraint items stayed live: 29 % of the heap of nside EASY_200_50
    Path fzn = tmp.resolve("release.fzn");
    Files.writeString(
        fzn,
        "var 0..9: x :: output_var;\nvar 0..9: y;\nconstraint int_lt(x, y);\nsolve minimize y;\n",
        StandardCharsets.UTF_8);
    Options opt = new Options(new String[] {"-t", "10000", fzn.toString()});
    PrintStream originalOut = System.out;
    try (PrintStream capture =
            new PrintStream(new ByteArrayOutputStream(), true, StandardCharsets.UTF_8);
        java.io.FileInputStream input = new java.io.FileInputStream(fzn.toFile())) {
      System.setOut(capture);
      Parser parser = new Parser(input);
      parser.setOptions(opt);
      parser.model();
      SimpleNode root = (SimpleNode) parser.jjtree.rootNode();
      int kept = 0;
      for (int i = 0; i < root.jjtGetNumChildren(); i++) {
        SimpleNode item = (SimpleNode) root.jjtGetChild(i);
        if (item != null) {
          assertEquals(ParserTreeConstants.JJTMODELEND, item.getId());
          kept++;
        } else {
          assertNull(item);
        }
      }
      assertEquals(1, kept, "only the solve item is kept");
      assertNotNull(parser.getStore());
    } finally {
      System.setOut(originalOut);
    }
  }

  @Test
  void aDeclarationKeepsItsPartsOnlyWhenItIsAnAlias() throws ParseException {
    // a declaration is read once, when its variable is made; only var int: y = x is read again,
    // by symmetry breaking. The others held their annotations and array literals while the model
    // was posted: a sixth of the heap of rcpsp-wet-diverse j90_48_4
    Parser parser =
        new Parser(
            new java.io.StringReader(
                """
                var 0..9: x :: output_var;
                var 0..9: y = x;
                array [1..2] of var int: a :: output_array([1..2]) = [x, y];
                """));
    Options opt = new Options(new String[] {"model.fzn"});
    parser.setOptions(opt);
    parser.cc.setOptions(opt);
    parser.cg.setOptions(opt);
    parser.var_decl_items();
    SimpleNode items = (SimpleNode) parser.jjtree.popNode();
    assertEquals(3, items.jjtGetNumChildren());
    assertEquals(0, items.jjtGetChild(0).jjtGetNumChildren(), "x");
    assertTrue(items.jjtGetChild(1).jjtGetNumChildren() >= 2, "y = x");
    assertEquals(0, items.jjtGetChild(2).jjtGetNumChildren(), "a");
    assertNotNull(parser.dict.getVariableArray("a"));
  }

  @Test
  void aReleasedItemKeptElsewhereDoesNotReachTheOtherItems() {
    // the linear overlap rewrites kept constraint nodes by identity during the search; through
    // their parent they reached every constraint item: 21 % of the heap of ma-path-finding
    // ins_g24_p20_a10 and nside HARD_2000_500
    SimpleNode root = new SimpleNode(ParserTreeConstants.JJTMODEL);
    SimpleNode items = new SimpleNode(ParserTreeConstants.JJTCONSTRAINTITEMS);
    SimpleNode end = new SimpleNode(ParserTreeConstants.JJTMODELEND);
    SimpleNode solve = new SimpleNode(ParserTreeConstants.JJTSOLVEITEM);
    SimpleNode kept = new SimpleNode(ParserTreeConstants.JJTCONSTRAINT);
    SimpleNode other = new SimpleNode(ParserTreeConstants.JJTCONSTRAINT);
    link(root, items, 0);
    link(root, end, 1);
    link(end, solve, 0);
    link(items, kept, 0);
    link(items, other, 1);

    Solve.releaseAllBut(root, solve);

    assertNull(root.jjtGetChild(0));
    assertSame(end, root.jjtGetChild(1));
    assertSame(solve, end.jjtGetChild(0));
    // the list no longer holds the items, and a kept item does not reach its list
    assertThrows(UnsupportedOperationException.class, kept::jjtGetParent);
    for (int i = 0; i < items.jjtGetNumChildren(); i++) {
      assertNull(items.jjtGetChild(i));
    }
  }

  private static void link(SimpleNode parent, SimpleNode child, int i) {
    parent.jjtAddChild(child, i);
    child.jjtSetParent(parent);
  }

  @Test
  void aNameReadTwiceIsOneString() {
    // one String per occurrence of a name made a third of the parse tree of ma-path-finding
    // ins_g32_p20_a10 (950 MB of strings for 12 million name uses), which died at 4 GB while
    // posting
    Parser parser = new Parser(new java.io.StringReader(""));
    Token first = new Token();
    first.image = new String("X_INTRODUCED_7_".toCharArray());
    Token second = new Token();
    second.image = new String("X_INTRODUCED_7_".toCharArray());
    assertSame(parser.name(first), parser.name(second));
  }

  @Test
  void readingTheModelStopsAtTheTimeOut() throws IOException, ParseException {
    // the time-out was checked only while the constraints were posted, after the whole file was
    // read: rcpsp-wet-diverse j90_48_4 (470 MB) read for a minute and ended 18 s after -t 60 s
    StringBuilder model = new StringBuilder();
    for (int i = 0; i < 3000; i++) {
      model.append("var 0..9: x").append(i).append(";\n");
    }
    model.append("constraint int_le(x0, x1);\nsolve satisfy;\n");
    Path fzn = tmp.resolve("long.fzn");
    Files.writeString(fzn, model.toString(), StandardCharsets.UTF_8);
    Options opt = new Options(new String[] {"-t", "1000", fzn.toString()});
    opt.startedEarlier(2000);
    try (java.io.FileInputStream input = new java.io.FileInputStream(fzn.toFile())) {
      Parser parser = new Parser(input);
      parser.setOptions(opt);
      assertThrows(ModelTimeOut.class, parser::model);
      assertTrue(parser.getStore().size() < 10, parser.getStore().size() + " variables read");
    }
  }

  @Test
  void modelDetectorsStopAtTheTimeOut() throws IOException, ParseException {
    // the detectors scan every constraint of the model before any is posted, without looking at
    // the clock: on rcpsp-wet-diverse j90_48_4 the scans alone took 10 s past the time-out
    Path fzn = tmp.resolve("detect.fzn");
    Files.writeString(
        fzn,
        "var 0..9: x;\nvar 0..9: y;\nconstraint int_le(x, y);\nsolve satisfy;\n",
        StandardCharsets.UTF_8);
    Options opt = new Options(new String[] {"-t", "60000", fzn.toString()});
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8);
        java.io.FileInputStream input = new java.io.FileInputStream(fzn.toFile())) {
      System.setOut(capture);
      Parser parser = new Parser(input);
      parser.setOptions(opt);
      parser.cc.setOptions(opt);
      // the items only: model() releases them before the search
      parser.pred_decl_items();
      parser.var_decl_items();
      parser.constraint_items();
      SimpleNode tree = new SimpleNode(ParserTreeConstants.JJTMODEL);
      Node constraints = parser.jjtree.popNode();
      tree.jjtAddChild(parser.jjtree.popNode(), 0);
      tree.jjtAddChild(constraints, 1);
      opt.startedEarlier(120_000);
      Support support = parser.cc.support;
      assertThrows(ModelTimeOut.class, () -> new PartialCopyDetector(support).detect(tree));
      assertThrows(ModelTimeOut.class, () -> new AlldifferentDetector(support).detect(tree));
    } finally {
      System.setOut(originalOut);
    }
  }

  // the number of solutions of a model with -a and no symmetry breaking
  private int allSolutions(String model) throws IOException, ParseException {
    Path fzn = tmp.resolve("declared.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String out;
    try {
      out =
          runInThisJvm(new Options(new String[] {"-a", "--symmetry", "off", fzn.toString()}), fzn);
    } catch (FailException _) {
      // failed while the model was read, which Fz2jacop prints as unsatisfiable
      return 0;
    }
    return out.split("----------", -1).length - 1;
  }

  // var i = w posts i = w on the two variables before the constraint items are read; bool2int then
  // made i an alias of b, which left w free (FlatZinc mutation harness, declared-equality mutants)
  @Test
  void aVariableOfADeclaredEqualityIsNoAliasOfABoolean() throws IOException, ParseException {
    assertEquals(
        2,
        allSolutions(
            """
            var bool: b :: output_var;
            var 0..1: w :: output_var;
            var 0..1: i = w;
            constraint bool2int(b, i);
            solve satisfy;
            """));
    assertEquals(
        2,
        allSolutions(
            """
            var bool: b :: output_var;
            var 0..1: i;
            var 0..1: w :: output_var = i;
            constraint bool2int(b, i);
            solve satisfy;
            """));
  }

  // common subexpressions made s of var s = w an alias of g for int_eq(g, s), which left w free
  @Test
  void aVariableOfADeclaredEqualityIsNoCommonSubexpressionAlias()
      throws IOException, ParseException {
    assertEquals(
        2,
        allSolutions(
            """
            var 0..3: w :: output_var;
            var 0..3: s = w;
            var 0..3: g :: output_var;
            constraint int_eq(g, s);
            constraint int_le(2, s);
            solve satisfy;
            """));
  }

  // affine folding replaced z of var z = w by 2x + 1 in the rows, which left w free
  @Test
  void aVariableOfADeclaredEqualityIsNotFolded() throws IOException, ParseException {
    assertEquals(
        10,
        allSolutions(
            """
            var 0..3: x :: output_var;
            var 0..3: y :: output_var;
            var 0..20: w :: output_var;
            var 0..20: z = w;
            constraint int_lin_eq([1,-2],[z,x],1);
            constraint int_lin_le([1,1],[z,y],6);
            solve satisfy;
            """));
  }

  // ChanceSum rejects a capacity that is also one of its loads; the front end stopped on
  // chance_sum(x, ..., c) with c among x (FlatZinc mutation harness, substituted variables)
  @Test
  void aChanceSumCapacityAmongItsLoadsIsCopied() throws IOException, ParseException {
    String chance =
        "constraint jacop_chance_sum([x1,x2,%s],[1,3,2,2,0,5],[1,3,2,2,3,1],2,4,%s,3);\n";
    String vars =
        """
        var 0..2: x1 :: output_var;
        var 0..2: x2 :: output_var;
        var 0..2: x3 :: output_var;
        var 0..2: c :: output_var;
        constraint int_eq(c, x3);
        """;
    int shared = allSolutions(vars + chance.formatted("c", "c") + "solve satisfy;\n");
    int apart = allSolutions(vars + chance.formatted("x3", "c") + "solve satisfy;\n");
    assertTrue(apart > 0);
    assertEquals(apart, shared);
  }

  // ScenarioChance rejects an indicator that is also in x; bool2int(b, y) makes b and y one
  // variable, so an indicator b whose 0/1 value y is in x stopped the run
  @Test
  void aScenarioChanceIndicatorAmongItsVariablesIsCopied() throws IOException, ParseException {
    String common =
        """
        var 0..1: y :: output_var;
        var -1..2: z :: output_var;
        var bool: b :: output_var;
        var bool: d :: output_var;
        """;
    String chance = "constraint jacop_scenario_chance([y,z],[1,1,1,-1],[1,0],[3,7],10,3,[b,d]);\n";
    int shared =
        allSolutions(common + "constraint bool2int(b, y);\n" + chance + "solve satisfy;\n");
    int apart =
        allSolutions(
            common
                + """
                var 0..1: w;
                constraint bool2int(b, w);
                constraint int_le(w, y);
                constraint int_le(y, w);
                """
                + chance
                + "solve satisfy;\n");
    assertTrue(apart > 0);
    assertEquals(apart, shared);
  }

  // SubcircuitCost rejects a cost that is also a successor; jacop_subcircuit_cost(x, d, x2) stopped
  @Test
  void aSubcircuitCostThatIsASuccessorIsCopied() throws IOException, ParseException {
    String vars =
        """
        var 1..3: x1 :: output_var;
        var 1..3: x2 :: output_var;
        var 1..3: x3 :: output_var;
        var 1..3: c :: output_var;
        constraint int_eq(c, x2);
        """;
    String sub = "constraint jacop_subcircuit_cost([x1,x2,x3],[0,1,2,0,0,1,2,1,0],%s);\n";
    int shared = allSolutions(vars + sub.formatted("x2") + "solve satisfy;\n");
    int apart = allSolutions(vars + sub.formatted("c") + "solve satisfy;\n");
    assertTrue(apart > 0);
    assertEquals(apart, shared);
  }

  // bool2int(b, i) made i an alias of b without the declared domain of i, so b took 0 and 1 for
  // an i declared 1..20 or 2..20 (FlatZinc mutation harness, substituted variables)
  @Test
  void aBooleanAliasKeepsTheDomainOfItsInteger() throws IOException, ParseException {
    String model =
        """
        var %s: i;
        var bool: b :: output_var;
        constraint bool2int(b, i);
        solve satisfy;
        """;
    assertEquals(2, allSolutions(model.formatted("0..20")));
    assertEquals(1, allSolutions(model.formatted("1..20")));
    assertEquals(0, allSolutions(model.formatted("2..20")));
  }

  // the output of a run of the model with the given options, in this JVM (no watchdog)
  private static String runInThisJvm(Options opt, Path fzn) throws IOException, ParseException {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8);
        java.io.FileInputStream input = new java.io.FileInputStream(fzn.toFile())) {
      System.setOut(capture);
      Parser parser = new Parser(input);
      parser.setOptions(opt);
      parser.model();
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }

  @Test
  void proofTurnsOffSymmetryBreakingAndComponents() {
    // lex-leader constraints are not in the model a proof is checked against, and a component
    // solved before search fixes values the proof does not derive: wide-set proofs used both
    Options opt = new Options(new String[] {"--proof", "p", "--symmetry", "on", "model.fzn"});
    assertTrue(!opt.symmetry());
    assertTrue(!opt.components());
    Options plain = new Options(new String[] {"--symmetry", "on", "model.fzn"});
    assertTrue(plain.symmetry());
    assertTrue(plain.components());
  }

  @Test
  void optionValueMayFollowAnEqualsSign() {
    // --lp=off was taken for an unknown option and ignored, so the relaxation stayed on
    Options opt = new Options(new String[] {"--lp=off", "-t", "50", "--restart=luby", "model.fzn"});
    assertTrue(!opt.lp());
    assertEquals("model.fzn", opt.getFileName());
    assertTrue(new Options(new String[] {"--lp", "on", "model.fzn"}).lp());
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
  void complementarySearchPrintsEachOutputSolutionOnce() throws IOException {
    // -cs labelled every variable, also under -a, so the output solutions with x < y, where the
    // half-reified b may take both values, were printed twice (9 solutions instead of 6).
    String model =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
        var bool: b;
        constraint int_ne(x, y);
        constraint int_lt_imp(x, y, b);
        solve satisfy;
        """;
    for (String[] options : new String[][] {{"-a"}, {"-a", "-cs"}, {"-a", "-cs", "--lcg", "off"}}) {
      String out = run(model, options)[0];
      List<String> solutions =
          Arrays.stream(out.split("----------\n"))
              .map(String::strip)
              .filter(s -> s.startsWith("x ="))
              .toList();
      assertEquals(6, solutions.size(), Arrays.toString(options) + "\n" + out);
      assertEquals(6, new HashSet<>(solutions).size(), Arrays.toString(options) + "\n" + out);
      assertTrue(out.contains("=========="), Arrays.toString(options) + "\n" + out);
    }
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
  void subcircuitUnderProofKeepsSuccessorsDifferent() throws IOException {
    // Nodes 1 and 2 both have successor 3. Under --proof the subcircuit was a decomposition by
    // positions without the all-different, which accepted 1 -> 3 -> 1 with 2 -> 3, so wide-set
    // tpp and mario proved optima better than the true ones.
    String fzn =
        """
        var {3}: x1:: output_var;
        var {3}: x2:: output_var;
        var 1..3: x3:: output_var;
        array [1..3] of var int: x = [x1,x2,x3];
        constraint jacop_subcircuit(x);
        solve satisfy;
        """;
    String prefix = tmp.resolve("subcircuit").toString();
    String out = run(fzn, "--proof", prefix)[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    assertTrue(run(fzn)[0].contains("=====UNSATISFIABLE====="));
  }

  @Test
  void subcircuitUnderProofLabelsPositions() throws IOException {
    // Two cycles, 1 -> 2 -> 1 and 3 -> 4 -> 3. The --proof decomposition rules out the second cycle
    // only once the positions are fixed, and the successors leave them open. -a ignores --proof but
    // keeps its decomposition, and its search labelled the successors alone, so it printed the two
    // cycles (as the hand-over after a slow LCG did on mario_t_hard_5, which proved 4482).
    String fzn =
        """
        var {2}: x1:: output_var;
        var {1}: x2:: output_var;
        var {4}: x3:: output_var;
        var {3}: x4:: output_var;
        array [1..4] of var int: x = [x1,x2,x3,x4];
        constraint jacop_subcircuit(x);
        solve satisfy;
        """;
    String prefix = tmp.resolve("subcircuitcycles").toString();
    String all = run(fzn, "-a", "--proof", prefix)[0];
    assertTrue(all.contains("=====UNSATISFIABLE====="), all);
    String proof = run(fzn, "--proof", prefix)[0];
    assertTrue(proof.contains("=====UNSATISFIABLE====="), proof);
  }

  @Test
  void networkFlowUnderProofIsProved() throws IOException {
    // Two units from node 1 to node 3, directly at cost 5 or through node 2 at cost 1 + 1. Under
    // --proof NetworkFlow had no OPB encoding and the proof stopped; with fixed weights it is now
    // posted as its rows, which the proof derives from.
    String fzn =
        """
        var 0..2: f1:: output_var;
        var 0..2: f2:: output_var;
        var 0..2: f3:: output_var;
        var 0..20: cost:: output_var;
        array [1..3] of var int: f = [f1,f2,f3];
        array [1..3] of var int: w = [5,1,1];
        constraint jacop_networkflow([1,3,1,2,2,3],f,w,[2,0,-2],cost);
        solve minimize cost;
        """;
    String prefix = tmp.resolve("networkflow").toString();
    String out = run(fzn, "--proof", prefix)[0];
    assertTrue(out.contains("cost = 4;"), out);
    assertTrue(!out.contains("does not support"), out);
    String proof = Files.readString(Path.of(prefix + ".pbp"), StandardCharsets.UTF_8);
    assertTrue(proof.contains("conclusion BOUNDS 4 4"), proof);
  }

  @Test
  void selfCountingUnderProofIsProved() throws IOException {
    // A magic sequence of length 4: x[i] counts the value i in x, as in nmseq. The cardinality
    // detector's GCC had counters among its counted variables, which the OPB model left out, so
    // the proof stopped; under --proof those counters are now copies linked by equalities.
    StringBuilder fzn = new StringBuilder();
    StringBuilder constraints = new StringBuilder();
    for (int i = 0; i < 4; i++) {
      fzn.append("var 0..3: x").append(i).append(":: output_var;\n");
    }
    int b = 0;
    for (int i = 0; i < 4; i++) {
      StringBuilder ints = new StringBuilder();
      for (int j = 0; j < 4; j++) {
        fzn.append("var bool: b").append(b).append(";\n");
        fzn.append("var 0..1: i").append(b).append(";\n");
        constraints.append("constraint int_eq_reif(x").append(j).append(",").append(i);
        constraints.append(",b").append(b).append(");\n");
        constraints.append("constraint bool2int(b").append(b).append(",i").append(b).append(");\n");
        ints.append(j == 0 ? "" : ",").append("i").append(b);
        b++;
      }
      constraints.append("constraint int_lin_eq([1,1,1,1,-1],[").append(ints).append(",x");
      constraints.append(i).append("],0);\n");
    }
    fzn.append(constraints);
    fzn.append("solve satisfy;\n");
    String prefix = tmp.resolve("selfcounting").toString();
    String out = run(fzn.toString(), "--proof", prefix, "-debug")[0];
    assertTrue(out.contains("redundant GCC"), out);
    assertTrue(out.contains("----------"), out);
    assertTrue(!out.contains("does not support"), out);
    String proof = Files.readString(Path.of(prefix + ".pbp"), StandardCharsets.UTF_8);
    assertTrue(proof.contains("end pseudo-Boolean proof"), proof);
  }

  @Test
  void rootFailureUnderFreeSearchIsProved() throws IOException {
    // s is false (x5 <= x1 cannot hold), so r is true, and the row of r fails over the bounds:
    // the store of the LCG solver fails at the root. Under -f the root probing ran first, saw the
    // failure and reported UNSAT without the proof starting, so the proof files stayed empty
    // (MiniZinc fuzz seed 2012355).
    String fzn =
        """
        var 0..1: x1:: output_var;
        var {0,2,5,6}: x2:: output_var;
        var -5..-4: x3:: output_var;
        var -3..5: x4:: output_var;
        var 2..5: x5:: output_var;
        var -6..10: obj:: output_var;
        var bool: r:: output_var;
        var bool: s:: output_var;
        constraint bool_clause([r,s],[]);
        constraint int_lin_le_reif([-1,1,-3],[x2,x4,x3],1,r);
        constraint int_lin_le_imp([-1,1],[x1,x5],0,s);
        constraint int_lin_eq([2,-1],[x4,obj],0);
        solve maximize obj;
        """;
    String prefix = tmp.resolve("rootfailure").toString();
    String out = run(fzn, "-f", "--lcg", "on", "--proof", prefix)[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    String proof = Files.readString(Path.of(prefix + ".pbp"), StandardCharsets.UTF_8);
    assertTrue(proof.contains("conclusion BOUNDS INF INF"), proof);
    assertTrue(proof.contains("end pseudo-Boolean proof"), proof);
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

  @Test
  void largeSparseAlldiffGetsDomainConsistency() throws IOException {
    // An all_different over more than 100 variables got bounds consistency (Alldiff) whatever its
    // domains. x1 and x2 take 3 and 5 between them, a Hall set that is not an interval, so bounds
    // consistency tries x120 = 5 and x120 = 3 first. The domains are sparse, so the constraint is
    // now an Alldistinct, which removes 3 and 5 from x120 at the root (as on the successor
    // arrays of multi-agent-graph-coverage, where only domain consistency finds a solution).
    int n = 120;
    StringBuilder fzn = new StringBuilder();
    fzn.append("var {3,5}: x1:: output_var;\n").append("var {3,5}: x2:: output_var;\n");
    for (int i = 3; i < n; i++) {
      fzn.append("var {")
          .append(10 + i)
          .append(',')
          .append(1000 + i)
          .append("}: x")
          .append(i)
          .append(":: output_var;\n");
    }
    fzn.append("var {1,2,3,5}: x").append(n).append(":: output_var;\n");
    fzn.append("array [1..").append(n).append("] of var int: x = [");
    for (int i = 1; i <= n; i++) {
      fzn.append(i > 1 ? "," : "").append('x').append(i);
    }
    fzn.append("];\nconstraint jacop_alldiff(x);\n").append(hallSetSearch(n));

    // without --lcg, whose conflicts the failures statistic does not count
    String out = run(fzn.toString(), "-s", "--lcg", "off")[0];
    assertTrue(out.contains("x120 = 2;"), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
  }

  @Test
  void channelledAlldiffOverManyValuesGetsDomainConsistency() throws IOException {
    // An all_different over more than 64 dense values gets bounds consistency (Alldiff). Here 60
    // variables share 70 values, and the elements y_i = c[x_i] with y1, y2 = 1 leave x1 and x2 the
    // values 3 and 5, a Hall set that is not an interval, so bounds consistency tries x60 = 3
    // first. Elements channel from every variable and there are few spare values, so the
    // constraint is an Alldistinct, which removes 3 and 5 from x60 at the root (as with cost
    // bounds in a bottleneck assignment).
    int n = 60;
    StringBuilder c = new StringBuilder();
    for (int v = 1; v <= 70; v++) {
      c.append(v > 1 ? "," : "").append(v == 3 || v == 5 ? 1 : 2);
    }
    StringBuilder fzn = new StringBuilder("array [1..70] of int: c = [" + c + "];\n");
    for (int i = 1; i <= n; i++) {
      fzn.append("var ").append(i <= 2 ? "1" : "3").append("..70: x").append(i);
      fzn.append(":: output_var;\n");
      fzn.append("var ").append(i <= 2 ? "1..1" : "1..2").append(": y").append(i).append(";\n");
    }
    fzn.append("array [1..").append(n).append("] of var int: x = [");
    for (int i = 1; i <= n; i++) {
      fzn.append(i > 1 ? "," : "").append('x').append(i);
    }
    fzn.append("];\n");
    for (int i = 1; i <= n; i++) {
      fzn.append("constraint array_int_element(x")
          .append(i)
          .append(",c,y")
          .append(i)
          .append(");\n");
    }
    fzn.append("constraint jacop_alldiff(x);\n");
    String model = fzn + hallSetSearch(n).replace("indomain_max", "indomain_min");

    // without --lcg, whose conflicts the failures statistic does not count
    String out = run(model, "-s", "--lcg", "off")[0];
    assertTrue(out.contains("x60 = 4;"), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
    // the sum of the y_i (at least 118 over 60 distinct indices) also removes 3 and 5 at the root
    System.setProperty("org.jacop.fz.alldiffChannel", "false");
    System.setProperty("org.jacop.fz.permutationElementSums", "false");
    try {
      String bounds = run(model, "-s", "--lcg", "off")[0];
      assertTrue(bounds.contains("x60 = 4;"), bounds);
      assertTrue(!bounds.contains("%%%mzn-stat: failures=0"), bounds);
    } finally {
      System.clearProperty("org.jacop.fz.alldiffChannel");
      System.clearProperty("org.jacop.fz.permutationElementSums");
    }
    System.setProperty("org.jacop.fz.alldiffChannel", "false");
    try {
      String sums = run(model, "-s", "--lcg", "off")[0];
      assertTrue(sums.contains("x60 = 4;"), sums);
      assertTrue(sums.contains("%%%mzn-stat: failures=0"), sums);
    } finally {
      System.clearProperty("org.jacop.fz.alldiffChannel");
    }
  }

  @Test
  void channelledAlldiffWithManySpareValuesKeepsBoundsConsistency() throws IOException {
    // Three variables over 100 values: the elements channel from them, but with that many spare
    // values the rule keeps Alldiff, which tries x3 = 3 first.
    StringBuilder c = new StringBuilder();
    for (int v = 1; v <= 100; v++) {
      c.append(v > 1 ? "," : "").append(v == 3 || v == 5 ? 1 : 9);
    }
    String fzn =
        "array [1..100] of int: c = ["
            + c
            + "];\n"
            + "var 1..100: x1:: output_var;\n"
            + "var 1..100: x2:: output_var;\n"
            + "var 3..100: x3:: output_var;\n"
            + "var 1..2: y1;\n"
            + "var 1..2: y2;\n"
            + "array [1..3] of var int: x = [x1,x2,x3];\n"
            + "constraint array_int_element(x1,c,y1);\n"
            + "constraint array_int_element(x2,c,y2);\n"
            + "constraint jacop_alldiff(x);\n"
            + "solve :: int_search([x3,x2,x1],input_order,indomain_min,complete) satisfy;\n";

    String out = run(fzn, "-s", "--lcg", "off")[0];
    assertTrue(out.contains("x3 = 4;"), out);
    assertTrue(!out.contains("%%%mzn-stat: failures=0"), out);
    System.setProperty("org.jacop.fz.alldiffChannel", "loose");
    try {
      String loose = run(fzn, "-s", "--lcg", "off")[0];
      assertTrue(loose.contains("x3 = 4;"), loose);
      assertTrue(loose.contains("%%%mzn-stat: failures=0"), loose);
    } finally {
      System.clearProperty("org.jacop.fz.alldiffChannel");
    }
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
  void inverseOfItselfIsSymmetricAlldifferent() throws IOException {
    // inverse(x, x) with x1, x3 in {2, 4} and x2, x4 in {1, 3, 5}: x5 can only be a fixed point,
    // and the other four form an even cycle with two solutions. The domain consistent propagator
    // finds them without a failure.
    String fzn =
        """
        array [1..5] of var 1..5: x :: output_array([1..5]);
        constraint set_in(x[1], {2, 4});
        constraint set_in(x[3], {2, 4});
        constraint set_in(x[2], {1, 3, 5});
        constraint set_in(x[4], {1, 3, 5});
        constraint jacop_assignment(x, x, 1, 1);
        solve satisfy;
        """;
    String out = run(fzn, "-a", "-s")[0];
    assertEquals(2, out.lines().filter(l -> l.startsWith("x = ")).count(), out);
    System.setProperty("org.jacop.fz.symmetricAlldifferent", "domain");
    try {
      out = run(fzn, "-a", "-s")[0];
    } finally {
      System.clearProperty("org.jacop.fz.symmetricAlldifferent");
    }
    assertEquals(2, out.lines().filter(l -> l.startsWith("x = ")).count(), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
    // three variables that may each take either of the other two have no perfect matching, which
    // fails before search; channeling x[i] = j with x[j] = i (Assignment) needed a search node
    String odd =
        """
        array [1..3] of var 1..3: x :: output_array([1..3]);
        constraint set_in(x[1], {2, 3});
        constraint set_in(x[2], {1, 3});
        constraint set_in(x[3], {1, 2});
        constraint jacop_assignment(x, x, 1, 1);
        solve satisfy;
        """;
    out = run(odd, "-s")[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    assertFalse(out.contains("%%%mzn-stat: nodes="), out);
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
  void projectScheduleKeepsTheBooleanClausesOfLcg() throws IOException {
    // under --lcg the Boolean constraints are clauses kept for the SAT solver, not in the store;
    // the project schedule heuristic of -f checked its schedules in the store alone, printed the
    // makespan 4 that breaks the chain s3 -> s2 -> s1 the clauses force, and the search then
    // proved it optimal
    String fzn =
        """
        var 0..20: s1 :: output_var;
        var 0..20: s2 :: output_var;
        var 0..20: s3 :: output_var;
        var 0..30: m :: output_var;
        var bool: b1;
        var bool: b2;
        constraint jacop_cumulative([s1, s2, s3], [3, 2, 2], [1, 1, 1], 2);
        constraint int_lin_le([1, -1], [s1, m], -3);
        constraint int_lin_le([1, -1], [s2, m], -2);
        constraint int_lin_le([1, -1], [s3, m], -2);
        constraint int_lin_le_reif([1, -1], [s2, s1], -2, b1);
        constraint int_lin_le_reif([1, -1], [s3, s2], -2, b2);
        constraint bool_clause([b1], []);
        constraint bool_clause([b2], []);
        solve minimize m;
        """;
    String out = run(fzn, "-f", "--lcg", "on")[0];
    List<Integer> makespans =
        out.lines()
            .filter(l -> l.startsWith("m = "))
            .map(l -> Integer.parseInt(l.substring(4, l.length() - 1)))
            .toList();
    assertEquals(7, makespans.get(makespans.size() - 1), out);
    assertTrue(makespans.stream().allMatch(v -> v >= 7), out);
    assertTrue(out.contains("=========="), out);
  }

  @Test
  void inverseWithAVariableRepeatedInOneArrayIsUnsatisfiable() throws IOException {
    // jacop_assignment with ::domain posts an implied Alldistinct on f, whose constructor threw
    // IllegalArgumentException when a variable is repeated in f; the model has no solution.
    String model =
        """
        var 1..3: a :: output_var;
        var 1..3: b :: output_var;
        array [1..3] of var 1..3: g :: output_array([1..3]);
        constraint jacop_assignment(%s, %s, 1, 1)%s;
        solve satisfy;
        """;
    for (String annotation : new String[] {"", " :: domain"}) {
      for (String[] args : new String[][] {{"[a, b, a]", "g"}, {"g", "[a, b, a]"}}) {
        String[] out = run(model.formatted(args[0], args[1], annotation), "-a");
        List<String> lines = out[0].lines().filter(l -> !l.startsWith("%%")).toList();
        assertEquals(List.of("=====UNSATISFIABLE====="), lines, out[0] + out[1]);
      }
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
  void freeSearchTakesAnySearchAnnotationCount() throws IOException {
    // -f put the model's int_search annotations in one sequence of selections, which held at most
    // 128: the 2020 code-generator models have 150 and failed with "At most 128 selections".
    int n = 150;
    StringBuilder model = new StringBuilder();
    StringBuilder searches = new StringBuilder();
    StringBuilder sum = new StringBuilder();
    for (int i = 0; i < n; i++) {
      model.append("var 1..3: x").append(i).append(";\n");
      searches
          .append(i > 0 ? ", " : "")
          .append("int_search([x")
          .append(i)
          .append("], input_order, indomain_min, complete)");
      sum.append(i > 0 ? ", " : "").append('x').append(i);
    }
    model.append("var 0..1000: total :: output_var;\n");
    for (int i = 0; i + 1 < n; i++) {
      model.append("constraint int_le(x").append(i).append(", x").append(i + 1).append(");\n");
    }
    model.append("constraint int_le(2, x").append(n - 1).append(");\n");
    String ones = String.join(",", Collections.nCopies(n, "1"));
    model.append("constraint int_lin_eq([").append(ones).append(",-1], [").append(sum);
    model.append(", total], 0);\n");
    model.append("solve :: seq_search([").append(searches).append("]) minimize total;\n");

    for (String[] options :
        List.of(new String[0], new String[] {"-f"}, new String[] {"--lcg", "off", "-f"})) {
      String out = run(model.toString(), options)[0];
      // x is 1 but for the last one, which is 2
      assertTrue(
          out.contains("total = 151;") && out.contains("=========="),
          String.join(" ", options) + ": " + out);
    }
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

  /** Pigeons x0..x(n-1) in 1..holes, pairwise different by binary tables (minus one pair). */
  private static String tablePigeons(int n, int holes, boolean dropPair) {
    StringBuilder ne = new StringBuilder();
    for (int a = 1; a <= holes; a++) {
      for (int b = 1; b <= holes; b++) {
        if (a != b && !(dropPair && a == 1 && b == 2)) {
          ne.append(ne.isEmpty() ? "" : ",").append(a).append(',').append(b);
        }
      }
    }
    StringBuilder fzn = new StringBuilder();
    fzn.append("predicate jacop_table_int(array [int] of var int: x,array [int] of int: t);\n");
    fzn.append("array [1..").append(ne.toString().split(",").length).append("] of int: T = [");
    fzn.append(ne).append("];\n");
    for (int i = 0; i < n; i++) {
      fzn.append("var 1..").append(holes).append(": x").append(i).append(" :: output_var;\n");
    }
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        fzn.append("constraint jacop_table_int([x").append(i).append(",x").append(j);
        fzn.append("],T);\n");
      }
    }
    return fzn.append("solve satisfy;\n").toString();
  }

  @Test
  void binaryTablesOfDisequalitiesBecomeAllDifferent() throws IOException {
    // XCSP3 pigeonsPlus writes x_i != x_j as binary tables; read as disequalities they give an
    // all-different over 13 pigeons in 12 holes, which fails at the root; the tables alone search
    // for hours (pigeonsPlus-11-04 took millions of failures)
    String out =
        assertTimeoutPreemptively(
            Duration.ofSeconds(60),
            () -> run(tablePigeons(13, 12, false), "--lcg", "off", "-t", "5000"))[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
  }

  @Test
  void binaryTableMissingOnlySomeEqualPairsIsNoDisequality() throws IOException {
    // (1,2) is missing as well, so the table is no disequality: the solutions stay those of the
    // tables (4 pigeons in 4 holes, 1 never at a smaller index than 2: 12 of 24)
    String model = tablePigeons(4, 4, true);
    Set<String> withDetection = solveAll(model);
    System.setProperty("org.jacop.fz.alldifferent", "false");
    try {
      assertEquals(solveAll(model), withDetection);
    } finally {
      System.clearProperty("org.jacop.fz.alldifferent");
    }
    assertEquals(12, withDetection.size(), withDetection.toString());
  }

  /** The n-queens model as MiniZinc flattens abs(q[i] - q[j]) != j - i, with auxiliaries. */
  private static String flattenedQueens(int n) {
    StringBuilder fzn = new StringBuilder();
    fzn.append("array [1..").append(n).append("] of var 1..").append(n);
    fzn.append(": q :: output_array([1..").append(n).append("]);\n");
    StringBuilder cs = new StringBuilder();
    int aux = 0;
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        int c = j - i;
        String t = "t" + aux;
        String a = "a" + aux++;
        fzn.append("var ").append(1 - n).append("..").append(n - 1).append(": ").append(t);
        fzn.append(" :: var_is_introduced :: is_defined_var;\n");
        fzn.append("var ").append(domainWithout(0, n - 1, c)).append(": ").append(a);
        fzn.append(" :: var_is_introduced :: is_defined_var;\n");
        cs.append("constraint int_lin_ne([1,-1],[q[").append(i).append("],q[").append(j);
        cs.append("]],0);\n");
        cs.append("constraint int_lin_eq([1,-1,-1],[q[").append(i).append("],q[").append(j);
        cs.append("],").append(t).append("],0) :: defines_var(").append(t).append(");\n");
        cs.append("constraint int_abs(").append(t).append(',').append(a);
        cs.append(") :: defines_var(").append(a).append(");\n");
      }
    }
    return fzn.append(cs).append("solve satisfy;\n").toString();
  }

  // lo..hi without v, as a FlatZinc set
  private static String domainWithout(int lo, int hi, int v) {
    StringJoiner values = new StringJoiner(",", "{", "}");
    for (int k = lo; k <= hi; k++) {
      if (k != v) {
        values.add(Integer.toString(k));
      }
    }
    return values.toString();
  }

  @Test
  void networkFlowModesKeepTheSolutions() throws IOException {
    // the flow conservation rows, NetworkFlow, or both, with and without free search: the same
    // flows and costs on random networks
    Random rnd = new Random(20261121);
    for (int run = 0; run < 25; run++) {
      String model = randomNetworkFlow(rnd);
      Set<String> reference = null;
      for (String mode : new String[] {"global", "rows", "both", "auto"}) {
        System.setProperty("org.jacop.fz.networkFlow", mode);
        try {
          for (String[] options : new String[][] {{}, {"-f"}}) {
            Set<String> solutions = new TreeSet<>(solveAllInOrder(model, options));
            if (reference == null) {
              reference = solutions;
            }
            assertEquals(
                reference, solutions, mode + " " + Arrays.toString(options) + "\n" + model);
          }
        } finally {
          System.clearProperty("org.jacop.fz.networkFlow");
        }
      }
    }
  }

  // a network of 3 to 5 nodes and up to 7 arcs with flows 0..2 and fixed weights 0..3, balances
  // that add up to 0, as jacop_networkflow (nodes numbered from 1)
  private static String randomNetworkFlow(Random rnd) {
    int nodes = 3 + rnd.nextInt(3);
    int arcs = 3 + rnd.nextInt(5);
    StringBuilder m = new StringBuilder();
    StringJoiner arc = new StringJoiner(",", "[", "]");
    StringJoiner flows = new StringJoiner(",", "[", "]");
    StringJoiner weights = new StringJoiner(",", "[", "]");
    for (int i = 0; i < arcs; i++) {
      int from = 1 + rnd.nextInt(nodes);
      int to = 1 + (from + rnd.nextInt(nodes - 1)) % nodes;
      arc.add(from + "," + to);
      m.append("var 0..2: f").append(i).append(" :: output_var;\n");
      flows.add("f" + i);
      weights.add(Integer.toString(rnd.nextInt(4)));
    }
    int[] balance = new int[nodes];
    for (int k = 0; k < 2; k++) {
      int a = rnd.nextInt(nodes);
      int b = rnd.nextInt(nodes);
      balance[a]++;
      balance[b]--;
    }
    StringJoiner b = new StringJoiner(",", "[", "]");
    for (int v : balance) {
      b.add(Integer.toString(v));
    }
    m.append("var 0..100: cost :: output_var;\n");
    m.append("constraint jacop_networkflow(")
        .append(arc)
        .append(",")
        .append(flows)
        .append(",")
        .append(weights)
        .append(",")
        .append(b)
        .append(",cost);\n");
    m.append("solve satisfy;\n");
    return m.toString();
  }

  @Test
  void absoluteDifferencesOfQueensBecomeDiagonalCliques() throws IOException {
    // t = q[i] - q[j], a = |t| with a hole at j - i: the rewrite drops t and a, and the diagonals
    // become all-different cliques with offsets (CPAI08 queens-100: 34 s and 43,168 nodes under
    // lazy clause generation before, 0.2 s and 88 nodes after)
    String model = flattenedQueens(7);
    String debug = run(model, "-debug", "-s")[0];
    assertTrue(debug.contains("% absolute differences rewritten: 21 of 21,"), debug);
    assertEquals(3, debug.split("% alldifferent on 7 variables", -1).length - 1, debug);
    Set<String> rewritten = solveAll(model);
    System.setProperty("org.jacop.fz.absoluteDifference", "false");
    try {
      assertEquals(solveAll(model), rewritten);
    } finally {
      System.clearProperty("org.jacop.fz.absoluteDifference");
    }
    assertEquals(40, rewritten.size());
  }

  @Test
  void absoluteDifferencesOutsideCliquesStay() throws IOException {
    // three queens: no clique of five, so the two adjacent pairs, whose hole at 1 would become
    // lone disequalities, keep their auxiliaries; the corner pair excludes only the end of its
    // range, which becomes two bounds
    String debug = run(flattenedQueens(3), "-debug", "-s")[0];
    assertTrue(debug.contains("% absolute differences rewritten: 1 of 3, 0 disequalities"), debug);
  }

  @Test
  void absoluteDifferenceRewriteKeepsTheSolutions() throws IOException {
    // every rewrite is made, also one whose disequalities are in no clique
    System.setProperty("org.jacop.fz.absoluteDifference", "all");
    try {
      randomAbsoluteDifferences();
    } finally {
      System.clearProperty("org.jacop.fz.absoluteDifference");
    }
  }

  private void randomAbsoluteDifferences() throws IOException {
    // random x, y with holes, t defined by q * t + p * x - p * y = c in any term order, t and a
    // with
    // holes and narrowed bounds: the solutions over x and y are those without the rewrite
    Random rnd = new Random(20261120);
    int fired = 0;
    for (int run = 0; run < 60; run++) {
      int p = (rnd.nextBoolean() ? 1 : -1) * (1 + rnd.nextInt(2));
      int q = rnd.nextBoolean() ? p : -p;
      int c = q * (rnd.nextInt(5) - 2);
      String[] terms = {"x", "y", "t"};
      int[] coefficients = {p, -p, q};
      int r = rnd.nextInt(3);
      StringBuilder fzn = new StringBuilder();
      fzn.append("var ").append(randomSet(rnd, 0, 6)).append(": x :: output_var;\n");
      fzn.append("var ").append(randomSet(rnd, 0, 6)).append(": y :: output_var;\n");
      fzn.append("var ").append(rnd.nextBoolean() ? "-9..9" : randomSet(rnd, -9, 9));
      fzn.append(": t :: var_is_introduced;\n");
      fzn.append("var ")
          .append(rnd.nextInt(4) == 0 ? "0..9" : randomSet(rnd, 0, 1 + rnd.nextInt(9)));
      fzn.append(": a :: var_is_introduced;\n");
      StringJoiner ws = new StringJoiner(",", "[", "]");
      StringJoiner vs = new StringJoiner(",", "[", "]");
      for (int k = 0; k < 3; k++) {
        ws.add(Integer.toString(coefficients[(k + r) % 3]));
        vs.add(terms[(k + r) % 3]);
      }
      fzn.append("constraint int_lin_eq(").append(ws).append(',').append(vs).append(',');
      fzn.append(c).append(");\n");
      fzn.append("constraint int_abs(t,a);\nsolve satisfy;\n");
      String model = fzn.toString();
      if (run(model, "-debug", "-s")[0].contains("% absolute differences rewritten: 1 of 1,")) {
        fired++;
      }
      Set<String> rewritten = solveAll(model);
      System.setProperty("org.jacop.fz.absoluteDifference", "false");
      try {
        assertEquals(solveAll(model), rewritten, model);
      } finally {
        System.setProperty("org.jacop.fz.absoluteDifference", "all");
      }
    }
    assertTrue(fired >= 20, "rewritten in " + fired + " of 60");
  }

  // a random non-empty subset of lo..hi, as a FlatZinc set
  private static String randomSet(Random rnd, int lo, int hi) {
    StringJoiner values = new StringJoiner(",", "{", "}");
    int added = 0;
    for (int k = lo; k <= hi; k++) {
      if (rnd.nextInt(3) > 0 || k == hi && added == 0) {
        values.add(Integer.toString(k));
        added++;
      }
    }
    return values.toString();
  }

  /** The pigeon-hole problem as XCSP3 writes it: conflict tables over 0/1, n holes. */
  private static String conflictTableHoles(int pigeons, int n) {
    StringBuilder fzn = new StringBuilder();
    fzn.append("predicate jacop_negative_table_int(array [int] of var int: x,");
    fzn.append("array [int] of int: t);\n");
    fzn.append("array [1..").append(n).append("] of int: T1 = [0");
    fzn.append(",0".repeat(n - 1)).append("];\n");
    fzn.append("array [1..2] of int: T2 = [1,1];\n");
    for (int p = 0; p < pigeons; p++) {
      for (int h = 0; h < n; h++) {
        // a Boolean seen through its 0/1 integer, as MiniZinc flattens bool2int arguments
        fzn.append("var bool: b").append(p).append('_').append(h).append(" :: output_var;\n");
        fzn.append("var 0..1: x").append(p).append('_').append(h).append(" :: is_defined_var;\n");
      }
    }
    for (int p = 0; p < pigeons; p++) {
      for (int h = 0; h < n; h++) {
        fzn.append("constraint bool2int(b").append(p).append('_').append(h).append(",x").append(p);
        fzn.append('_').append(h).append(") :: defines_var(x").append(p).append('_').append(h);
        fzn.append(");\n");
      }
    }
    for (int p = 0; p < pigeons; p++) {
      fzn.append("constraint jacop_negative_table_int([");
      for (int h = 0; h < n; h++) {
        fzn.append(h == 0 ? "" : ",").append('x').append(p).append('_').append(h);
      }
      fzn.append("],T1);\n");
    }
    for (int h = 0; h < n; h++) {
      for (int p = 0; p < pigeons; p++) {
        for (int q = p + 1; q < pigeons; q++) {
          fzn.append("constraint jacop_negative_table_int([x").append(p).append('_');
          fzn.append(h).append(",x").append(q).append('_').append(h).append("],T2);\n");
        }
      }
    }
    return fzn.append("solve satisfy;\n").toString();
  }

  @Test
  void negativeTablesOverBooleansAreClausesTheRootRefutationSees() throws IOException {
    // hole-10 (XCSP 2017): the forbidden rows of 0/1 tables are clauses, so the model is a pure
    // clause model; its root clause refutation must run before JaSAT takes it (nothing at the
    // root woke it), and refutes the pigeons at once, where JaSAT does not finish
    String out =
        assertTimeoutPreemptively(
            Duration.ofSeconds(60),
            () ->
                run(
                    conflictTableHoles(11, 10),
                    "--lcg",
                    "on",
                    "--search-statistics",
                    "-t",
                    "5000"))[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    assertTrue(out.contains("lpRefutation=refuted"), out);
    // 3 pigeons in 3 holes, at least one hole each and none shared: 3! = 6 ways, as clauses too
    assertEquals(6, solveAll(conflictTableHoles(3, 3)).size());
    assertTrue(
        run(conflictTableHoles(3, 3), "--search-statistics")[0].contains("negativeTableClauses=1"));
    // with a constraint other than a clause the tables stay tables (StillLife: sums and tables ran
    // 1.4-3x slower with the tables as clauses)
    String mixed =
        conflictTableHoles(3, 3)
            .replace("solve ", "constraint int_lin_le([1,1],[x0_0,x1_1],2);\nsolve ");
    assertFalse(run(mixed, "--search-statistics")[0].contains("negativeTableClauses"));
    assertEquals(6, solveAll(mixed).size());
  }

  /** Courses of credit 1..n over 3 periods, as XCSP3 BACP rows: credit in the period column. */
  private static String tableCourses(int n) {
    StringBuilder par = new StringBuilder();
    StringBuilder var = new StringBuilder();
    StringBuilder con = new StringBuilder();
    par.append("predicate jacop_table_int(array [int] of var int: x,array [int] of int: t);\n");
    par.append("predicate jacop_maximum(var int: m,array [int] of var int: x);\n");
    for (int i = 1; i <= n; i++) {
      par.append("array [1..12] of int: T").append(i).append(" = [").append(i);
      par.append(",0,0,0,0,").append(i).append(",0,1,0,0,").append(i).append(",2];\n");
      for (int j = 0; j < 3; j++) {
        var.append("var 0..").append(i).append(": c").append(i).append('_').append(j);
        var.append(" :: output_var;\n");
      }
      var.append("var 0..2: p").append(i).append(" :: output_var;\n");
      con.append("constraint jacop_table_int([c").append(i).append("_0,c").append(i);
      con.append("_1,c").append(i).append("_2,p").append(i).append("],T").append(i).append(");\n");
    }
    for (int j = 0; j < 3; j++) {
      var.append("var 0..100: l").append(j).append(" :: output_var;\n");
      StringBuilder w = new StringBuilder("-1");
      StringBuilder x = new StringBuilder("l").append(j);
      for (int i = 1; i <= n; i++) {
        w.append(",1");
        x.append(",c").append(i).append('_').append(j);
      }
      con.append("constraint int_lin_eq([").append(w).append("],[").append(x).append("],0);\n");
    }
    var.append("var 0..100: m :: output_var;\n");
    con.append("constraint jacop_maximum(m,[l0,l1,l2]);\n");
    return par.append(var).append(con).append("solve minimize m;\n").toString();
  }

  @Test
  void tableColumnsWithConstantSumPostTheSum() throws IOException {
    // every row of a course table holds its credit in one period column, so the credit columns
    // sum to the credit; the sum is posted (Bacp-m1-08a, XCSP 2018, proved in 0.2 s instead of
    // not in 240 s) and the optimum stays the same
    String model = tableCourses(4);
    String out = run(model, "-s", "--search-statistics")[0];
    assertTrue(out.contains("%%%mzn-stat: impliedTableSums=1"), out);
    // credits 1..4 over 3 periods: the largest load is at least 10 / 3, so 4
    assertTrue(out.contains("m = 4;") && out.contains("=========="), out);
    System.setProperty("org.jacop.fz.tableSums", "false");
    try {
      String off = run(model, "--search-statistics")[0];
      assertFalse(off.contains("impliedTableSums"), off);
      assertTrue(off.contains("m = 4;") && off.contains("=========="), off);
    } finally {
      System.clearProperty("org.jacop.fz.tableSums");
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
  void lcgExplainsEachDeferredRemovalOnce() {
    // a magic sequence over a literal budget of 0, so no value removal is pushed to the solver:
    // a reason expanded each deferred removal at every citation, and the counts cite each other's
    // removals, which took exponential time (over a minute for 80 counts)
    int n = 80;
    StringBuilder model = new StringBuilder();
    model.append("predicate jacop_count(array [int] of var int: x, int: y, var int: c);\n");
    StringJoiner xs = new StringJoiner(",");
    for (int i = 0; i < n; i++) {
      model.append("var 0..").append(n).append(": x").append(i).append(" :: output_var;\n");
      xs.add("x" + i);
    }
    model.append("array [1..").append(n).append("] of var int: xs = [").append(xs).append("];\n");
    for (int i = 0; i < n; i++) {
      model.append("constraint jacop_count(xs, ").append(i).append(", x").append(i).append(");\n");
    }
    model.append("solve satisfy;\n");
    System.setProperty("jacop.lcg.literalBudget", "0");
    try {
      String out =
          assertTimeoutPreemptively(Duration.ofSeconds(30), () -> run(model.toString(), "--lcg"))[
              0];
      int[] x = new int[n];
      Matcher m = Pattern.compile("x(\\d+) = (\\d+);").matcher(out);
      int found = 0;
      while (m.find()) {
        x[Integer.parseInt(m.group(1))] = Integer.parseInt(m.group(2));
        found++;
      }
      assertEquals(n, found, out);
      for (int i = 0; i < n; i++) {
        int value = i;
        assertEquals(x[i], Arrays.stream(x).filter(v -> v == value).count(), out);
      }
    } finally {
      System.clearProperty("jacop.lcg.literalBudget");
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
    String out = run(model, "--lcg", "--search-statistics")[0];
    assertTrue(out.contains("x = 5;"), out);
    assertTrue(out.strip().contains("=========="), out);
    assertTrue(out.contains("lcgExplanations"), out);
    String last = out.substring(out.lastIndexOf("x = "));
    assertTrue(last.startsWith("x = 5;") && last.contains("b = true;"), last);
  }

  @Test
  void engineStatisticsArePrintedOnlyInVerboseMode() throws IOException {
    // -s prints the standard FlatZinc statistics only; the statistics of LCG, LP, presolve,
    // components, ... come with -v (or --search-statistics, or -debug) as well
    String model =
        """
        var 0..5: x :: output_var;
        var 0..5: y :: output_var;
        constraint int_lin_le([1, 1], [x, y], 7);
        constraint int_ne(x, y);
        solve maximize x;
        """;
    String plain = run(model, "-s")[0];
    assertTrue(plain.contains("%%%mzn-stat: nodes="), plain);
    for (String extra : List.of("lcg", "components", "presolve", "lp", "nodesPerSecond")) {
      assertTrue(
          plain.lines().noneMatch(l -> l.startsWith("%%%mzn-stat: " + extra)),
          extra + "\n" + plain);
    }
    for (String[] flags :
        List.of(
            new String[] {"-s", "-v"},
            new String[] {"--search-statistics"},
            new String[] {"-s", "-debug"})) {
      String out = run(model, flags)[0];
      assertTrue(out.contains("%%%mzn-stat: lpRows="), String.join(" ", flags) + "\n" + out);
      assertTrue(out.contains("%%%mzn-stat: components="), String.join(" ", flags) + "\n" + out);
    }
  }

  @Test
  void lcgSplitsLongLinearConstraintsAndKeepsTheOptimum() throws IOException {
    // --lcg splits a linear constraint of more than 20 terms into sums of blocks of about
    // sqrt(n) terms: the optimum stays that of the flat constraints and of the CP solver, and the
    // linear reasons, about 32 atoms on the flat sums of 60 terms, get below 16; sums of 25 terms
    // are split too, with shorter reasons than flat
    java.util.Random rnd = new java.util.Random(3);
    int shorter25 = 0;
    for (int run = 0; run < 16; run++) {
      int n = run < 12 ? 60 : 25;
      StringBuilder model = new StringBuilder();
      // 60 terms over 6 independent values: each x(i) equals y(i mod 6), so the search is small
      for (int j = 0; j < 6; j++) {
        model.append("var 0..2: y%d;\n".formatted(j));
      }
      for (int i = 0; i < n; i++) {
        model.append("var 0..2: x%d;\n".formatted(i));
      }
      model.append("var -1000..1000: s;\n");
      model.append("var -1000..1000: obj :: output_var;\n");
      for (int i = 0; i < n; i++) {
        model.append("constraint int_le(x%d, y%d);\n".formatted(i, i % 6));
        model.append("constraint int_le(y%d, x%d);\n".formatted(i % 6, i));
      }
      String xs =
          java.util.stream.IntStream.range(0, n)
              .mapToObj(i -> "x" + i)
              .collect(Collectors.joining(","));
      int[][] w = new int[3][n];
      for (int[] row : w) {
        for (int i = 0; i < n; i++) {
          row[i] = rnd.nextInt(9) - 3;
        }
      }
      String[] ws = new String[3];
      for (int k = 0; k < 3; k++) {
        ws[k] = Arrays.stream(w[k]).mapToObj(Integer::toString).collect(Collectors.joining(","));
      }
      model.append("constraint int_lin_le([%s], [%s], %d);\n".formatted(ws[0], xs, 20 + 3 * run));
      model.append("constraint int_lin_le([%s], [%s], %d);\n".formatted(ws[1], xs, 30 - run));
      // the objective is not a term of the long sum, which would then stay whole
      model.append("constraint int_lin_eq([%s,-1], [%s,s], 0);\n".formatted(ws[2], xs));
      model.append("constraint int_lin_eq([1,1,-1], [s,y0,obj], 0);\n");
      model.append(
          "solve :: int_search([y0,y1,y2,y3,y4,y5], input_order, indomain_min, complete) %s obj;\n"
              .formatted(run % 2 == 0 ? "minimize" : "maximize"));
      String[] flatRun =
          run(model.toString(), "--lcg", "--search-statistics", "--free-config", "lcg-split=0");
      String flat = lastObjective(flatRun);
      String cp = lastObjective(run(model.toString()));
      String[] split = run(model.toString(), "--lcg", "--search-statistics");
      assertEquals(cp, flat, model.toString());
      assertEquals(cp, lastObjective(split), model.toString());
      double splitAtoms = linearAtoms(split[0]);
      if (n == 60 && splitAtoms >= 0) {
        assertTrue(splitAtoms < 16, split[0]);
      }
      double flatAtoms = linearAtoms(flatRun[0]);
      if (n == 25 && splitAtoms >= 0 && flatAtoms >= 0) {
        shorter25 += splitAtoms < flatAtoms ? 1 : 0;
      }
    }
    assertTrue(shorter25 > 0, "no sum of 25 terms got shorter linear reasons");
  }

  @Test
  void lcgSplitsSumsOfMoreThan400TermsIntoATree() throws IOException {
    // a sum of 1,700 terms: blocks of sqrt(1700) = 42 terms and a sum of 41 blocks give
    // reasons of about 41 atoms; lcg-split-tree (the default) keeps every sum at 20 terms or
    // fewer, with the same optimum
    java.util.Random rnd = new java.util.Random(5);
    int n = 1700;
    for (int run = 0; run < 2; run++) {
      StringBuilder model = new StringBuilder();
      for (int j = 0; j < 6; j++) {
        model.append("var 0..2: y%d;%n".formatted(j));
      }
      for (int i = 0; i < n; i++) {
        model.append("var 0..2: x%d;%n".formatted(i));
      }
      model.append("var -100000..100000: s;\n");
      model.append("var -100000..100000: obj :: output_var;\n");
      for (int i = 0; i < n; i++) {
        model.append("constraint int_le(x%d, y%d);%n".formatted(i, i % 6));
        model.append("constraint int_le(y%d, x%d);%n".formatted(i % 6, i));
      }
      String xs =
          java.util.stream.IntStream.range(0, n)
              .mapToObj(i -> "x" + i)
              .collect(Collectors.joining(","));
      String ys = "y0,y1,y2,y3,y4,y5";
      String[] ws = new String[2];
      for (int k = 0; k < 2; k++) {
        ws[k] =
            java.util.stream.IntStream.range(0, n)
                .mapToObj(
                    i -> Integer.toString((1 + rnd.nextInt(3)) * (rnd.nextBoolean() ? 1 : -1)))
                .collect(Collectors.joining(","));
      }
      // one long sum: two over the same terms would also be factored (linear overlap)
      model.append(
          "constraint int_lin_le([%s], [%s], %d);%n".formatted("1,1,1,1,1,1", ys, 4 + run));
      model.append("constraint int_lin_eq([%s,-1], [%s,s], 0);%n".formatted(ws[1], xs));
      model.append("constraint int_lin_eq([1,1,-1], [s,y0,obj], 0);\n");
      model.append(
          "solve :: int_search([y0,y1,y2,y3,y4,y5], input_order, indomain_min, complete) %s obj;%n"
              .formatted(run == 0 ? "minimize" : "maximize"));
      String cp = lastObjective(run(model.toString()));
      String[] blocks =
          run(
              model.toString(),
              "--lcg",
              "--search-statistics",
              "--free-config",
              "lcg-split-tree=0");
      // the objective block bound would add six sums of about 280 terms (one per y), which
      // are not split: measure the split sums alone
      String[] tree;
      System.setProperty("org.jacop.fz.blockBound", "false");
      try {
        tree = run(model.toString(), "--lcg", "--search-statistics");
      } finally {
        System.clearProperty("org.jacop.fz.blockBound");
      }
      assertEquals(cp, lastObjective(blocks), model.toString());
      assertEquals(cp, lastObjective(tree), model.toString());
      // 1,701 terms with s: 41 blocks of up to 42 terms; in the tree 86 blocks of up to 20
      // terms, and 9 sums of up to 10 of those
      assertEquals(41, statistic(blocks[0], "lcgSplitSums"), blocks[0]);
      assertEquals(86 + 9, statistic(tree[0], "lcgSplitSums"), tree[0]);
      double treeAtoms = linearAtoms(tree[0]);
      assertTrue(treeAtoms <= 20, tree[0]);
    }
  }

  // the average atoms of the LinearInt reasons in the -s statistics, or -1 without such reasons
  @Test
  void lcgSplitsLongCountsIntoBlockCounts() throws IOException {
    // a count over 43 variables: blocks of sqrt(43) = 7 variables, the last variable joining the
    // block before it, so 6 block counts; the count with a fixed counter is split the same way.
    // The optimum stays that of plain CP and of whole counts (lcg-split-count=0)
    java.util.Random rnd = new java.util.Random(11);
    int n = 43;
    for (int run = 0; run < 4; run++) {
      StringBuilder model = new StringBuilder();
      for (int j = 0; j < 6; j++) {
        model.append("var 0..2: y%d;%n".formatted(j));
      }
      for (int i = 0; i < n; i++) {
        model.append("var 0..2: x%d;%n".formatted(i));
      }
      model.append("var 0..%d: obj :: output_var;%n".formatted(n));
      // x(i) equals y(i mod 6) or y((i + 1) mod 6), so the search is small
      for (int i = 0; i < n; i++) {
        model.append("constraint int_le(x%d, y%d);%n".formatted(i, i % 6));
        model.append("constraint int_le(y%d, x%d);%n".formatted((i + run) % 6, i));
      }
      String xs =
          java.util.stream.IntStream.range(0, n)
              .mapToObj(i -> "x" + i)
              .collect(Collectors.joining(","));
      String reversed =
          java.util.stream.IntStream.range(0, n)
              .mapToObj(i -> "x" + (n - 1 - i))
              .collect(Collectors.joining(","));
      String ws =
          java.util.stream.IntStream.range(0, n)
              .mapToObj(i -> Integer.toString(rnd.nextInt(5) - 1))
              .collect(Collectors.joining(","));
      model.append("constraint int_lin_le([%s], [%s], %d);%n".formatted(ws, xs, 20 + 5 * run));
      model.append("constraint jacop_count([%s], 1, obj);%n".formatted(xs));
      // over the list in another order, so it is not merged with the first into CountValues
      model.append("constraint jacop_count([%s], 2, %d);%n".formatted(reversed, 7 + run));
      model.append(
          "solve :: int_search([y0,y1,y2,y3,y4,y5], input_order, indomain_min, complete) %s obj;%n"
              .formatted(run % 2 == 0 ? "maximize" : "minimize"));
      String cp = lastObjective(run(model.toString()));
      String[] whole =
          run(
              model.toString(),
              "--lcg",
              "--search-statistics",
              "--free-config",
              "lcg-split-count=0");
      String[] split = run(model.toString(), "--lcg", "--search-statistics");
      assertEquals(cp, lastObjective(whole), model.toString());
      assertEquals(cp, lastObjective(split), model.toString());
      if (!cp.startsWith("=====UNSAT")) {
        assertEquals(0, statistic(whole[0], "lcgSplitCounts"), whole[0]);
        assertEquals(12, statistic(split[0], "lcgSplitCounts"), split[0]);
      }
    }
  }

  @Test
  void lcgSplitsLongCountValuesIntoBlockCountValues() throws IOException {
    // CountValues over 43 variables: 6 blocks, as for one count, with a counter per block and
    // value (24 for 4 values); with 8 values the 48 block counters would outnumber the 43
    // variables, so the constraint stays whole. The optimum stays that of plain CP and of the
    // whole constraint (lcg-split-count-values=0)
    java.util.Random rnd = new java.util.Random(13);
    int n = 43;
    int checked = 0;
    for (int run = 0; run < 4; run++) {
      int values = run < 3 ? 4 : 8;
      StringBuilder model = new StringBuilder();
      for (int j = 0; j < 6; j++) {
        model.append("var 0..3: y%d;%n".formatted(j));
      }
      for (int i = 0; i < n; i++) {
        model.append("var 0..3: x%d;%n".formatted(i));
      }
      for (int v = 0; v < values; v++) {
        model.append("var 0..%d: c%d;%n".formatted(n, v));
      }
      model.append("var 0..%d: obj :: output_var;%n".formatted(n));
      for (int i = 0; i < n; i++) {
        model.append("constraint int_le(x%d, y%d);%n".formatted(i, i % 6));
        model.append("constraint int_le(y%d, x%d);%n".formatted((i + run) % 6, i));
      }
      String xs =
          java.util.stream.IntStream.range(0, n)
              .mapToObj(i -> "x" + i)
              .collect(Collectors.joining(","));
      String ws =
          java.util.stream.IntStream.range(0, n)
              .mapToObj(i -> Integer.toString(rnd.nextInt(5) - 1))
              .collect(Collectors.joining(","));
      String vs =
          java.util.stream.IntStream.range(0, values)
              .mapToObj(Integer::toString)
              .collect(Collectors.joining(","));
      String cs =
          java.util.stream.IntStream.range(0, values)
              .mapToObj(v -> "c" + v)
              .collect(Collectors.joining(","));
      model.append("constraint int_lin_le([%s], [%s], %d);%n".formatted(ws, xs, 60 + 10 * run));
      model.append("constraint jacop_count_values([%s], [%s], [%s]);%n".formatted(xs, vs, cs));
      model.append("constraint int_le(c2, %d);%n".formatted(10 + 3 * run));
      model.append("constraint int_le(c0, %d);%n".formatted(20 + run));
      model.append("constraint int_le(c1, %d);%n".formatted(15 + run));
      model.append("constraint int_lin_eq([1,-2,-1], [obj,c1,c0], 0);\n");
      model.append(
          "solve :: int_search([y0,y1,y2,y3,y4,y5], input_order, indomain_min, complete) %s obj;%n"
              .formatted(run % 2 == 0 ? "maximize" : "minimize"));
      String cp = lastObjective(run(model.toString()));
      String[] whole =
          run(
              model.toString(),
              "--lcg",
              "--search-statistics",
              "--verbose",
              "--free-config",
              "lcg-split-count-values=0");
      String[] split = run(model.toString(), "--lcg", "--search-statistics", "--verbose");
      assertEquals(cp, lastObjective(whole), model.toString());
      assertEquals(cp, lastObjective(split), model.toString());
      if (!cp.startsWith("=====UNSAT")) {
        assertEquals(0, statistic(whole[0], "lcgSplitCounts"), whole[0]);
        assertEquals(values == 4 ? 24 : 0, statistic(split[0], "lcgSplitCounts"), split[0]);
        checked++;
      }
    }
    assertTrue(checked >= 3, "models with a solution: " + checked);
  }

  private static double linearAtoms(String out) {
    java.util.regex.Matcher m =
        java.util.regex.Pattern.compile("%% lcg LinearInt: reasons=(\\d+) .*?avgAtoms=([0-9.]+)")
            .matcher(out);
    return m.find() && Long.parseLong(m.group(1)) > 0 ? Double.parseDouble(m.group(2)) : -1;
  }

  // the last obj = value or status line printed
  private static String lastObjective(String[] out) {
    List<String> lines =
        out[0]
            .lines()
            .filter(line -> line.startsWith("obj = ") || line.startsWith("====="))
            .toList();
    return lines.isEmpty() ? "" : lines.get(lines.size() - 1);
  }

  @Test
  void lcgStatisticsAfterTheShutdownHookStopsASearchBetweenRuns() throws Exception {
    // MiniZinc stops a run at its time limit with SIGTERM, and the shutdown hook prints the
    // statistics while LcgSolver may be between two runs of its search, holding no solution;
    // LcgSolver.value then threw IllegalStateException: no solution. The clauses on p need more
    // than 1024 decisions, so a run started past its deadline stops before it finds a solution.
    StringBuilder model = new StringBuilder("array [1..4000] of var bool: p;\n");
    model.append("var 0..1: i;\nvar 3..4: o :: output_var;\n");
    for (int i = 1; i < 4000; i++) {
      model.append("constraint bool_clause([p[%d], p[%d]], []);\n".formatted(i, i + 1));
    }
    model.append(
        "constraint bool2int(p[1], i);\nconstraint int_plus(i, 3, o);\nsolve minimize o;\n");
    Path fzn = tmp.resolve("hook.fzn");
    Files.writeString(fzn, model.toString(), StandardCharsets.UTF_8);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8);
        java.io.FileInputStream input = new java.io.FileInputStream(fzn.toFile())) {
      System.setOut(capture);
      Parser parser = new Parser(input);
      parser.setOptions(new Options(new String[] {"--lcg", "-s", fzn.toString()}));
      parser.model();
      // a new run drops the solution, as each run of the search does; past its deadline it stops
      // at once without finding another
      parser.solver.lcg.sat().setDeadline(System.nanoTime());
      parser.solver.lcg.solve();
      parser.solver.printStatisticsIterrupt();
    } finally {
      System.setOut(originalOut);
    }
    String text = out.toString(StandardCharsets.UTF_8);
    assertTrue(text.contains("%%%mzn-stat: objective=3"), text);
  }

  @Test
  void lcgFreeSearchBranchesOnDefinedVariablesLast() throws IOException {
    // with -f, the activity of the variables chose the defined sum s and the objective as often as
    // the others; they follow from x, so the search now branches on x first and never needs them
    StringBuilder model =
        new StringBuilder("array [1..8] of var 0..3: x :: output_array([1..8]);\n");
    model.append("var 0..24: s :: output_var;\nvar 0..24: obj;\n");
    for (int i = 1; i < 8; i++) {
      model.append("constraint int_lin_le([-1, -1], [x[%d], x[%d]], -3);\n".formatted(i, i + 1));
      model.append("constraint int_ne(x[%d], x[%d]);\n".formatted(i, i + 1));
    }
    model.append(
        """
        constraint int_lin_eq([1, 1, 1, 1, 1, 1, 1, 1, -1], [x[1], x[2], x[3], x[4], x[5], x[6], \
        x[7], x[8], s], 0) :: defines_var(s);
        constraint int_lin_eq([2, -1, 1], [s, obj, x[1]], 0) :: defines_var(obj);
        solve minimize obj;
        """);
    String out =
        run(
            model.toString(),
            "--lcg",
            "-f",
            "--search-statistics",
            "--free-config",
            "lcg-branching=activity")[0];
    assertTrue(out.strip().contains("=========="), out);
    assertTrue(out.contains("%%%mzn-stat: lcgLateDecisions=0\n"), out);
    assertTrue(out.contains("%%%mzn-stat: objective="), out);
  }

  @Test
  void lcgFreeSearchReturnsToClausesAfterEachPruningOnSatisfactionModels() throws IOException {
    // lazy clause generation is under test: the model is not compiled to clauses
    ClausalOff.run(this::lcgFreeSearchReturnsToClausesAfterEachPruningOnSatisfactionModelsBody);
  }

  private void lcgFreeSearchReturnsToClausesAfterEachPruningOnSatisfactionModelsBody()
      throws IOException {
    // the full fixpoint of the store (#317) paid on optimisation models but not on satisfaction
    // models: nonogram non_fast_3 took 39 to 57 s instead of 4 to 6 s
    String model =
        """
        var 1..4: x :: output_var;
        var 1..4: y :: output_var;
        constraint int_lin_le([1,1], [x,y], 4);
        constraint int_ne(x, y);
        %s;
        """;
    String sat = run(model.formatted("solve satisfy"), "--lcg", "-f", "--search-statistics")[0];
    assertTrue(sat.contains("%%%mzn-stat: lcgFullFixpoint=false\n"), sat);
    String opt = run(model.formatted("solve maximize x"), "--lcg", "-f", "--search-statistics")[0];
    assertTrue(opt.contains("%%%mzn-stat: lcgFullFixpoint=true\n"), opt);
    assertTrue(opt.contains("x = 3;"), opt);
    // the annotation, followed without -f, keeps the full fixpoint
    String fixed =
        run(
            model.formatted("solve :: int_search([x,y],input_order,indomain_min,complete) satisfy"),
            "--lcg",
            "--search-statistics")[0];
    assertTrue(fixed.contains("%%%mzn-stat: lcgFullFixpoint=true\n"), fixed);
  }

  @Test
  void lcgFreeSearchBranchesOnBlockSumsLast() throws IOException {
    // --lcg splits a sum of 60 terms into block sums of about 8 terms: they follow from the terms,
    // as defined variables do, so free search branches on them last (develop-5.0 branched on them
    // like on the terms, celar SUB2 6x worse)
    StringBuilder model = new StringBuilder();
    for (int i = 0; i < 60; i++) {
      model.append("var 0..1: x%d;\n".formatted(i));
    }
    model.append("var 0..200: obj :: output_var;\n");
    String xs =
        java.util.stream.IntStream.range(0, 60)
            .mapToObj(i -> "x" + i)
            .collect(Collectors.joining(","));
    String ws =
        java.util.stream.IntStream.range(0, 60)
            .mapToObj(i -> Integer.toString(1 + i % 5))
            .collect(Collectors.joining(","));
    model.append(
        "constraint int_lin_eq([%s,-1], [%s,obj], 0) :: defines_var(obj);\n".formatted(ws, xs));
    model.append(
        "constraint int_lin_le([%s], [%s], -30);\n".formatted(ws.replaceAll("(\\d)", "-$1"), xs));
    model.append("solve minimize obj;\n");
    // without linear overlap factoring, which would make the two long sums one
    String out =
        withoutLinearOverlap(
            () ->
                run(
                    model.toString(),
                    "--lcg",
                    "-f",
                    "--search-statistics",
                    "--free-config",
                    "lcg-branching=activity")[0]);
    assertTrue(out.strip().contains("=========="), out);
    String late = out.substring(out.indexOf("lcgLateVariables=") + 17);
    // obj, the objective, and the block sums of the two long constraints
    assertTrue(Integer.parseInt(late.substring(0, late.indexOf('\n')).strip()) > 10, out);
  }

  private interface Run {
    String get() throws IOException;
  }

  private static String withoutLinearOverlap(Run run) throws IOException {
    System.setProperty("org.jacop.fz.linearOverlap", "false");
    try {
      return run.get();
    } finally {
      System.clearProperty("org.jacop.fz.linearOverlap");
    }
  }

  @Test
  void lcgSplitsTheObjectivesSum() throws IOException {
    // --lcg splits linear constraints of more than 40 terms into block sums, the objective's
    // definition too: kept whole, on-call-rostering 20s-200d took 25 to 54 s instead of 2 to 4 s
    StringBuilder model = new StringBuilder();
    for (int i = 0; i < 60; i++) {
      model.append("var 0..1: x%d;\n".formatted(i));
    }
    model.append("var 0..200: obj :: output_var;\n");
    String xs =
        java.util.stream.IntStream.range(0, 60)
            .mapToObj(i -> "x" + i)
            .collect(Collectors.joining(","));
    String ws =
        java.util.stream.IntStream.range(0, 60)
            .mapToObj(i -> Integer.toString(1 + i % 5))
            .collect(Collectors.joining(","));
    model.append(
        "constraint int_lin_eq([%s,-1], [%s,obj], 0) :: defines_var(obj);\n".formatted(ws, xs));
    model.append(
        "constraint int_lin_le([%s], [%s], -30);\n".formatted(ws.replaceAll("(\\d)", "-$1"), xs));
    model.append("solve minimize obj;\n");
    // without linear overlap factoring, which would make the two long sums one
    String out = withoutLinearOverlap(() -> run(model.toString(), "--lcg", "-f", "-debug")[0]);
    // two sums of block sums, the inequality's and the objective's equation
    long sumsOfBlocks =
        out.lines().filter(l -> l.matches("% LinearInt\\d+ : LinearInt\\( \\[ _.*")).count();
    assertEquals(2, sumsOfBlocks, out);
    assertTrue(out.contains("obj = 30;"), out);
  }

  @Test
  void lcgFreeSearchWithoutAnnotationStartsTasksBySetTimes() throws IOException {
    // a job shop without a search annotation: LCG free search branches on the task starts with set
    // times (dom/wdeg found a first makespan of 3803 against the optimum 784 on jobshop la17, and
    // branch and bound needed 273 solutions). The optimum must be the one depth-first search proves
    Random random = new Random(7);
    for (int trial = 0; trial < 5; trial++) {
      int jobs = 4;
      int machines = 3;
      int[][] duration = new int[jobs][machines];
      int[][] machine = new int[jobs][machines];
      int horizon = 0;
      for (int j = 0; j < jobs; j++) {
        List<Integer> order = new ArrayList<>(List.of(0, 1, 2));
        Collections.shuffle(order, random);
        for (int k = 0; k < machines; k++) {
          duration[j][k] = 1 + random.nextInt(6);
          machine[j][k] = order.get(k);
          horizon += duration[j][k];
        }
      }
      StringBuilder model = new StringBuilder();
      for (int j = 0; j < jobs; j++) {
        for (int k = 0; k < machines; k++) {
          model.append("var 0..%d: s%d_%d;\n".formatted(horizon, j, k));
        }
      }
      model.append("var 0..%d: obj :: output_var;\n".formatted(horizon));
      for (int j = 0; j < jobs; j++) {
        for (int k = 0; k < machines; k++) {
          String next = k + 1 < machines ? "s%d_%d".formatted(j, k + 1) : "obj";
          model.append(
              "constraint int_lin_le([1,-1], [s%d_%d,%s], %d);\n"
                  .formatted(j, k, next, -duration[j][k]));
        }
      }
      for (int m = 0; m < machines; m++) {
        List<String> starts = new ArrayList<>();
        List<String> durations = new ArrayList<>();
        for (int j = 0; j < jobs; j++) {
          for (int k = 0; k < machines; k++) {
            if (machine[j][k] == m) {
              starts.add("s%d_%d".formatted(j, k));
              durations.add(Integer.toString(duration[j][k]));
            }
          }
        }
        model.append(
            "constraint jacop_cumulative([%s], [%s], [%s], 1);\n"
                .formatted(
                    String.join(",", starts),
                    String.join(",", durations),
                    String.join(",", Collections.nCopies(starts.size(), "1"))));
      }
      model.append("solve minimize obj;\n");
      String lcg = run(model.toString(), "--lcg", "-f", "--search-statistics")[0];
      String dfs = run(model.toString(), "--search-statistics", "--default-search", "input")[0];
      assertTrue(lcg.contains("=========="), lcg);
      assertTrue(dfs.contains("=========="), dfs);
      assertEquals(lastObjective(dfs), lastObjective(lcg), lcg);
      assertEquals(jobs * machines, statistic(lcg, "lcgSetTimesStarts"), lcg);
    }
  }

  /**
   * Without a search annotation, the default search under --lcg branches in input order on a model
   * with more than 50,000 search variables: dom/wdeg scans all of them at every decision (XCSP3
   * AztecDiamond-200, 160,000 cells, had no solution in 60 s and has one in about a second).
   */
  @Test
  void lcgDefaultSearchOnManyVariablesIsInInputOrder() throws Exception {
    int n = 50_001;
    StringBuilder model = new StringBuilder();
    for (int i = 0; i < n; i++) {
      model.append("var bool: b").append(i).append(" :: output_var;\n");
    }
    for (int i = 0; i + 1 < n; i++) {
      model
          .append("constraint bool_clause([b")
          .append(i)
          .append(", b")
          .append(i + 1)
          .append("], []);\n");
    }
    model.append("solve satisfy;\n");
    // clauses alone would go to JaSAT without lazy clause generation (PureClauseModel)
    System.setProperty("org.jacop.fz.pureClauses", "false");
    String out;
    try {
      out = run(model.toString(), "--lcg", "--search-statistics")[0];
    } finally {
      System.clearProperty("org.jacop.fz.pureClauses");
    }
    assertTrue(out.contains("----------"), out.substring(Math.max(0, out.length() - 2000)));
    assertEquals(n, statistic(out, "lcgInputOrder"));
  }

  private static String lastObjective(String out) {
    int at = out.lastIndexOf("obj = ");
    assertTrue(at >= 0, out);
    return out.substring(at, out.indexOf(';', at));
  }

  private static long statistic(String out, String name) {
    String key = "%%%mzn-stat: " + name + "=";
    int at = out.indexOf(key);
    assertTrue(at >= 0, out);
    String rest = out.substring(at + key.length());
    return Long.parseLong(rest.substring(0, rest.indexOf('\n')).strip());
  }

  @Test
  void lcgFreeSearchKeepsDefinedBooleansOutOfTheLateTier() throws IOException {
    // a defined 0/1 variable is the truth of a reified constraint, a literal to branch on: on
    // skill-allocation 5d_1, where all but 126 of 12,851 variables are such reifications, the late
    // tier left activity the 126 alone and found no proof in 30 s instead of 5 s. Here b1, b2, c
    // and y are defined 0/1 variables; obj alone is late
    String model =
        """
        array [1..4] of var 1..4: x :: output_array([1..4]);
        var bool: b1;
        var bool: b2;
        var bool: b3;
        var bool: c;
        var 0..1: y;
        var 0..4: obj :: output_var;
        constraint int_eq_reif(x[1], 1, b1) :: defines_var(b1);
        constraint int_le_reif(x[2], 2, b2) :: defines_var(b2);
        constraint int_eq_reif(x[3], 3, b3) :: defines_var(b3);
        constraint array_bool_and([b1, b2], c) :: defines_var(c);
        constraint bool2int(b3, y) :: defines_var(y);
        constraint jacop_alldiff(x);
        constraint int_lin_eq([1, 1, 1, -1], [x[1], x[2], y, obj], 0) :: defines_var(obj);
        constraint bool_clause([c], []);
        solve minimize obj;
        """;
    String out =
        run(model, "--lcg", "-f", "--search-statistics", "--free-config", "lcg-branching=activity")[
            0];
    assertTrue(out.strip().contains("=========="), out);
    assertTrue(out.contains("%%%mzn-stat: objective=3\n"), out);
    assertTrue(out.contains("%%%mzn-stat: lcgLateVariables=1\n"), out);
  }

  @Test
  void lcgImpliedEqualityKeepsTheBoundsOfALargeDomain() throws IOException {
    // liner-sf-repositioning fm3_5: int_eq_imp between a variable of a million values and one of
    // four copied the holes of the small domain into the large one once b held, a != atom with its
    // own literals for each of a million values, until the heap ran out
    String model =
        """
        var 1..1000000: x :: output_var;
        var {250000, 500000, 750000, 1000000}: y;
        var bool: b;
        var 0..3000000: cost :: output_var;
        constraint int_eq_imp(x, y, b);
        constraint int_lin_eq([1, -1000000, -1], [x, b, cost], -1000000);
        solve minimize cost;
        """;
    String out = run(model, "--lcg", "--search-statistics")[0];
    String last = out.substring(out.lastIndexOf("x = "));
    assertTrue(last.startsWith("x = 250000;"), out);
    // literals created only to push a bound are released on backtrack: count the live ones
    assertTrue(stat(out, "lcgAtomLiterals") - stat(out, "lcgLiteralsReleased") < 1000, out);
  }

  private static long stat(String out, String name) {
    String from = out.substring(out.indexOf("%%%mzn-stat: " + name + "=") + name.length() + 14);
    return Long.parseLong(from.substring(0, from.indexOf('\n')).strip());
  }

  @Test
  void lcgFreeSearchWithoutAnnotationAlternatesWithDomWdeg() throws IOException {
    // cutstock without a search annotation: --lcg -f branched on activity alone and found no
    // solution in 60 s on type04_TEST9, where dom/wdeg finds one; its runs now alternate with
    // dom/wdeg on the default search variables, as they alternate with an annotation (under
    // lcg-branching=activity, the branching this test is about)
    int[] length = {45, 36, 31, 14};
    int[] demand = {3, 4, 5, 6};
    int pieces = 12;
    StringBuilder model = new StringBuilder();
    StringBuilder used = new StringBuilder();
    for (int k = 1; k <= pieces; k++) {
      model.append("var 0..1: p%d;\n".formatted(k));
      used.append("p%d, ".formatted(k));
      for (int i = 1; i <= length.length; i++) {
        model.append("var 0..6: q%d_%d;\n".formatted(k, i));
      }
    }
    model.append("var 0..%d: used :: output_var;\n".formatted(pieces));
    for (int k = 1; k <= pieces; k++) {
      StringBuilder vars = new StringBuilder();
      StringBuilder weights = new StringBuilder();
      for (int i = 1; i <= length.length; i++) {
        vars.append("q%d_%d, ".formatted(k, i));
        weights.append(length[i - 1]).append(", ");
      }
      model.append("constraint int_lin_le([%s-100], [%sp%d], 0);\n".formatted(weights, vars, k));
    }
    for (int i = 1; i <= length.length; i++) {
      StringBuilder vars = new StringBuilder();
      for (int k = 1; k <= pieces; k++) {
        vars.append(k == 1 ? "" : ", ").append("q%d_%d".formatted(k, i));
      }
      model.append(
          "constraint int_lin_le([%s], [%s], %d);\n"
              .formatted("-1, ".repeat(pieces - 1) + "-1", vars, -demand[i - 1]));
    }
    model.append(
        "constraint int_lin_eq([%s-1], [%sused], 0);\n".formatted("1, ".repeat(pieces), used));
    model.append("solve minimize used;\n");
    // proving that six pieces are optimal takes long among the symmetric pieces
    String out =
        run(
            model.toString(),
            "--lcg",
            "-f",
            "--search-statistics",
            "-t",
            "1000",
            "--free-config",
            "lcg-branching=activity")[0];
    Matcher u = Pattern.compile("used = (\\d+);").matcher(out);
    assertTrue(u.find() && Integer.parseInt(u.group(1)) >= 6, out);
    Matcher m = Pattern.compile("lcgAnnotationDecisions=(\\d+)").matcher(out);
    assertTrue(m.find() && Long.parseLong(m.group(1)) > 0, out);
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
    // the disequalities would become an all-different, with which LCG may prove at once that the
    // pigeons do not fit
    System.setProperty("org.jacop.fz.alldifferent", "false");
    try {
      // without the linear relaxation: the root clause refutation refutes it at once from the
      // cliques of the pair clauses
      String out = run(model.toString(), "--lcg", "--lp", "off", "-t", "100")[0];
      assertTrue(!out.contains("==========") && !out.contains("UNSATISFIABLE"), out);
      assertTrue(out.contains("=====UNKNOWN=====") || out.contains("TIME-OUT"), out);
    } finally {
      System.clearProperty("org.jacop.fz.alldifferent");
    }
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

  @Test
  void lcgAskedForBuildsFloatModelsAsWithoutIt() throws IOException {
    // --lcg turned the Boolean constraints into clauses and then solved the float model by search,
    // so it was a different model from the one solved without --lcg: 2 propagators instead of 3
    String model =
        """
        var 0.0..2.0: f:: output_var;
        var bool: a:: output_var;
        var bool: b:: output_var;
        var bool: c:: output_var;
        constraint bool_xor(a,b,true);
        constraint bool_clause([a,c],[b]);
        constraint float_lin_le([1.0],[f],1.5);
        solve maximize f;
        """;
    String lcg = System.clearProperty("jacop.lcg");
    try {
      String with = run(model, "--lcg", "-s", "--precision", "0.5")[0];
      String without = run(model, "--lcg", "off", "-s", "--precision", "0.5")[0];
      assertTrue(with.contains("%% --lcg ignored: the model has float variables"), with);
      for (String stat : new String[] {"propagators=", "nodes=", "propagations="}) {
        assertEquals(statLine(without, stat), statLine(with, stat), with);
      }
    } finally {
      restoreProperty("jacop.lcg", lcg);
    }
  }

  @Test
  void freeSearchKeepsThePrecisionOfFloatSearch() throws IOException {
    // golden_search: -f dropped the annotation's precision 0.001, so each better solution was a
    // few ulps better than the last; after 15 s it was at z = -17.08, far from the optimum -1
    String model =
        """
        array [1..3] of float: c = [1.0,-1.0,1.0];
        var -1.0..3.0: x:: output_var;
        var float: z:: output_var:: is_defined_var;
        var float: e ::var_is_introduced ;
        constraint float_exp(x,e);
        constraint float_lin_eq(c,[z,x,e],0.0):: defines_var(z);
        solve :: float_search([x],0.001,input_order,indomain_split,complete) maximize z;
        """;
    String out =
        assertTimeoutPreemptively(Duration.ofSeconds(60), () -> run(model, "-f", "-t", "15000")[0]);
    assertTrue(out.contains("=========="), out);
    Matcher m = Pattern.compile("(?m)^z = (\\S+);").matcher(out);
    double z = Double.NaN;
    while (m.find()) {
      z = Double.parseDouble(m.group(1));
    }
    assertEquals(-1.0, z, 0.01, out);
  }

  private static String statLine(String out, String stat) {
    return out.lines().filter(l -> l.contains("mzn-stat: " + stat)).findFirst().orElse(null);
  }

  @Test
  void lcgSolvesSetModels() throws IOException {
    String model =
        """
        var set of 1..4: s :: output_var;
        var 0..4: k;
        var bool: b2;
        var bool: b3;
        constraint set_card(s, k);
        constraint int_le(2, k);
        constraint set_in_reif(2, s, b2);
        constraint set_in_reif(3, s, b3);
        constraint bool_clause([], [b2, b3]);
        solve :: set_search([s], input_order, indomain_min, complete) satisfy;
        """;
    String out = run(model, "--lcg", "-s")[0];
    assertTrue(!out.contains("--lcg ignored"), out);
    assertTrue(out.contains("----------"), out);
    // the annotation's decisions on the set are followed, as without --lcg: 1 and 2 are put in s,
    // which leaves 3 out, then 4
    assertTrue(out.contains("s = {1, 2, 4};"), out);
    assertTrue(!out.contains("lcgAnnotationDecisions=0"), out);
  }

  /**
   * Random models over set variables (union, intersection, difference, subset, cardinality, element
   * and membership) with a weighted objective over the membership of their elements: the optimum
   * under --lcg, with every explanation checked, is the one of the search without it. The mirror of
   * a set variable once skipped a membership already fixed the other way, which lost solutions.
   */
  @Test
  void lcgOnSetModelsFindsTheOptimum() throws IOException {
    System.setProperty("jacop.lcg.check", "true");
    try {
      for (int seed = 1; seed <= 60; seed++) {
        String model = randomSetModel(new Random(seed));
        String expected = objective(run(model)[0]);
        String lcg = objective(run(model, "--lcg", "-f")[0]);
        assertEquals(expected, lcg, "seed " + seed + "\n" + model);
      }
    } finally {
      System.clearProperty("jacop.lcg.check");
    }
  }

  /**
   * Random weighted constraint networks over binary tables, as spot5: the cost of each variable is
   * paid when it takes the value 0. The clique rows of the tables enter the linear relaxation, and
   * the optimum, with every explanation checked under --lcg, is the one of an enumeration.
   */
  @Test
  void tableCliquesKeepTheOptimumOfBinaryTables() throws IOException {
    System.setProperty("jacop.lcg.check", "true");
    try {
      int withRows = 0;
      for (int seed = 1; seed <= 40; seed++) {
        Random r = new Random(seed);
        int n = 6;
        int[] w = new int[n];
        List<int[]> pairs = new ArrayList<>();
        List<boolean[][]> allowed = new ArrayList<>();
        StringBuilder m = new StringBuilder();
        for (int i = 0; i < n; i++) {
          w[i] = 1 + r.nextInt(20);
          m.append(
              "var 0..3: p%d :: output_var;\nvar bool: b%d;\nvar 0..1: c%d;\n".formatted(i, i, i));
        }
        m.append("var 0..1000: obj :: output_var;\n");
        for (int t = 0; t < 9; t++) {
          int i = r.nextInt(n);
          int j = r.nextInt(n);
          if (i == j) {
            continue;
          }
          boolean[][] ok = new boolean[4][4];
          StringBuilder tuples = new StringBuilder();
          for (int a = 0; a < 4; a++) {
            for (int b = 0; b < 4; b++) {
              ok[a][b] = a == 0 || b == 0 || r.nextInt(3) == 0;
              if (ok[a][b]) {
                tuples.append(tuples.isEmpty() ? "" : ", ").append(a).append(", ").append(b);
              }
            }
          }
          pairs.add(new int[] {i, j});
          allowed.add(ok);
          m.append("constraint jacop_table_int([p%d, p%d], [%s]);\n".formatted(i, j, tuples));
        }
        StringBuilder ws = new StringBuilder("1");
        StringBuilder cs = new StringBuilder("obj");
        for (int i = 0; i < n; i++) {
          m.append(
              "constraint int_eq_reif(p%d, 0, b%d);\nconstraint bool2int(b%d, c%d);\n"
                  .formatted(i, i, i, i));
          ws.append(", -").append(w[i]);
          cs.append(", c").append(i);
        }
        m.append("constraint int_lin_eq([%s], [%s], 0);\nsolve minimize obj;\n".formatted(ws, cs));
        int best = Integer.MAX_VALUE;
        for (int code = 0; code < 1 << 2 * n; code++) {
          int[] p = new int[n];
          int cost = 0;
          for (int i = 0; i < n; i++) {
            p[i] = code >> 2 * i & 3;
            cost += p[i] == 0 ? w[i] : 0;
          }
          boolean feasible = true;
          for (int t = 0; t < pairs.size() && feasible; t++) {
            feasible = allowed.get(t)[p[pairs.get(t)[0]]][p[pairs.get(t)[1]]];
          }
          if (feasible) {
            best = Math.min(best, cost);
          }
        }
        for (String[] options :
            List.of(
                new String[] {"--search-statistics"}, new String[] {"-f", "--search-statistics"})) {
          String out = run(m.toString(), options)[0];
          assertEquals("obj = " + best + ";", objective(out), "seed " + seed + "\n" + m);
          withRows += out.contains("lpTableCliques=0") || !out.contains("lpTableCliques=") ? 0 : 1;
        }
      }
      assertTrue(withRows > 20, "clique rows in " + withRows + " runs");
    } finally {
      System.clearProperty("jacop.lcg.check");
    }
  }

  /**
   * Every infeasible relaxation fails its node: the Farkas multipliers of the simplex carry
   * round-off far below the multipliers of the proof, and rounding them at a scale of 2^24 lost the
   * proof on most infeasible relaxations of spot5 2014-42 (2,556 of 4,063).
   */
  @Test
  void anInfeasibleRelaxationFailsItsNode() throws IOException {
    long infeasible = 0;
    for (int seed = 1; seed <= 3; seed++) {
      String model = weightedTables(new Random(seed), 40, 160);
      String out =
          run(model, "-f", "--lp", "sparse", "--search-statistics", "--free-config", "lcg-core=0")[
              0];
      assertEquals(stat(out, "lpInfeasible"), stat(out, "lpFailures"), "seed " + seed + "\n" + out);
      infeasible += stat(out, "lpInfeasible");
    }
    assertTrue(infeasible > 0, "infeasible relaxations: " + infeasible);
  }

  // n variables over 0..3 and t random binary tables that allow every pair with a 0; the cost of a
  // variable, small or in thousands as in spot5, is paid when it is 0
  private static String weightedTables(Random r, int n, int t) {
    int[] costs = {1, 2, 3, 1000, 2000, 3000, 5000};
    StringBuilder m = new StringBuilder();
    StringBuilder ws = new StringBuilder("1");
    StringBuilder cs = new StringBuilder("obj");
    for (int i = 0; i < n; i++) {
      m.append("var 0..3: p%d :: output_var;\nvar bool: b%d;\nvar 0..1: c%d;\n".formatted(i, i, i));
      ws.append(", -").append(costs[r.nextInt(costs.length)]);
      cs.append(", c").append(i);
    }
    m.append("var 0..1000000: obj :: output_var;\n");
    for (int k = 0; k < t; k++) {
      int i = r.nextInt(n);
      int j = r.nextInt(n);
      if (i == j) {
        continue;
      }
      StringBuilder tuples = new StringBuilder();
      for (int a = 0; a < 4; a++) {
        for (int b = 0; b < 4; b++) {
          if (a == 0 || b == 0 || r.nextInt(3) == 0) {
            tuples.append(tuples.isEmpty() ? "" : ", ").append(a).append(", ").append(b);
          }
        }
      }
      m.append("constraint jacop_table_int([p%d, p%d], [%s]);\n".formatted(i, j, tuples));
    }
    for (int i = 0; i < n; i++) {
      m.append(
          "constraint int_eq_reif(p%d, 0, b%d);\nconstraint bool2int(b%d, c%d);\n"
              .formatted(i, i, i, i));
    }
    m.append("constraint int_lin_eq([%s], [%s], 0);\nsolve minimize obj;\n".formatted(ws, cs));
    return m.toString();
  }

  private static String objective(String out) {
    return out.lines()
        .filter(l -> l.startsWith("obj = ") || l.contains("UNSATISFIABLE"))
        .reduce((a, b) -> b)
        .orElse(out);
  }

  private static String randomSetModel(Random r) {
    int sets = 3 + r.nextInt(4);
    StringBuilder vars = new StringBuilder();
    StringBuilder constraints = new StringBuilder();
    for (int i = 0; i < sets; i++) {
      vars.append("var set of 1..5: s%d;\n".formatted(i));
    }
    int extra = 0;
    for (int n = 2 + r.nextInt(5); n > 0; n--) {
      int a = r.nextInt(sets);
      int b = (a + 1 + r.nextInt(sets - 1)) % sets;
      int c = r.nextInt(sets);
      while (c == a || c == b) {
        c = r.nextInt(sets);
      }
      switch (r.nextInt(9)) {
        case 0 -> constraints.append("constraint set_union(s%d, s%d, s%d);\n".formatted(a, b, c));
        case 1 ->
            constraints.append("constraint set_intersect(s%d, s%d, s%d);\n".formatted(a, b, c));
        case 2 -> constraints.append("constraint set_diff(s%d, s%d, s%d);\n".formatted(a, b, c));
        case 3 -> constraints.append("constraint set_subset(s%d, s%d);\n".formatted(a, b));
        case 7 -> constraints.append("constraint set_le(s%d, s%d);\n".formatted(a, b));
        case 8 -> constraints.append("constraint set_lt(s%d, s%d);\n".formatted(a, b));
        case 4 -> {
          vars.append("var 0..5: k%d;\n".formatted(extra));
          constraints.append("constraint set_card(s%d, k%d);\n".formatted(a, extra));
          constraints.append("constraint int_le(%d, k%d);\n".formatted(r.nextInt(4), extra++));
        }
        case 5 -> {
          StringBuilder values = new StringBuilder();
          for (int j = 0; j < 3; j++) {
            Set<Integer> value = new TreeSet<>();
            for (int e = 1; e <= 5; e++) {
              if (r.nextInt(3) == 0) {
                value.add(e);
              }
            }
            values.append(j == 0 ? "{" : ", {");
            values.append(value.stream().map(String::valueOf).collect(Collectors.joining(",")));
            values.append('}');
          }
          vars.append("var 1..3: x%d;\n".formatted(extra));
          constraints.append(
              "constraint array_set_element(x%d, [%s], s%d);\n".formatted(extra++, values, a));
        }
        default -> {
          vars.append("var 1..5: x%d;\n".formatted(extra));
          constraints.append("constraint set_in(x%d, s%d);\n".formatted(extra++, a));
        }
      }
    }
    StringJoiner weights = new StringJoiner(",");
    StringJoiner terms = new StringJoiner(",");
    for (int i = 0; i < sets; i++) {
      for (int e = 1; e <= 5; e++) {
        vars.append("var bool: b%d_%d;\nvar 0..1: i%d_%d;\n".formatted(i, e, i, e));
        constraints.append("constraint set_in_reif(%d, s%d, b%d_%d);\n".formatted(e, i, i, e));
        constraints.append("constraint bool2int(b%d_%d, i%d_%d);\n".formatted(i, e, i, e));
        weights.add(String.valueOf(r.nextInt(11) - 5));
        terms.add("i%d_%d".formatted(i, e));
      }
    }
    vars.append("var -1000..1000: obj :: output_var;\n");
    constraints.append("constraint int_lin_eq([%s,-1], [%s,obj], 0);\n".formatted(weights, terms));
    return vars + constraints.toString() + "solve minimize obj;\n";
  }

  @Test
  void lcgIsOnByDefault() {
    // the test suites run with -Djacop.lcg=off; fzn-jacop runs without it
    String lcg = System.clearProperty("jacop.lcg");
    try {
      Options defaults = new Options(new String[] {"-s", "model.fzn"});
      assertTrue(defaults.lcg());
      assertTrue(new Options(new String[] {"-f", "model.fzn"}).lcg());

      assertFalse(new Options(new String[] {"--lcg", "off", "model.fzn"}).lcg());
      assertTrue(new Options(new String[] {"--lcg", "model.fzn"}).lcg());
      assertTrue(new Options(new String[] {"--lcg", "on", "-f", "model.fzn"}).lcg());
      // -sat is CP with a SAT solver for the Boolean constraints, not LCG, unless --lcg is given
      assertFalse(new Options(new String[] {"-sat", "model.fzn"}).lcg());
      assertTrue(new Options(new String[] {"-sat", "--lcg", "model.fzn"}).lcg());

      // a model loaded for the API keeps its constraints in the loaded store
      Options loaded = new Options(new String[] {"model.fzn"});
      loaded.doNotRunSearch();
      assertFalse(loaded.lcg());
      Options asked = new Options(new String[] {"--lcg", "model.fzn"});
      asked.doNotRunSearch();
      assertTrue(asked.lcg());
    } finally {
      restoreProperty("jacop.lcg", lcg);
    }
  }

  @Test
  void symmetryIsBrokenByDefaultWithoutPresolve() {
    // the test suites run with -Djacop.symmetry=presolve; fzn-jacop runs without it
    String symmetry = System.clearProperty("jacop.symmetry");
    try {
      assertTrue(new Options(new String[] {"model.fzn"}).symmetry());
      assertTrue(new Options(new String[] {"--presolve", "on", "model.fzn"}).symmetry());
      assertFalse(new Options(new String[] {"--symmetry", "off", "model.fzn"}).symmetry());

      // a model loaded for the API keeps the constraints of the model only
      Options loaded = new Options(new String[] {"model.fzn"});
      loaded.doNotRunSearch();
      assertFalse(loaded.symmetry());
      Options asked = new Options(new String[] {"--symmetry", "on", "model.fzn"});
      asked.doNotRunSearch();
      assertTrue(asked.symmetry());

      System.setProperty("jacop.symmetry", "presolve");
      assertFalse(new Options(new String[] {"model.fzn"}).symmetry());
      assertTrue(new Options(new String[] {"--presolve", "on", "model.fzn"}).symmetry());
      assertTrue(new Options(new String[] {"--symmetry", "on", "model.fzn"}).symmetry());
    } finally {
      restoreProperty("jacop.symmetry", symmetry);
    }
  }

  @Test
  void defaultLcgIsLeftOutForFloatModelsAndEnumeratesAllSolutionsOfSatisfactionProblems()
      throws IOException {
    // LCG on by default must not change how a model it cannot solve is solved: no "--lcg ignored"
    // message, and the Boolean constraints are not turned into clauses
    String floats =
        """
        var 0.0..2.0: f:: output_var;
        var bool: a:: output_var;
        var bool: b:: output_var;
        constraint bool_xor(a,b,true);
        constraint float_lin_le([1.0],[f],1.5);
        solve maximize f;
        """;
    String sat =
        """
        var bool: a:: output_var;
        var bool: b:: output_var;
        constraint bool_xor(a,b,true);
        solve satisfy;
        """;
    String lcg = System.clearProperty("jacop.lcg");
    try {
      String[] out = run(floats, "--precision", "0.5");
      assertFalse(out[0].contains("--lcg ignored"), out[0]);
      assertTrue(out[0].contains("=========="), out[0]);
      out = run(sat, "-a");
      assertFalse(out[0].contains("--lcg ignored"), out[0]);
      assertEquals(2, out[0].split("----------", -1).length - 1, out[0]);
      // asked for, LCG enumerates the solutions with blocking clauses
      out = run(sat, "-a", "--lcg");
      assertFalse(out[0].contains("--lcg ignored"), out[0]);
      assertEquals(2, out[0].split("----------", -1).length - 1, out[0]);
      assertTrue(out[0].contains("=========="), out[0]);
    } finally {
      restoreProperty("jacop.lcg", lcg);
    }
  }

  private static void restoreProperty(String name, String value) {
    if (value == null) {
      System.clearProperty(name);
    } else {
      System.setProperty(name, value);
    }
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
      lastStatus = new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.setErr(originalErr);
    }
    // IO.println ends lines with the platform separator ("\r\n" on Windows); the checks expect "\n"
    return new String[] {
      out.toString(StandardCharsets.UTF_8).replace("\r\n", "\n"),
      err.toString(StandardCharsets.UTF_8).replace("\r\n", "\n")
    };
  }

  private Set<String> solveAll(String model) throws IOException {
    return new TreeSet<>(solveAllInOrder(model));
  }

  private List<String> solveAllInOrder(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      List<String> args = new ArrayList<>(List.of("-a"));
      args.addAll(Arrays.asList(options));
      args.add(fzn.toString());
      new Fz2jacop().callMain(args.toArray(new String[0]));
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

  /**
   * Three difference constraints in a cycle over wide domains: posting them propagates until the
   * bounds have crept across the whole domain, which took 27 s with -t 2000, as prop_stress (2009)
   * never left the parser. A command-line run ends a second after its time-out, with UNKNOWN.
   */
  @Test
  void commandLineRunEndsAtItsTimeOutWhilePosting() throws IOException, InterruptedException {
    // coefficients 2 and -2, so that DifferenceBoundsDetector leaves the creeping cycle alone
    Path fzn = tmp.resolve("creep.fzn");
    Files.writeString(
        fzn,
        """
        var -500000000..500000000: x:: output_var;
        var -500000000..500000000: y:: output_var;
        var -500000000..500000000: z:: output_var;
        constraint int_lin_le([2,-2],[x,y],-1);
        constraint int_lin_le([2,-2],[y,z],-1);
        constraint int_lin_le([2,-2],[z,x],-1);
        solve satisfy;
        """);
    Path java = Path.of(System.getProperty("java.home"), "bin", "java");
    ProcessBuilder pb =
        new ProcessBuilder(
            java.toString(),
            "-cp",
            System.getProperty("java.class.path"),
            "org.jacop.fz.Fz2jacop",
            "-t",
            "1000",
            fzn.toString());
    pb.redirectErrorStream(true);
    long start = System.nanoTime();
    Process p = pb.start();
    String out = new String(p.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
    boolean ended = p.waitFor(60, TimeUnit.SECONDS);
    if (!ended) {
      p.destroyForcibly();
    }
    long millis = (System.nanoTime() - start) / 1_000_000;
    assertTrue(ended, out);
    assertTrue(out.contains("=====UNKNOWN====="), out);
    assertTrue(out.contains("%% =====TIME-OUT====="), out);
    // the time-out, the grace of a second, and the start of a JVM
    assertTrue(millis < 15_000, "ended after " + millis + " ms");
  }

  /** What the watchdog prints when it fires, by what the solver printed before. */
  @Test
  void timeLimitWatchdogPrintsWhatTheRunLacks() throws InterruptedException {
    PrintStream saved = System.out;
    try {
      assertEquals("=====UNKNOWN=====\n%% =====TIME-OUT=====\n", watchdogOutput("", true));
      assertEquals(
          "x = 1;\n----------\n%% =====TIME-OUT=====\n",
          watchdogOutput("x = 1;\n----------\n", true));
      // a run that printed its status ends on its own
      assertEquals("=====UNSATISFIABLE=====\n", watchdogOutput("=====UNSATISFIABLE=====\n", false));
      assertEquals(
          "x = 1;\n----------\n==========\n",
          watchdogOutput("x = 1;\n----------\n==========\n", false));
      // lines that only start like a solution or a status are neither
      assertEquals(
          "-- note\n== x\n=====UNKNOWN=====\n%% =====TIME-OUT=====\n",
          watchdogOutput("-- note\n== x\n", true));
      // the statistics of a search print its status as well, but the watchdog printed it already
      assertEquals(
          "=====UNKNOWN=====\n%% =====TIME-OUT=====\n%%%mzn-stat: nodes=7\n%%%mzn-stat-end\n",
          watchdogOutput(
              "",
              "",
              "=====UNKNOWN=====\n%% =====TIME-OUT=====\n%%%mzn-stat: nodes=7\n%%%mzn-stat-end\n",
              true));
      // the solution kept back without -a, unless the run printed it already as it ended
      assertEquals(
          "x = 2;\n----------\n%% =====TIME-OUT=====\n",
          watchdogOutput("", "x = 2;\n----------\n", "", true));
      assertEquals(
          "x = 2;\n----------\n%% =====TIME-OUT=====\n",
          watchdogOutput("x = 2;\n----------\n", "x = 2;\n----------\n", "", true));
    } finally {
      System.setOut(saved);
    }
  }

  // the output of a run that printed printed and was still going 0.2 s later, when a watchdog fired
  private static String watchdogOutput(String printed, boolean halts) throws InterruptedException {
    return watchdogOutput(printed, "", "", halts);
  }

  // the same, with the statistics the run would print when interrupted
  private static String watchdogOutput(
      String printed, String kept, String statistics, boolean halts) throws InterruptedException {
    ByteArrayOutputStream bytes = new ByteArrayOutputStream();
    System.setOut(new PrintStream(bytes, true, StandardCharsets.UTF_8));
    CountDownLatch halted = new CountDownLatch(1);
    TimeLimitWatchdog w =
        TimeLimitWatchdog.start(
            200 - TimeLimitWatchdog.GRACE,
            new TimeLimitWatchdog.Report() {
              @Override
              public boolean printKeptSolution() {
                System.out.print(kept);
                return !kept.isEmpty();
              }

              @Override
              public void printStatistics() {
                System.out.print(statistics);
              }
            },
            halted::countDown);
    System.out.print(printed);
    assertEquals(halts, halted.await(halts ? 5000 : 1000, TimeUnit.MILLISECONDS), printed);
    w.cancel();
    return bytes.toString(StandardCharsets.UTF_8);
  }

  @Test
  void negativeCycleOfDifferencesFailsWithoutCreeping() {
    // 2009 prop_stress in small: y0 <= y1 + 1, y1 <= x0 <= x1, x1 <= y0 - 2. Bounds propagation
    // moves the bounds by 1 each time round the cycle, 5 * 10^8 times over these domains.
    String model =
        """
        array [1..2] of int: a = [1,-1];
        var 0..500000000: y0:: output_var;
        var 0..500000000: y1:: output_var;
        var 0..500000000: x0:: output_var;
        var 0..500000000: x1:: output_var;
        constraint int_lin_le(a,[y0,y1],1);
        constraint int_le(y1,x0);
        constraint int_lin_le(a,[x0,x1],0);
        constraint int_lin_le(a,[x1,y0],-2);
        solve satisfy;
        """;
    String out = assertTimeoutPreemptively(Duration.ofSeconds(10), () -> run(model, "-s")[0]);
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
  }

  @Test
  void conditionalNegativeCycleFailsWithoutCreeping() {
    // b -> x + 1 <= y closes the cycle y + 1 <= z, z + 1 <= x of weight -3. Bounds propagation
    // after b = 1 moves the bounds by 3 each time round it, 10^8 times over these domains;
    // DifferenceCycles fails at once with the reason b = 1, so the solution has b = 0.
    String model =
        """
        array [1..2] of int: a = [1,-1];
        var 0..300000000: x:: output_var;
        var 0..300000000: y:: output_var;
        var 0..300000000: z:: output_var;
        var bool: b:: output_var;
        constraint int_lin_le_imp(a,[x,y],-1,b);
        constraint int_lin_le(a,[y,z],-1);
        constraint int_lin_le(a,[z,x],-1);
        solve :: bool_search([b],input_order,indomain_max,complete) satisfy;
        """;
    String out = assertTimeoutPreemptively(Duration.ofSeconds(10), () -> run(model, "-s")[0]);
    assertTrue(out.contains("b = false;"), out);
  }

  @Test
  void integerOfBool2intInASearchedOutputArrayPrintsAsInteger() throws IOException {
    // 2016 maximum-dag 25_01 printed distance = [..., true, ...]: the int_search over distance read
    // the array through getVariableArray, which wrote the Boolean alias of a bool2int integer into
    // the stored array, and that array is also the output array
    String model =
        """
        var bool: b :: output_var;
        var 0..1: x :: is_defined_var;
        var 0..2: y;
        array [1..2] of var int: a :: output_array([1..2]) = [x, y];
        constraint bool2int(b, x) :: defines_var(x);
        constraint int_le(y, x);
        solve :: int_search(a, input_order, indomain_max, complete) satisfy;
        """;
    for (String lcg : new String[] {"on", "off"}) {
      String out = run(model, "-a", "--lcg", lcg)[0];
      assertTrue(out.contains("a = array1d(1..2, [1, 1]);"), out);
      assertTrue(out.contains("a = array1d(1..2, [0, 0]);"), out);
      assertFalse(out.contains("true,") || out.contains("false,"), out);
    }
  }

  @Test
  void constraintNodesWithAnInlinedControlAreReleasedAfterPosting(@TempDir Path dir)
      throws Exception {
    // the constraint nodes posted with an eliminated control stayed in a map for the whole search
    // and, through their parents, the parse tree of every such constraint: 38 MB of rcpsp_max
    // psp_ubo500_33 (99,000 disjunctions b1 -> s1 + d1 <= s2, b2 -> s2 + d2 <= s1, b1 \/ b2)
    String model =
        """
        var 0..10: s1:: output_var;
        var 0..10: s2:: output_var;
        var bool: b1;
        var bool: b2;
        constraint int_lin_le_imp([1,-1],[s1,s2],-3,b1);
        constraint int_lin_le_imp([1,-1],[s2,s1],-4,b2);
        constraint bool_clause([b1,b2],[]);
        solve satisfy;
        """;
    Path file = dir.resolve("disjunction.fzn");
    Files.writeString(file, model);
    FlatzincLoader loader = new FlatzincLoader(new String[] {file.toString()});
    loader.load();
    org.jacop.fz.constraints.Support support = loader.parser.cc.support;
    java.lang.reflect.Field nodes =
        org.jacop.fz.constraints.Support.class.getDeclaredField("controlSubstitutions");
    nodes.setAccessible(true);
    assertTrue(((Map<?, ?>) nodes.get(support)).isEmpty());
    // the substitutions by eliminated control went too: only detectors read them while posting
    // (4.5 MB of rcpsp_max psp_ubo500_33 during the search)
    java.lang.reflect.Field substituted =
        org.jacop.fz.constraints.Support.class.getDeclaredField("substitutedControls");
    substituted.setAccessible(true);
    assertTrue(((Map<?, ?>) substituted.get(support)).isEmpty());
    // a control was eliminated: without enforcement inlining the store holds more constraints
    String old = System.setProperty("org.jacop.fz.enforcementInlining", "false");
    try {
      FlatzincLoader plain = new FlatzincLoader(new String[] {file.toString()});
      plain.load();
      assertTrue(
          plain.getStore().numberConstraints() > loader.getStore().numberConstraints(),
          plain.getStore().numberConstraints() + " vs " + loader.getStore().numberConstraints());
    } finally {
      if (old == null) {
        System.clearProperty("org.jacop.fz.enforcementInlining");
      } else {
        System.setProperty("org.jacop.fz.enforcementInlining", old);
      }
    }
  }

  @Test
  void unitSumsAreReleasedAfterPosting(@TempDir Path dir) throws Exception {
    // every sum of unit coefficients was kept for the AlldiffSum and partition sum detectors for
    // the whole search: 1.6 million records, 146 MB, on XCSP 2022 DiamondFree-80
    StringBuilder m = new StringBuilder();
    for (int i = 0; i < 6; i++) {
      m.append("var 0..1: b").append(i).append(":: output_var;\n");
    }
    m.append("constraint int_lin_le([1,1,1],[b0,b1,b2],2);\n");
    m.append("constraint int_lin_le([1,1,1],[b3,b4,b5],2);\n");
    m.append("constraint int_lin_le([1,1,1],[b0,b3,b5],1);\n");
    m.append("solve satisfy;\n");
    Path file = dir.resolve("sums.fzn");
    Files.writeString(file, m.toString());
    FlatzincLoader loader = new FlatzincLoader(new String[] {file.toString()});
    loader.load();
    java.lang.reflect.Field sums =
        org.jacop.fz.constraints.Support.class.getDeclaredField("unitSums");
    sums.setAccessible(true);
    assertTrue(((List<?>) sums.get(loader.parser.cc.support)).isEmpty());
  }

  /**
   * A scalar expression keeps its identifier, string or float in one field: they are the largest
   * part of the parse tree (7.8 million of XCSP 2022 RoomMate-sr0700, 48 bytes each with a field
   * for each, 40 now), and a node holds only one of them.
   */
  @Test
  void scalarExpressionsKeepOneFieldForIdentStringOrFloat() {
    List<String> fields =
        Arrays.stream(ASTScalarFlatExpr.class.getDeclaredFields())
            .filter(f -> !Modifier.isStatic(f.getModifiers()))
            .map(Field::getName)
            .sorted()
            .toList();
    assertEquals(List.of("intValue", "text", "type"), fields);
    ASTScalarFlatExpr ident = new ASTScalarFlatExpr(ParserTreeConstants.JJTSCALARFLATEXPR);
    ident.setType(2);
    ident.setIdent("x");
    assertEquals("x", ident.getIdent());
    assertNull(ident.getString());
    assertEquals(0.0, ident.getFloat());
    ASTScalarFlatExpr string = new ASTScalarFlatExpr(ParserTreeConstants.JJTSCALARFLATEXPR);
    string.setType(4);
    string.setString("\"s\"");
    assertEquals("\"s\"", string.getString());
    assertNull(string.getIdent());
    ASTScalarFlatExpr real = new ASTScalarFlatExpr(ParserTreeConstants.JJTSCALARFLATEXPR);
    real.setType(5);
    real.setFloat(2.5);
    assertEquals(2.5, real.getFloat());
    assertNull(real.getIdent());
    assertNull(real.getString());
    ASTScalarFlatExpr access = new ASTScalarFlatExpr(ParserTreeConstants.JJTSCALARFLATEXPR);
    access.setType(3);
    access.setIdent("a");
    access.setInt(4);
    assertEquals("a", access.getIdent());
    assertEquals(4, access.getInt());
  }

  /**
   * The body of a half-reified constraint of enforcement inlining is kept as a compact set, not as
   * the identity set it is collected in, whose table of 64 slots took 272 bytes for the one or two
   * variables of most bodies (53 MB of XCSP 2022 RoomMate-sr0300 while the model is read).
   */
  @Test
  @SuppressWarnings("unchecked")
  void halfReifiedBodiesOfEnforcementInliningAreCompact() throws Exception {
    Class<?> imp = Class.forName("org.jacop.fz.constraints.EnforcementInliner$Imp");
    Constructor<?> make = imp.getDeclaredConstructors()[0];
    make.setAccessible(true);
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar b = new IntVar(store, "b", 0, 1);
    Set<IntVar> collected = Collections.newSetFromMap(new IdentityHashMap<>());
    collected.add(x);
    collected.add(y);
    Object made = make.newInstance(null, b, collected);
    Method body = imp.getDeclaredMethod("body");
    body.setAccessible(true);
    Set<IntVar> kept = (Set<IntVar>) body.invoke(made);
    assertEquals(Set.of(x, y), kept);
    assertTrue(kept.contains(x));
    assertFalse(kept.contains(b));
    assertFalse(kept.getClass().getName().contains("SetFromMap"), kept.getClass().getName());
  }

  /**
   * A variable of enforcement inlining keeps its only clause without a list: a list for each
   * variable was 48 bytes of each of the 1.46 million variables of XCSP 2022 RoomMate-sr0700 while
   * the model is read. The clauses count, list and drop their dead ones as before.
   */
  @Test
  void variablesOfEnforcementInliningKeepOneClauseWithoutAList() throws Exception {
    Class<?> info = Class.forName("org.jacop.fz.constraints.EnforcementInliner$Info");
    Class<?> clause = Class.forName("org.jacop.fz.constraints.EnforcementInliner$Clause");
    Constructor<?> makeInfo = info.getDeclaredConstructor();
    makeInfo.setAccessible(true);
    Constructor<?> makeClause = clause.getDeclaredConstructors()[0];
    makeClause.setAccessible(true);
    Method add = info.getDeclaredMethod("add", clause);
    Method live = info.getDeclaredMethod("live");
    Method clauses = info.getDeclaredMethod("clauses");
    for (Method m : new Method[] {add, live, clauses}) {
      m.setAccessible(true);
    }
    Field held = info.getDeclaredField("clauses");
    held.setAccessible(true);
    Field dead = clause.getDeclaredField("dead");
    dead.setAccessible(true);

    Object v = makeInfo.newInstance();
    Object first = makeClause.newInstance(null, new ArrayList<>(), new ArrayList<>());
    Object second = makeClause.newInstance(null, new ArrayList<>(), new ArrayList<>());
    add.invoke(v, first);
    assertSame(first, held.get(v));
    assertEquals(List.of(first), clauses.invoke(v));
    add.invoke(v, second);
    assertEquals(List.of(first, second), clauses.invoke(v));
    assertEquals(2, live.invoke(v));
    dead.setBoolean(first, true);
    assertEquals(1, live.invoke(v));
    assertSame(second, held.get(v));
    dead.setBoolean(second, true);
    assertEquals(0, live.invoke(v));
    assertEquals(List.of(), clauses.invoke(v));
  }

  /**
   * A node of the parse tree keeps its id and its children only: the parser and a value of the
   * node, never read, cost 8 bytes of each of the 20 million nodes of XCSP 2022 RoomMate-sr0700
   * (163 MB while the model is read), and the parent took the 7.8 million scalar expressions from
   * 32 to 40 bytes each; the readers of a parent now get it from the root.
   */
  @Test
  void parseTreeNodesKeepNoParserOrValue() {
    List<String> fields =
        Arrays.stream(SimpleNode.class.getDeclaredFields())
            .filter(f -> !Modifier.isStatic(f.getModifiers()))
            .map(Field::getName)
            .sorted()
            .toList();
    assertEquals(List.of("children", "id"), fields);
  }

  /**
   * A node with one child keeps the child itself, not an array of one: most annotations, annotation
   * expressions and constraint items without annotations have one child, an array of 24 bytes for
   * each of about 5 million nodes of XCSP 2022 RoomMate-sr0700. The children read, copy and release
   * as before.
   */
  /**
   * A detector that reads the annotations of a constraint (the sequence detector skips the window
   * rows that define a variable) gets the constraint item with its element, since a node does not
   * keep its parent.
   */
  @Test
  void constraintElementsComeWithTheirItems(@TempDir Path dir) throws Exception {
    Path fzn = dir.resolve("items.fzn");
    Files.writeString(
        fzn,
        """
        var 0..1: a;
        var 0..1: b;
        var 0..2: s :: is_defined_var;
        constraint int_lin_eq([1,1,-1],[a,b,s],0) :: defines_var(s);
        constraint int_lin_le([1,1],[a,b],1);
        solve satisfy;
        """,
        StandardCharsets.UTF_8);
    SimpleNode tree;
    Parser parser;
    try (java.io.FileInputStream in = new java.io.FileInputStream(fzn.toFile())) {
      parser = new Parser(in);
      parser.setOptions(new Options(new String[] {fzn.toString()}));
      tree = parser.parseModel();
    }
    Method each =
        org.jacop.fz.constraints.Support.class.getDeclaredMethod(
            "forEachConstraintItem", SimpleNode.class, java.util.function.BiConsumer.class);
    each.setAccessible(true);
    List<SimpleNode> items = new ArrayList<>();
    List<ASTConstElem> elements = new ArrayList<>();
    java.util.function.BiConsumer<SimpleNode, ASTConstElem> collect =
        (item, element) -> {
          items.add(item);
          elements.add(element);
        };
    each.invoke(parser.cc.support, tree, collect);
    assertEquals(2, items.size());
    for (int i = 0; i < 2; i++) {
      assertSame(elements.get(i), items.get(i).jjtGetChild(0));
    }
    assertEquals(2, items.get(0).jjtGetNumChildren());
    assertEquals("defines_var", ((ASTAnnotation) items.get(0).jjtGetChild(1)).getAnnId());
    assertEquals(1, items.get(1).jjtGetNumChildren());
  }

  @Test
  void nodesWithOneChildKeepNoArray() {
    SimpleNode one = new SimpleNode(ParserTreeConstants.JJTANNOTATION);
    SimpleNode child = new SimpleNode(ParserTreeConstants.JJTANNEXPR);
    child.jjtSetParent(one);
    one.jjtAddChild(child, 0);
    assertFalse(one.children instanceof Node[]);
    assertEquals(1, one.jjtGetNumChildren());
    assertSame(child, one.jjtGetChild(0));
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> one.jjtGetChild(1));
    SimpleNode copy = one.copy();
    assertEquals(1, copy.jjtGetNumChildren());
    assertNotSame(child, copy.jjtGetChild(0));

    // the parser adds the children of a node from the last one
    SimpleNode three = new SimpleNode(ParserTreeConstants.JJTCONSTELEM);
    SimpleNode[] kids = new SimpleNode[3];
    for (int i = 2; i >= 0; i--) {
      kids[i] = new SimpleNode(ParserTreeConstants.JJTSCALARFLATEXPR);
      three.jjtAddChild(kids[i], i);
    }
    assertEquals(3, three.jjtGetNumChildren());
    for (int i = 0; i < 3; i++) {
      assertSame(kids[i], three.jjtGetChild(i));
    }
    // and a child added after the first one turns the child into an array
    SimpleNode two = new SimpleNode(ParserTreeConstants.JJTCONSTELEM);
    two.jjtAddChild(kids[0], 0);
    two.jjtAddChild(kids[1], 1);
    assertEquals(2, two.jjtGetNumChildren());
    assertSame(kids[0], two.jjtGetChild(0));
    assertSame(kids[1], two.jjtGetChild(1));

    // a released child keeps its place
    one.releaseChildren();
    assertEquals(1, one.jjtGetNumChildren());
    assertNull(one.jjtGetChild(0));
    three.releaseChild(1);
    assertEquals(3, three.jjtGetNumChildren());
    assertNull(three.jjtGetChild(1));
    assertSame(kids[2], three.jjtGetChild(2));
  }

  @Test
  void channelMapsAreReleasedAfterPosting(@TempDir Path dir) throws Exception {
    // the int_eq_reif and int_eq_imp constraints collected for the channels were kept for the
    // whole search: 115 MB on XCSP 2022 RoomMate-sr0700 (490,000 implications)
    String model =
        """
        var 1..3: x:: output_var;
        var bool: a;
        var bool: b;
        var bool: c;
        var bool: d;
        constraint int_eq_reif(x,1,a);
        constraint int_eq_reif(x,2,b);
        constraint int_eq_imp(x,2,c);
        constraint int_eq_imp(x,3,d);
        constraint bool_clause([a,b,c,d],[]);
        solve satisfy;
        """;
    Path file = dir.resolve("channels.fzn");
    Files.writeString(file, model);
    FlatzincLoader loader = new FlatzincLoader(new String[] {file.toString()});
    loader.load();
    org.jacop.fz.constraints.Support support = loader.parser.cc.support;
    Class<?> channelMap = Class.forName("org.jacop.fz.constraints.ChannelMap");
    java.lang.reflect.Field cs = channelMap.getDeclaredField("cs");
    java.lang.reflect.Field byBoolean = channelMap.getDeclaredField("byBoolean");
    cs.setAccessible(true);
    byBoolean.setAccessible(true);
    for (String name : new String[] {"reif", "imply"}) {
      java.lang.reflect.Field f = org.jacop.fz.constraints.Support.class.getDeclaredField(name);
      f.setAccessible(true);
      Object map = f.get(support);
      assertTrue(((Map<?, ?>) cs.get(map)).isEmpty(), name);
      assertTrue(((Map<?, ?>) byBoolean.get(map)).isEmpty(), name);
    }
  }

  @Test
  void tablesOverOneKeyedRelationShareTheirBinaryParts(@TempDir Path dir) throws Exception {
    // a table whose first column is a key is posted as one binary table per other column; over a
    // relation of 80,000 words, 60 such tables built 300 binary tables with their own tuples and
    // index (5.8 GB). The tables over the same relation share the binary part of each column.
    StringBuilder m = new StringBuilder("array [1..24] of int: t = [");
    int[][] rows = {
      {1, 0, 2, 1}, {2, 1, 0, 2}, {3, 2, 2, 0}, {4, 0, 1, 1}, {5, 1, 1, 2}, {6, 2, 0, 0}
    };
    StringJoiner cells = new StringJoiner(",");
    for (int[] r : rows) {
      for (int v : r) {
        cells.add(Integer.toString(v));
      }
    }
    m.append(cells).append("];\n");
    for (int i = 0; i < 3; i++) {
      m.append("var 1..6: w").append(i).append(":: output_var;\n");
    }
    for (int j = 0; j < 9; j++) {
      m.append("var 0..2: l").append(j).append(":: output_var;\n");
    }
    for (int i = 0; i < 3; i++) {
      m.append("constraint jacop_table_int([w").append(i);
      for (int k = 0; k < 3; k++) {
        m.append(",l").append((i * 2 + k) % 9);
      }
      m.append("],t);\n");
    }
    m.append("solve satisfy;\n");
    Path file = dir.resolve("words.fzn");
    Files.writeString(file, m.toString());
    PrintStream out = System.out;
    Store store;
    try (PrintStream quiet = new PrintStream(OutputStream.nullOutputStream())) {
      System.setOut(quiet);
      FlatzincLoader loader = new FlatzincLoader(new String[] {file.toString()});
      loader.load();
      store = loader.getStore();
    } finally {
      System.setOut(out);
    }
    java.lang.reflect.Field shared = HybridTable.class.getDeclaredField("shared");
    shared.setAccessible(true);
    List<HybridTable> binary = new ArrayList<>();
    Set<Object> indexes = Collections.newSetFromMap(new IdentityHashMap<>());
    for (org.jacop.constraints.Constraint c : store.getConstraints()) {
      if (c instanceof HybridTable h && h.columnCount() == 2) {
        binary.add(h);
        indexes.add(shared.get(h));
      }
    }
    // the last letter is a function of the first one, so each table has two parts with the word
    assertEquals(6, binary.size(), binary.toString());
    assertEquals(2, indexes.size());
    for (HybridTable h : binary) {
      assertEquals(0, h.keyColumn());
    }
  }

  @Test
  void tablesOfSevenColumnsOverOneRelationShareTheirCells(@TempDir Path dir) throws Exception {
    // only tables of at most TableCliques.MAX_ARITY (6) columns shared their tuples:
    // pigeonsPlus-08-08 (XCSP 2017) posts one table of 5.8 million rows on eight lists of eight
    // variables, and with its own tuples and cells for each table it ran out of 4 GB. The rows here
    // (sum divisible by 3) have no exact reformulation.
    StringJoiner cells = new StringJoiner(",");
    int count = 0;
    for (int code = 0; code < 2187; code++) {
      int sum = 0;
      StringJoiner row = new StringJoiner(",");
      for (int i = 0, rest = code; i < 7; i++, rest /= 3) {
        sum += rest % 3;
        row.add(Integer.toString(rest % 3));
      }
      if (sum % 3 == 0) {
        cells.add(row.toString());
        count++;
      }
    }
    StringBuilder m = new StringBuilder();
    m.append("array [1..").append(7 * count).append("] of int: t = [").append(cells).append("];\n");
    for (int i = 0; i < 21; i++) {
      m.append("var 0..2: x").append(i).append(":: output_var;\n");
    }
    m.append("constraint jacop_table_int([x0,x1,x2,x3,x4,x5,x6],t);\n");
    m.append("constraint jacop_table_int([x7,x8,x9,x10,x11,x12,x13],t);\n");
    // the same rows written in the constraint, read from the packed array literal
    m.append("constraint jacop_table_int([x14,x15,x16,x17,x18,x19,x20],[")
        .append(cells)
        .append("]);\n");
    m.append("solve satisfy;\n");
    Path file = dir.resolve("tables.fzn");
    Files.writeString(file, m.toString());
    PrintStream out = System.out;
    Store store;
    try (PrintStream quiet = new PrintStream(OutputStream.nullOutputStream())) {
      System.setOut(quiet);
      FlatzincLoader loader = new FlatzincLoader(new String[] {file.toString()});
      loader.load();
      store = loader.getStore();
    } finally {
      System.setOut(out);
    }
    java.lang.reflect.Field shared = HybridTable.class.getDeclaredField("shared");
    shared.setAccessible(true);
    List<HybridTable> tables = new ArrayList<>();
    Set<Object> indexes = Collections.newSetFromMap(new IdentityHashMap<>());
    for (org.jacop.constraints.Constraint c : store.getConstraints()) {
      if (c instanceof HybridTable h && h.columnCount() == 7) {
        tables.add(h);
        indexes.add(shared.get(h));
      }
    }
    assertEquals(3, tables.size());
    assertEquals(1, indexes.size());
  }

  @Test
  void arrayLiteralsOfIntLiteralsArePackedAndReadAsNodes() {
    // the parser keeps an array literal of int literals as one int[] (a table of pigeonsPlus-11-07
    // has 70 million entries, 3.4 GB as nodes); its children are read as int literal nodes
    SimpleNode array = new SimpleNode(ParserTreeConstants.JJTARRAYLITERAL);
    array.setPackedInts(new int[] {3, -1, 7});
    assertEquals(3, array.jjtGetNumChildren());
    ASTScalarFlatExpr second = (ASTScalarFlatExpr) array.jjtGetChild(1);
    assertEquals(0, second.getType());
    assertEquals(-1, second.getInt());
    SimpleNode copy = array.copy();
    assertSame(array.packedInts(), copy.packedInts());
    // a change of a child turns the packed children into nodes
    ASTScalarFlatExpr replaced = SimpleNode.intLiteral(5);
    array.jjtAddChild(replaced, 2);
    assertNull(array.packedInts());
    assertEquals(3, ((ASTScalarFlatExpr) array.jjtGetChild(0)).getInt());
    assertSame(replaced, array.jjtGetChild(2));
    assertEquals(7, ((ASTScalarFlatExpr) copy.jjtGetChild(2)).getInt());
  }

  @Test
  void arrayLiteralsMixingIntLiteralsWithOtherElementsKeepTheirOrder() throws IOException {
    // ints then a variable then ints, negative ints, sets that start with an int literal
    String fzn =
        """
        array [1..4] of int: c = [2,-1,3,1];
        array [1..2] of set of int: s = [1..2,3..4];
        var 0..4: x:: output_var;
        var 0..4: y:: output_var;
        array [1..4] of var int: v = [1,x,-2,y];
        constraint int_lin_eq(c,v,-7);
        constraint set_in(x,s[2]);
        constraint int_lin_le([1,1],[x,y],5);
        solve satisfy;
        """;
    // 2 - x - 6 + y = -7: y = x - 3
    Set<String> expected = new TreeSet<>();
    for (int x = 3; x <= 4; x++) {
      for (int y = 0; y <= 4; y++) {
        if (2 - x - 6 + y == -7 && x + y <= 5) {
          expected.add("x = " + x + "; y = " + y + ";");
        }
      }
    }
    assertEquals(expected, solveAll(fzn));
  }

  @Test
  void regularsOverOneAutomatonShareItsGraph(@TempDir Path dir) throws Exception {
    // each regular built its own automaton and layered graph: 200 regulars over one automaton of
    // 500 states held 1.5 GB. They share one automaton, and the graph over equal domains.
    StringBuilder m = new StringBuilder();
    m.append("predicate jacop_regular(array [int] of var int: x,int: Q,int: S,");
    m.append("array [int] of int: d,int: q0,set of int: F,int: min_index);\n");
    for (int i = 0; i < 12; i++) {
      m.append("var 0..1: x").append(i).append(":: output_var;\n");
    }
    for (int r = 0; r < 3; r++) {
      m.append("constraint jacop_regular([");
      for (int i = 0; i < 4; i++) {
        m.append(i > 0 ? "," : "").append('x').append(r * 4 + i);
      }
      // no two consecutive ones
      m.append("],2,2,[1,2,1,0],1,1..2,0);\n");
    }
    m.append("solve satisfy;\n");
    Path file = dir.resolve("regular.fzn");
    Files.writeString(file, m.toString());
    PrintStream out = System.out;
    Store store;
    try (PrintStream quiet = new PrintStream(OutputStream.nullOutputStream())) {
      System.setOut(quiet);
      FlatzincLoader loader = new FlatzincLoader(new String[] {file.toString()});
      loader.load();
      store = loader.getStore();
    } finally {
      System.setOut(out);
    }
    List<Regular> regulars = new ArrayList<>();
    for (org.jacop.constraints.Constraint c : store.getConstraints()) {
      if (c instanceof Regular r) {
        regulars.add(r);
      }
    }
    assertEquals(3, regulars.size());
    assertSame(regulars.get(0).fsm, regulars.get(1).fsm);
    assertSame(regulars.get(0).fsm, regulars.get(2).fsm);
    assertTrue(regulars.get(0).sharesGraphWith(regulars.get(1)));
    assertTrue(regulars.get(0).sharesGraphWith(regulars.get(2)));
    // the words of 4 letters without two consecutive ones, 8 of them, for each of the 3 regulars
    String all = run(m.toString(), "-a")[0];
    assertEquals(8 * 8 * 8, all.split("----------", -1).length - 1, all);
  }

  @Test
  void anIdentifierKeepsItsVariableForItsStoreOnly() {
    // the nodes of a name share an Ident that keeps the variable it was looked up as; the tables of
    // another store (a portfolio thread, a presolved copy) look the name up again
    Tables first = new Tables(new Store());
    IntVar x = new IntVar(first.store, "x", 0, 5);
    BooleanVar b = new BooleanVar(first.store, "b");
    first.addVariable("x", x);
    first.addVariable("b", b);
    Tables second = new Tables(new Store());
    IntVar otherX = new IntVar(second.store, "x", 0, 5);
    second.addVariable("x", otherX);
    ASTScalarFlatExpr node = new ASTScalarFlatExpr(ParserTreeConstants.JJTSCALARFLATEXPR);
    node.setType(2);
    node.setIdent(new Ident("x"));
    assertEquals("x", node.getIdent());
    assertSame(x, first.getVariable(node));
    assertSame(otherX, second.getVariable(node));
    assertSame(x, first.getVariable(node));
    // an alias made after the lookup is followed
    first.addAlias(b, x);
    assertSame(b, first.getVariable(node));
    assertSame(b, first.getVariable("x"));
    assertSame(otherX, second.getVariable(node));
    ASTScalarFlatExpr unknown = new ASTScalarFlatExpr(ParserTreeConstants.JJTSCALARFLATEXPR);
    unknown.setType(2);
    unknown.setIdent(new Ident("y"));
    assertNull(first.getVariable(unknown));
  }

  @Test
  void anArrayOfParametersIsReadAsConstantsOnce() {
    // every detector that looked at an element read its array of parameters as constants again,
    // boxing each entry: 2000 elements over one array of 20,000 allocated 5 GB of Integer
    Tables tables = new Tables(new Store());
    int[] values = new int[2000];
    for (int i = 0; i < values.length; i++) {
      values[i] = i % 7;
    }
    tables.addIntArray("a", values);
    IntVar[] first = tables.getVariableArray("a");
    assertEquals(2000, first.length);
    assertEquals(3, first[3].value());
    assertSame(first, tables.getVariableArray("a"));
    tables.releaseConstantArrays();
    IntVar[] again = tables.getVariableArray("a");
    assertNotSame(first, again);
    assertSame(first[3], again[3]);
  }

  @Test
  void differenceCyclesKeepElementArcsWithinTheirBudget() throws IOException {
    // each y = a[index] adds two difference arcs per value of the index: 800 elements over one
    // array of 5000 variables made 8 million arcs (570 MB). Over the budget an element adds none.
    int n = 40;
    StringBuilder m = new StringBuilder();
    for (int j = 0; j < n; j++) {
      m.append("var 0..9: a").append(j).append(";\n");
    }
    for (int i = 0; i < 3; i++) {
      m.append("var 1..").append(n).append(": i").append(i).append(";\n");
      m.append("var 0..9: y").append(i).append(":: output_var;\n");
    }
    m.append("array [1..").append(n).append("] of var int: a = [");
    for (int j = 0; j < n; j++) {
      m.append(j > 0 ? "," : "").append('a').append(j);
    }
    m.append("];\n");
    for (int i = 0; i < 3; i++) {
      m.append("constraint array_var_int_element(i").append(i).append(",a,y").append(i);
      m.append(");\n");
    }
    m.append("solve satisfy;\n");
    String model = m.toString();
    assertTrue(run(model, "-debug")[0].contains("% difference cycles: 240 difference"));
    String old = System.getProperty("org.jacop.fz.differenceElements.maxArcs");
    System.setProperty("org.jacop.fz.differenceElements.maxArcs", "100");
    try {
      String out = run(model, "-debug")[0];
      assertTrue(out.contains("% difference cycles: 80 difference"), out);
      assertTrue(out.contains("----------"), out);
    } finally {
      if (old == null) {
        System.clearProperty("org.jacop.fz.differenceElements.maxArcs");
      } else {
        System.setProperty("org.jacop.fz.differenceElements.maxArcs", old);
      }
    }
  }

  @Test
  void differenceCyclesSurvivePresolveFixingAVariableOfAnArc() throws IOException {
    // fuzz seed 1300110: x <= y or y < x is a conditional cycle, so DifferenceCycles is posted with
    // the arc f1 <= x too. Presolve fixes f1, which only the literals of the constraint name, and
    // the copy in the presolved store got null for it and stopped with an error.
    String model =
        """
        predicate jacop_assignment(array [int] of var int: f,array [int] of var int: invf,\
        int: index_f,int: index_invf);
        var 1..2: f1:: output_var;
        var 1..2: f2:: output_var;
        var 1..2: g1:: output_var;
        var 1..2: g2:: output_var;
        var 4..7: x;
        var 4..7: y;
        var 4..7: z;
        var bool: b;
        var bool: p;
        var bool: q;
        constraint jacop_assignment([f1,f2],[g1,g2],1,1);
        constraint int_lin_le([-1,1],[x,f1],0);
        constraint int_lin_le_reif([1,-1],[x,y],0,b);
        constraint int_lin_ne_reif([1,-1],[x,z],0,p);
        constraint int_lin_ne_reif([1,-1],[y,z],0,q);
        solve satisfy;
        """;
    for (String lcg : new String[] {"on", "off"}) {
      // presolve fixes nothing when all solutions are asked for, so one solution is enough
      String[] out = run(model, "--presolve", "on", "--lcg", lcg);
      assertFalse(out[0].contains("Error") || out[1].contains("Error"), out[0] + out[1]);
      assertTrue(out[0].contains("----------"), out[0]);
    }
  }

  @Test
  void localSearchAfterSlowLcgPrintsOnlyBetterSolutions() throws IOException {
    // -f ls=0.1 printed 2009 and then 2018 on ta21: local search runs before LCG, and again when
    // LCG gives way as too slow (forced here), and that second local search and the free search
    // after it took no account of the best solution printed. A random 10 x 10 job shop.
    Random r = new Random(7);
    int n = 10;
    StringBuilder m = new StringBuilder();
    m.append("predicate jacop_cumulative(array [int] of var int: s,array [int] of var int: d,")
        .append("array [int] of var int: r,var int: b);\n");
    int[][] dur = new int[n][n];
    int[][] machine = new int[n][n];
    int horizon = 0;
    for (int j = 0; j < n; j++) {
      List<Integer> order = new ArrayList<>();
      for (int k = 0; k < n; k++) {
        dur[j][k] = 1 + r.nextInt(99);
        horizon += dur[j][k];
        order.add(k);
      }
      Collections.shuffle(order, r);
      for (int k = 0; k < n; k++) {
        machine[j][k] = order.get(k);
      }
    }
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < n; k++) {
        m.append("var 0..").append(horizon).append(": s").append(j).append('_').append(k);
        m.append(";\n");
      }
    }
    m.append("var 0..").append(horizon).append(": makespan:: output_var;\n");
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < n; k++) {
        String next = k + 1 < n ? "s" + j + "_" + (k + 1) : "makespan";
        m.append("constraint int_lin_le([1,-1],[s").append(j).append('_').append(k).append(',');
        m.append(next).append("],").append(-dur[j][k]).append(");\n");
      }
    }
    for (int q = 0; q < n; q++) {
      StringJoiner s = new StringJoiner(",", "[", "]");
      StringJoiner d = new StringJoiner(",", "[", "]");
      StringJoiner h = new StringJoiner(",", "[", "]");
      for (int j = 0; j < n; j++) {
        for (int k = 0; k < n; k++) {
          if (machine[j][k] == q) {
            s.add("s" + j + "_" + k);
            d.add(String.valueOf(dur[j][k]));
            h.add("1");
          }
        }
      }
      m.append("constraint jacop_cumulative(").append(s).append(',').append(d).append(',');
      m.append(h).append(",1);\n");
    }
    m.append("solve minimize makespan;\n");
    // lcg-slow-at=0 makes LCG give way at once, after the first local search
    String out =
        run(
            m.toString(),
            "-a",
            "-f",
            "--lcg",
            "--free-config",
            "ls=0.3,lcg-slow-at=0",
            "-t",
            "4000")[0];
    Matcher cost = Pattern.compile("makespan = (\\d+);").matcher(out);
    int last = Integer.MAX_VALUE;
    int solutions = 0;
    while (cost.find()) {
      int c = Integer.parseInt(cost.group(1));
      assertTrue(c < last, "makespan " + c + " printed after " + last);
      last = c;
      solutions++;
    }
    assertTrue(solutions > 1, out);
  }

  @Test
  void differenceBoundsKeepEverySolution() throws IOException {
    Random r = new Random(20261031);
    for (int run = 0; run < 150; run++) {
      int n = 2 + r.nextInt(3);
      int[] lo = new int[n];
      int[] hi = new int[n];
      StringBuilder model = new StringBuilder("array [1..2] of int: a = [1,-1];\n");
      model.append("array [1..2] of int: b = [-1,1];\narray [1..2] of int: c = [2,1];\n");
      for (int i = 0; i < n; i++) {
        lo[i] = r.nextInt(9) - 4;
        hi[i] = lo[i] + r.nextInt(6);
        model.append("var %d..%d: x%d:: output_var;\n".formatted(lo[i], hi[i], i));
      }
      List<java.util.function.Predicate<int[]>> checks = new ArrayList<>();
      for (int k = 1 + r.nextInt(5); k > 0; k--) {
        int p = r.nextInt(n);
        int q = (p + 1 + r.nextInt(n - 1)) % n;
        int d = r.nextInt(7) - 3;
        switch (r.nextInt(6)) {
          case 0 -> {
            model.append("constraint int_lin_le(a,[x%d,x%d],%d);\n".formatted(p, q, d));
            checks.add(v -> v[p] - v[q] <= d);
          }
          case 1 -> {
            model.append("constraint int_lin_le(b,[x%d,x%d],%d);\n".formatted(p, q, d));
            checks.add(v -> v[q] - v[p] <= d);
          }
          case 2 -> {
            model.append("constraint int_lin_eq(a,[x%d,x%d],%d);\n".formatted(p, q, d));
            checks.add(v -> v[p] - v[q] == d);
          }
          case 3 -> {
            model.append("constraint int_le(x%d,x%d);\n".formatted(p, q));
            checks.add(v -> v[p] <= v[q]);
          }
          case 4 -> {
            model.append("constraint int_lt(x%d,x%d);\n".formatted(p, q));
            checks.add(v -> v[p] < v[q]);
          }
          default -> {
            model.append("constraint int_lin_le(c,[x%d,x%d],%d);\n".formatted(p, q, d));
            checks.add(v -> 2 * v[p] + v[q] <= d);
          }
        }
      }
      model.append("solve satisfy;\n");
      int solutions = 0;
      int[] v = lo.clone();
      while (true) {
        int[] t = v;
        if (checks.stream().allMatch(ch -> ch.test(t))) {
          solutions++;
        }
        int i = 0;
        while (i < n && v[i] == hi[i]) {
          v[i] = lo[i];
          i++;
        }
        if (i == n) {
          break;
        }
        v[i]++;
      }
      String out = run(model.toString(), "-a")[0];
      long found = out.lines().filter(l -> l.equals("----------")).count();
      assertEquals(solutions, found, model + out);
      if (solutions == 0) {
        assertTrue(out.contains("=====UNSATISFIABLE====="), model + out);
      }
    }
  }

  // a prize-collecting path from node 1 as the MiniZinc Challenge 2016 model flattens it: next[i]
  // is 0 for an unused node, 1 for the edge back to node 1, and pos[next[i]] = pos[i] + 1 (MTZ)
  private static String prizeCollecting(int n, long seed) {
    Random r = new Random(seed);
    StringBuilder v = new StringBuilder();
    StringBuilder c = new StringBuilder();
    v.append("predicate jacop_array_var_int_element_nonshifted(var int: idx,")
        .append("array [int] of var int: xs,var int: y,int: min_index);\n");
    v.append("predicate int_lin_eq_imp(array [int] of int: as,array [int] of var int: bs,int: c,")
        .append("var bool: r);\n");
    v.append("predicate int_eq_imp(var int: a,var int: b,var bool: r);\n");
    StringJoiner pos = new StringJoiner(",");
    StringJoiner next = new StringJoiner(",");
    StringJoiner prize = new StringJoiner(",");
    StringJoiner ones = new StringJoiner(",");
    for (int i = 1; i <= n; i++) {
      v.append("var 0..").append(n).append(": p").append(i).append(";\n");
      v.append("var 0..").append(n).append(": x").append(i).append(";\n");
      v.append("var -1000..20: w").append(i).append(";\n");
      v.append("var 0..").append(n).append(": e").append(i).append(";\n");
      v.append("var bool: u").append(i).append(";\n");
      v.append("var bool: b").append(i).append(";\n");
      v.append("var 1..").append(n).append(": y").append(i).append(";\n");
      pos.add("p" + i);
      next.add("x" + i);
      prize.add("w" + i);
      ones.add("1");
    }
    v.append("var 0..1000: obj :: output_var;\n");
    v.append("array [1..").append(n).append("] of var int: next :: output_array([1..").append(n);
    v.append("]) = [").append(next).append("];\n");
    c.append("constraint int_eq(p1,1);\n");
    for (int i = 1; i <= n; i++) {
      // a used node has a successor, and a successor other than node 1 is one position later
      c.append("constraint int_le_reif(1,p").append(i).append(",u").append(i).append(");\n");
      c.append("constraint int_le_reif(1,x").append(i).append(",u").append(i).append(");\n");
      c.append("constraint int_le_reif(2,x").append(i).append(",b").append(i).append(");\n");
      c.append("constraint int_eq_imp(y").append(i).append(",x").append(i).append(",b").append(i);
      c.append(");\n");
      c.append("constraint jacop_array_var_int_element_nonshifted(y").append(i);
      c.append(",[").append(pos).append("],e").append(i).append(",1);\n");
      c.append("constraint int_lin_eq_imp([1,-1],[e").append(i).append(",p").append(i);
      c.append("],1,b").append(i).append(");\n");
      // the prize of the edge to next[i]; small for the edges back to node 1, so that the
      // assignment relaxation prefers the cycles the subtour cuts remove
      StringJoiner row = new StringJoiner(",");
      row.add("0");
      for (int j = 1; j <= n; j++) {
        row.add(j == i ? "-1000" : j == 1 ? "1" : Integer.toString(5 + r.nextInt(16)));
      }
      c.append("constraint jacop_array_var_int_element_nonshifted(x").append(i);
      c.append(",[").append(row).append("],w").append(i).append(",0);\n");
    }
    for (int j = 2; j <= n; j++) {
      // node j has at most one predecessor
      StringJoiner is = new StringJoiner(",");
      for (int i = 1; i <= n; i++) {
        String q = "q" + i + "_" + j;
        v.append("var bool: ").append(q).append(";\n");
        v.append("var 0..1: c").append(q).append(";\n");
        c.append("constraint int_eq_reif(x").append(i).append(',').append(j);
        c.append(',').append(q).append(");\n");
        c.append("constraint bool2int(").append(q).append(",c").append(q).append(");\n");
        is.add("c" + q);
      }
      c.append("constraint int_lin_le([").append(ones).append("],[").append(is).append("],1);\n");
    }
    c.append("constraint int_lin_eq([").append(ones).append(",-1],[").append(prize);
    c.append(",obj],0);\n");
    c.append("solve maximize obj;\n");
    return v.toString() + c;
  }

  @Test
  void successorForestNearMissesKeepTheOptimum() throws IOException {
    // models one constraint away from the path: node 3 without its position link (a cycle through
    // it is allowed), node 4 used without a successor or without a position, node 2 with two
    // predecessors; the forest must keep only what still holds, so the optimum stays
    String[] drops = {
      "constraint int_lin_eq_imp([1,-1],[e3,p3],1,b3);\n",
      "constraint int_le_reif(1,x4,u4);\n",
      "constraint int_le_reif(1,p4,u4);\n",
      "constraint int_eq(p1,1);\n"
    };
    int posted = 0;
    for (long seed = 1; seed <= 3; seed++) {
      for (int k = 0; k < drops.length + 1; k++) {
        String model = prizeCollecting(7, seed);
        model =
            k < drops.length
                ? model.replace(drops[k], "")
                : model.replaceFirst(
                    "(constraint int_lin_le\\(\\[[1,]*\\],\\[[^]]*\\]),1\\)", "$1,2)");
        assertTrue(k == drops.length || !model.contains(drops[k]), model);
        String[] options = seed == 2 ? new String[] {"-s", "-f"} : new String[] {"-s"};
        String base = run(model, options)[0];
        String expected = base.substring(base.lastIndexOf("obj = "));
        expected = expected.substring(0, expected.indexOf('\n'));
        try {
          System.setProperty("org.jacop.fz.successorForest", "true");
          String[] debug = Arrays.copyOf(options, options.length + 1);
          debug[options.length] = "-debug";
          String out = run(model, debug)[0];
          posted += out.contains("% successor forest:") ? 1 : 0;
          String got = out.substring(out.lastIndexOf("obj = "));
          assertEquals(
              expected, got.substring(0, got.indexOf('\n')), k + " " + seed + "\n" + model);
        } finally {
          System.clearProperty("org.jacop.fz.successorForest");
        }
      }
    }
    assertTrue(posted > 0, "posted " + posted);
  }

  @Test
  void successorForestCutsKeepTheOptimum() throws IOException {
    // the subtour cuts of a successor forest (off by default) remove the subtours of the LP
    // relaxation and the optimum stays the same; under free search the dense tableau of
    // prize-collecting 32-4-8-2 ran out of pivots in the first round, and the round now goes on
    // on the sparse simplex (the LP statistics are printed with -debug)
    String[][] runs = {{"-s", "-debug"}, {"-s", "-debug", "-f"}, {"-s", "-debug", "--lcg", "off"}};
    int[] cuts = new int[runs.length];
    for (long seed = 1; seed <= 5; seed++) {
      String model = prizeCollecting(8, seed);
      String base = run(model)[0];
      assertTrue(base.contains("=========="), base);
      int from = base.lastIndexOf("obj = ");
      String optimum = base.substring(from, base.indexOf('\n', from));
      try {
        System.setProperty("org.jacop.fz.successorForest", "true");
        for (int k = 0; k < runs.length; k++) {
          String out = run(model, runs[k])[0];
          String what = Arrays.toString(runs[k]) + out;
          assertTrue(out.contains("==========") && out.contains("% successor forest:"), what);
          from = out.lastIndexOf("obj = ");
          assertEquals(optimum, out.substring(from, out.indexOf('\n', from)), what);
          Matcher m = Pattern.compile("lpTreeCuts=(\\d+)").matcher(out);
          assertTrue(m.find(), what);
          cuts[k] += Integer.parseInt(m.group(1));
        }
      } finally {
        System.clearProperty("org.jacop.fz.successorForest");
      }
    }
    for (int k = 0; k < runs.length; k++) {
      assertTrue(cuts[k] > 0, Arrays.toString(runs[k]));
    }
  }

  @Test
  void singleWeightLinearLeBoundIsExact() throws IOException {
    // the bound of w * x <= c was computed in float: wrong beyond 2^24 and NaN for w = 0
    String[][] cases = {
      {
        "var 100000005..100000008: x:: output_var;",
        "int_lin_le([3],[x],300000020)",
        "[x = 100000005;, x = 100000006;] =========="
      },
      {
        "var 100000005..100000008: x:: output_var;",
        "int_lin_le([1,2],[x,x],300000020)",
        "[x = 100000005;, x = 100000006;] =========="
      },
      {
        "var -100000008..-100000005: x:: output_var;",
        "int_lin_le([-3],[x],300000020)",
        "[x = -100000005;, x = -100000006;] =========="
      },
      {
        "var 16777215..16777220: x:: output_var;",
        "int_lin_le([1],[x],16777217)",
        "[x = 16777215;, x = 16777216;, x = 16777217;] =========="
      },
      {"var 0..2: x:: output_var;", "int_lin_le([0],[x],5)", "[x = 0;, x = 1;, x = 2;] =========="},
      {"var 0..2: x:: output_var;", "int_lin_le([0],[x],-1)", "[] =====UNSATISFIABLE====="},
      {"var bool: x:: output_var;", "bool_lin_le([0],[x],3)", "[x = false;, x = true;] =========="},
      {"var bool: x:: output_var;", "bool_lin_le([0],[x],-1)", "[] =====UNSATISFIABLE====="}
    };
    for (String[] c : cases) {
      String model = c[0] + "\nconstraint " + c[1] + ";\nsolve satisfy;\n";
      assertEquals(c[2], normalised(run(model, "-a")[0], false), model);
    }
    String opt =
        "var 0..200000000: x:: output_var;\nconstraint int_lin_le([3],[x],300000020);\n"
            + "solve maximize x;\n";
    assertEquals("x = 100000006; ==========", normalised(run(opt)[0], true));
  }

  @Test
  void reifiedLinearLeSkipsZeroWeights() throws IOException {
    // (b1 + 0 * b2 <= 0) <-> r was posted as r <-> b1 = b2 = 0, which constrains b2
    String model =
        "var bool: b1:: output_var;\nvar bool: b2:: output_var;\nvar bool: r:: output_var;\n"
            + "constraint int_lin_le_reif([1,0],[b1,b2],0,r);\nsolve satisfy;\n";
    String zeros = model.replace("[1,0]", "[0,0]");
    for (String[] options : new String[][] {{"-a"}, {"-a", "--lcg"}}) {
      assertEquals(
          "[b1 = false; b2 = false; r = true;, b1 = false; b2 = true; r = true;,"
              + " b1 = true; b2 = false; r = false;, b1 = true; b2 = true; r = false;] ==========",
          normalised(run(model, options)[0], false));
      assertEquals(
          "[b1 = false; b2 = false; r = true;, b1 = false; b2 = true; r = true;,"
              + " b1 = true; b2 = false; r = true;, b1 = true; b2 = true; r = true;] ==========",
          normalised(run(zeros, options)[0], false));
    }
  }

  @Test
  void emptyXorIsUnsatisfiable() throws IOException {
    // the xor of no variables is false; the SAT translation failed with a negative array size
    String model = "var bool: b1:: output_var;\nconstraint array_bool_xor([]);\nsolve satisfy;\n";
    for (String[] options : new String[][] {{}, {"-a"}, {"--lcg"}, {"-sat"}}) {
      String[] out = run(model, options);
      assertEquals("[] =====UNSATISFIABLE=====", normalised(out[0], false), out[1]);
      assertEquals(0, lastStatus, out[1]);
      assertFalse(out[1].contains("problem detected"), out[1]);
    }
  }

  @Test
  void emptyReifiedLinearIsAConstantTest() throws IOException {
    // an empty sum was posted as a LinearInt, which needs at least one variable
    String[][] cases = {
      {"int_lin_lt_reif([],[],0,b)", "[b = false;] =========="},
      {"int_lin_lt_reif([],[],1,b)", "[b = true;] =========="},
      {"bool_lin_lt_reif([],[],0,b)", "[b = false;] =========="},
      {"int_lin_lt_imp([],[],0,b)", "[b = false;] =========="},
      {"int_lin_ge_imp([],[],1,b)", "[b = false;] =========="},
      {"int_lin_gt_imp([],[],-1,b)", "[b = false;, b = true;] =========="},
      {"int_lin_le_reif([],[],-1,b)", "[b = false;] =========="},
      {"int_lin_ne_reif([],[],0,b)", "[b = false;] =========="},
      {"int_lin_eq_reif([],[],0,b)", "[b = true;] =========="}
    };
    for (String[] c : cases) {
      String model = "var bool: b:: output_var;\nconstraint " + c[0] + ";\nsolve satisfy;\n";
      assertEquals(c[1], normalised(run(model, "-a")[0], false), model);
    }
  }

  @Test
  void reifiedTableWithItsControlInTheScope() throws IOException {
    // bool2int(b, i) makes i the control b itself, and TableReified rejects a control in its list
    int[][] table = {{2, 0}, {0, 2}, {1, 0}, {-2, 1}, {0, 1}};
    for (boolean imp : new boolean[] {true, false}) {
      for (int rows : new int[] {4, 5}) {
        StringBuilder tbl = new StringBuilder();
        Set<String> expected = new TreeSet<>();
        for (int k = 0; k < rows; k++) {
          tbl.append(k == 0 ? "" : ",").append(table[k][0]).append(',').append(table[k][1]);
        }
        for (int b = 0; b <= 1; b++) {
          for (int x = -2; x <= 2; x++) {
            boolean in = false;
            for (int k = 0; k < rows; k++) {
              in |= table[k][0] == x && table[k][1] == b;
            }
            if (imp ? b == 0 || in : (b == 1) == in) {
              expected.add("b2 = " + (b == 1) + "; i3 = " + b + "; x1 = " + x + ";");
            }
          }
        }
        String model =
            "var bool: b2:: output_var;\nvar 0..1: i3:: output_var;\n"
                + "var -2..2: x1:: output_var;\nconstraint bool2int(b2,i3);\n"
                + "constraint jacop_table_int_"
                + (imp ? "imp" : "reif")
                + "([x1,i3],["
                + tbl
                + "],b2);\nsolve satisfy;\n";
        assertEquals(expected + " ==========", normalised(run(model, "-a")[0], false), model);
      }
    }
  }

  @Test
  void emptyLexChainsAndTablesAnswer() throws IOException {
    // a chain of vectors of length 0 holds, unless it is strict over two vectors or more; a table
    // without columns has no rows and is false (a negative one true)
    String[][] cases = {
      {"jacop_lex_chain_less_int([],0)", "6"},
      {"jacop_lex_chain_less_bool([],0)", "6"},
      {"jacop_lex_chain_lesseq_int([],0)", "6"},
      {"jacop_lex_chain_lesseq_bool([],0)", "6"},
      {"jacop_lex_chain_less_int([],1)", "6"},
      {"jacop_lex_chain_less_int([],2)", "0"},
      {"jacop_lex_chain_lesseq_int([],3)", "6"},
      {"jacop_table_int([],[])", "0"},
      {"jacop_table_int_reif([],[],b)", "6"},
      {"jacop_table_int_imp([],[],b)", "6"},
      {"jacop_table_int_reif([],[],true)", "0"},
      {"jacop_negative_table_int([],[])", "6"}
    };
    for (String[] c : cases) {
      // domains of three values let -f compile the model into clauses (ClausalCompiler)
      String model =
          "var 0..2: y:: output_var;\nvar 0..2: z:: output_var;\nvar bool: b:: output_var;\n"
              + "constraint bool_eq(b,false);\nconstraint int_le(y,z);\nconstraint "
              + c[0]
              + ";\nsolve satisfy;\n";
      int expected = Integer.parseInt(c[1]);
      for (String[] options :
          new String[][] {{"-a"}, {"-a", "--lcg"}, {"-a", "--lcg", "off"}, {"-f", "--lcg"}}) {
        String[] out = run(model, options);
        String what = c[0] + " " + Arrays.toString(options) + "\n" + out[0] + out[1];
        int solutions = out[0].split("----------", -1).length - 1;
        // -f looks for one solution
        boolean all = "-a".equals(options[0]);
        assertEquals(all || expected == 0 ? expected : 1, solutions, what);
        assertTrue(out[0].contains(solutions == 0 ? "=====UNSATISFIABLE=====" : "y = "), what);
      }
    }
  }

  @Test
  void medianSearchSeesTheFirstHoleOfALargeDomain() throws IOException {
    // x has 100000 values, so its holes are kept as intervals; the first hole, x != -1, was not
    // seen
    // by the intervals cached before it, and the median search failed on a satisfiable model
    String model =
        "var -50000..49999: x :: output_var;\n"
            + "var 0..50000: y :: output_var;\n"
            + "var -1..0: d :: output_var;\n"
            + "constraint int_abs(x, y) :: domain;\n"
            + "constraint int_ne(x, d);\n"
            + "solve :: seq_search([int_search([d], input_order, indomain_min, complete),"
            + " int_search([x, y], input_order, indomain_median, complete)]) satisfy;\n";
    for (String[] options : new String[][] {{"-a"}, {"--lcg", "off"}}) {
      String out = run(model, options)[0];
      assertTrue(out.contains("x = 0;") && out.contains("d = -1;"), Arrays.toString(options) + out);
      assertFalse(out.contains("UNSATISFIABLE"), Arrays.toString(options) + out);
    }
  }

  @Test
  void congruenceOfALinearSystemPrunesFewValuesOfAWideDomain() throws IOException {
    // the congruence x0 = 1 (mod 4) of the system was applied by building every congruent value
    // between the bounds of x0, about 268 million of them for its five values: out of memory
    String model =
        """
        var {-536870910,268435456,268435457,536685545,536870909}: x0:: output_var;
        var {-536870910,-536870909,-46341,4,32768}: x2:: output_var;
        var {-3,-2,-1,65536}: x3:: output_var;
        constraint int_lin_eq([4,-1,-536870910],[x2,x0,x3],1);
        solve satisfy;
        """;
    assertEquals(List.of("x0 = 536685545; x2 = -46341; x3 = -1;"), solveAllInOrder(model));
  }

  @Test
  void elementOfConstantsBeyondTheDomainRangeIsSolved() throws IOException {
    // a constant beyond MIN_INT..MAX_INT at the only position of the index was posted as XeqC,
    // which rejected it: "Constraint XeqC has a constant c 2147483646 that is not in the
    // allowed range" instead of the answer
    String fixed =
        """
        var {1}: i:: output_var;
        var {-1,0,1}: v:: output_var;
        constraint array_int_element(i,[2147483646],v);
        solve satisfy;
        """;
    String[] out = run(fixed, "-a");
    assertTrue(out[0].contains("=====UNSATISFIABLE====="), out[0] + out[1]);
    assertEquals(0, lastStatus, out[0] + out[1]);
    String open =
        """
        var {1,2}: i:: output_var;
        var {-4,0}: v:: output_var;
        constraint array_int_element(i,[2147483646,-4],v);
        solve satisfy;
        """;
    assertEquals(List.of("i = 2; v = -4;"), solveAllInOrder(open));
  }

  @Test
  void shortLinearRowBeyondIntIsDecidedByItsBounds() throws IOException {
    // rows of two variables with unit weights are posted as XplusCeqZ, XplusYeqC or XplusClteqZ,
    // which add their bounds and constant in int and rejected these models with "Evaluation of
    // model resulted in an overflow"; each row is decided by its bounds
    String reified =
        """
        var {-3,65536,268435454}: x:: output_var;
        var bool: b:: output_var;
        constraint int_lin_ne_reif([1,-1],[x,x],2147483647,b);
        solve satisfy;
        """;
    assertEquals(
        List.of("b = true; x = -3;", "b = true; x = 65536;", "b = true; x = 268435454;"),
        solveAllInOrder(reified));
    String implied =
        """
        var {-536870909,0,536870909}: x:: output_var;
        var {-536870909,0,536870909}: y:: output_var;
        var bool: b:: output_var;
        constraint int_lin_eq_imp([1,-1],[x,y],2147483646,b);
        constraint bool_eq(b,true);
        solve satisfy;
        """;
    String[] out = run(implied, "-a");
    assertTrue(out[0].contains("=====UNSATISFIABLE====="), out[0] + out[1]);
    assertEquals(0, lastStatus, out[0] + out[1]);
    String plain =
        """
        var {-65536,1,268435454}: x:: output_var;
        var {-32768,7}: y:: output_var;
        constraint int_lin_le([1,-1],[y,x],-2147483647);
        solve satisfy;
        """;
    out = run(plain, "-a");
    assertTrue(out[0].contains("=====UNSATISFIABLE====="), out[0] + out[1]);
    assertEquals(0, lastStatus, out[0] + out[1]);
  }

  @Test
  void diffnProjectionOverAWideSpanIsLeftOut() throws IOException {
    // the cumulative projection of diffn bounds its span by first + span = last, whose int bounds
    // reach twice the distance from the lowest origin to the highest end: XplusYeqZ rejected it
    // and the model ended in "Evaluation of model resulted in an overflow"
    String model =
        """
        var {-536870910,536870908}: x0:: output_var;
        var {-268435455,536870909}: x1:: output_var;
        var {-536870910,32768}: y0:: output_var;
        var {0,536870908}: w0:: output_var;
        var {0,268435455}: h1:: output_var;
        constraint jacop_diff2_strict([x0,x1],[y0,-46340],[w0,2],[65536,h1]);
        solve satisfy;
        """;
    long expected = 0;
    int[] xs0 = {-536870910, 536870908};
    int[] xs1 = {-268435455, 536870909};
    int[] ys0 = {-536870910, 32768};
    int[] ws0 = {0, 536870908};
    int[] hs1 = {0, 268435455};
    for (long a : xs0) {
      for (long b : xs1) {
        for (long c : ys0) {
          for (long w : ws0) {
            for (long h : hs1) {
              if (a + w <= b || c + 65536 <= -46340 || b + 2 <= a || -46340 + h <= c) {
                expected++;
              }
            }
          }
        }
      }
    }
    assertEquals(expected, solveAllInOrder(model).size());
  }

  /** No set has an empty union, so it partitions only the empty universe. */
  @Test
  void aPartitionOfNoSetHoldsOnlyForAnEmptyUniverse() throws IOException {
    String model =
        "var 0..1: y :: output_var;\nconstraint jacop_partition_set([], %s);\nsolve satisfy;\n";
    for (String[] options : new String[][] {{"-a"}, {"-a", "--lcg", "off"}}) {
      String rejected = run(model.formatted("{1}"), options)[0];
      assertTrue(rejected.contains("=====UNSATISFIABLE====="), rejected);
      assertEquals(Set.of("y = 0;", "y = 1;"), solveAll(model.formatted("{}")));
    }
  }

  /** An index of array_float_element beyond the array selects no value and gave an exception. */
  @Test
  void aFloatElementIndexBeyondTheArraySelectsNoValue() throws IOException {
    String head = "var 1.0..1.0: f :: output_var;\nvar 2.0..2.0: g :: output_var;\n";
    String[][] cases = {
      {"var 3..3: i :: output_var;\nconstraint array_float_element(i, [0.0, 2.0], 2.0);\n", "0"},
      {"var 2..3: i :: output_var;\nconstraint array_float_element(i, [0.0, 2.0], 2.0);\n", "1"},
      {"var 2..4: i :: output_var;\nconstraint array_var_float_element(i, [f, g], g);\n", "1"},
      {"var 3..3: i :: output_var;\nconstraint array_var_float_element(i, [f, g], f);\n", "0"}
    };
    for (String[] c : cases) {
      String model = head + c[0] + "solve satisfy;\n";
      for (String[] options : new String[][] {{"-a"}, {"-a", "--lcg", "off"}}) {
        String[] out = run(model, options);
        String what = model + out[0] + out[1];
        assertFalse(out[1].contains("Exception"), what);
        if (c[1].equals("0")) {
          assertTrue(out[0].contains("=====UNSATISFIABLE====="), what);
        } else {
          assertTrue(out[0].contains("i = 2;") && out[0].contains("=========="), what);
        }
      }
    }
  }

  /** float_lin_* over no variable is the constant test 0 rel c; LinearFloat rejected it. */
  @Test
  void anEmptyFloatLinearRowIsAConstantTest() throws IOException {
    String head = "var bool: b :: output_var;\n";
    String[][] cases = {
      {"float_lin_le([], [], 0.0)", "b = false; b = true;"},
      {"float_lin_le([], [], -1.0)", ""},
      {"float_lin_eq([], [], 1.0)", ""},
      {"float_lin_ne([], [], 1.0)", "b = false; b = true;"},
      {"float_lin_lt([], [], 0.0)", ""},
      {"float_lin_lt_reif([], [], 1.0, b)", "b = true;"},
      {"float_lin_eq_reif([], [], 1.0, b)", "b = false;"}
    };
    for (String[] c : cases) {
      String model = head + "constraint " + c[0] + ";\nsolve satisfy;\n";
      String[] out = run(model, "-a");
      String what = model + out[0] + out[1];
      Set<String> expected =
          c[1].isEmpty()
              ? Set.of("=====UNSATISFIABLE=====")
              : new TreeSet<>(Arrays.asList(c[1].split(" (?=b)")));
      assertEquals(expected, solveAll(model), what);
      assertTrue(out[0].contains(c[1].isEmpty() ? "=====UNSATISFIABLE=====" : "=========="), what);
    }
  }

  @Test
  void sumMergedIntoAMinimumKeepsTheHoleOfItsVariable() throws IOException {
    // z = x + y is merged into m = min(z, w) without z; the hole z != 3 is a constraint on x + y
    // that the merge dropped (160 solutions for 120)
    String model =
        "var 0..3: x :: output_var;\n"
            + "var 0..3: y :: output_var;\n"
            + "var {0,1,2,4,5,6}: z;\n"
            + "var 0..9: w :: output_var;\n"
            + "var 0..9: m :: output_var;\n"
            + "constraint int_lin_eq([1,1,-1],[x,y,z],0);\n"
            + "constraint int_min(z, w, m);\n"
            + "solve satisfy;\n";
    int expected = 0;
    for (int x = 0; x <= 3; x++) {
      for (int y = 0; y <= 3; y++) {
        expected += x + y == 3 ? 0 : 10;
      }
    }
    assertEquals(expected, solveAll(model).size());
  }

  @Test
  void indexDisjunctionKeepsTheDomainOfAnElementResult() throws IOException {
    // r0 = [x0,x1][k] takes only 0 or 2, and x0, x1 are 1 or 2, so r0 = 2 and r0 < r1 has no
    // solution; the disjunction x0 < x1 or x1 < x0 without the domain of r0 printed r0 = 1
    String model =
        "var 1..2: x0 :: output_var;\n"
            + "var 1..2: x1 :: output_var;\n"
            + "var 1..2: k0 :: output_var;\n"
            + "var {0,2}: r0 :: output_var;\n"
            + "var 0..2: r1 :: output_var;\n"
            + "constraint array_var_int_element(k0,[x0,x1],r0);\n"
            + "constraint array_var_int_element(k0,[x1,x0],r1);\n"
            + "constraint int_lt(r0,r1);\n"
            + "solve satisfy;\n";
    String[] out = run(model);
    assertTrue(out[0].contains("=====UNSATISFIABLE====="), out[0] + out[1]);
  }

  @Test
  void indexDisjunctionKeepsAnIndexDeclaredEqualToAnOutput() throws IOException {
    // the only solution has k0 = 2 and r0 = x1 = 1; with k0 and r0 left out of the model, z and w,
    // declared equal to them, were printed as 1 and 0
    String model =
        "var 0..2: x0 :: output_var;\n"
            + "var 1..2: x1 :: output_var;\n"
            + "var 1..2: k0;\n"
            + "var 0..2: r0;\n"
            + "var 0..2: r1;\n"
            + "var 1..2: z :: output_var = k0;\n"
            + "var 0..2: w :: output_var = r0;\n"
            + "constraint array_var_int_element(k0,[x0,x1],r0);\n"
            + "constraint array_var_int_element(k0,[x1,x0],r1);\n"
            + "constraint int_lt(r0,r1);\n"
            + "constraint int_lt(x1, x0);\n"
            + "solve satisfy;\n";
    String[] out = run(model);
    assertTrue(out[0].contains("z = 2;") && out[0].contains("w = 1;"), out[0] + out[1]);
  }

  @Test
  void setUnionKeepsAnInnerUnionDeclaredEqualToAnOutput() throws IOException {
    // w is declared equal to the inner union u3 of {e0} + ... + {e7}; the union chain was replaced
    // by membership clauses on its root, u3 was left free and w was printed as 1..9
    StringBuilder model = new StringBuilder();
    for (int i = 0; i < 8; i++) {
      model.append("var 1..9: e").append(i).append(" :: output_var;\n");
      model.append("var set of 1..9: s").append(i).append(";\n");
    }
    for (int i = 1; i < 8; i++) {
      model.append("var set of 1..9: u").append(i).append(";\n");
    }
    model.append("var set of 1..9: w :: output_var = u3;\n");
    for (int i = 0; i < 8; i++) {
      model.append("constraint set_card(s").append(i).append(", 1);\n");
      model.append("constraint set_in(e").append(i).append(", s").append(i).append(");\n");
    }
    model.append("constraint set_union(s0, s1, u1);\n");
    for (int i = 2; i < 8; i++) {
      model.append("constraint set_union(u").append(i - 1).append(", s").append(i);
      model.append(", u").append(i).append(");\n");
    }
    model.append("constraint int_lt(e0, e1);\n");
    model.append("solve :: int_search([e0,e1,e2,e3,e4,e5,e6,e7], input_order, indomain_min,");
    model.append(" complete) satisfy;\n");
    String[] out = run(model.toString());
    // e0 = 1, e1 = 2 and the others 1
    assertTrue(out[0].contains("w = 1..2;"), out[0] + out[1]);
  }

  @Test
  void propagationWhileTheModelIsBuiltStopsAtTheTimeOut() throws IOException {
    // x < y < z < x over wide domains fails only after the bounds have crept one unit per step
    // across them, in the propagation of the constraints posted (or of the root, for rows posted
    // late): minutes past -t when run in process, where no watchdog ends the run
    String vars =
        "var -500000000..500000000: x :: output_var;\n"
            + "var -500000000..500000000: y :: output_var;\n"
            + "var -500000000..500000000: z :: output_var;\n";
    String[] models = {
      vars
          + "var 1..3: a :: output_var;\n"
          + "var 1..3: b :: output_var;\n"
          + "constraint int_lin_le([1,-1,1],[x,y,a],0);\n"
          + "constraint int_lin_le([1,-1,1],[y,z,b],0);\n"
          + "constraint int_lin_le([1,-1],[z,x],-1);\n"
          + "solve satisfy;\n",
      vars
          + "var -500000000..500000000: w :: output_var;\n"
          + "constraint int_lin_le([2,-3],[x,y],-1);\n"
          + "constraint int_lin_le([3,-2],[y,z],-1);\n"
          + "constraint int_lin_le([1,-1,1],[z,x,w],-1);\n"
          + "constraint int_lin_le([-1],[w],0);\n"
          + "solve satisfy;\n"
    };
    for (String model : models) {
      long start = System.nanoTime();
      String out = run(model, "-t", "300")[0];
      long millis = (System.nanoTime() - start) / 1_000_000;
      assertTrue(out.contains("=====UNKNOWN====="), out);
      assertTrue(!out.contains("=====UNSATISFIABLE====="), out);
      // about 0.3 s; it took 20 s and more before
      assertTrue(millis < 8_000, millis + " ms");
    }
  }

  @Test
  void equalityOverBooleansWithWeightsBeyondIntIsPosted() throws IOException {
    // the weights add up to more than an int holds: LinearBool threw "overflow" for the valid
    // model; b2 = b1 = 1, b0 = 0 is the only assignment, for each of the 3 values of x
    String head =
        "var bool: b0 :: output_var;\n"
            + "var bool: b1 :: output_var;\n"
            + "var bool: b2 :: output_var;\n"
            + "var 0..2: x :: output_var;\n";
    for (String row :
        new String[] {
          "bool_lin_eq([2147483646,1073741824,3],[b0,b2,b1],1073741827)",
          "int_lin_eq([2147483646,1073741824,3],[b0,b2,b1],1073741827)"
        }) {
      String model = head + "constraint " + row + ";\nsolve satisfy;\n";
      Set<String> solutions = solveAll(model);
      assertEquals(3, solutions.size(), model + solutions);
      assertTrue(solutions.contains("b0 = false; b1 = true; b2 = true; x = 1;"), model + solutions);
    }
  }

  @Test
  void floatDomainNarrowedToTheFloatRangeProvesNoUnsatisfiability() throws IOException {
    // x is declared up to 1e300 and narrowed to 1e150; ln(x) >= 400 needs x >= e^400, about
    // 5e173, beyond the narrowed domain: the search fails, but the model has solutions
    String model =
        "var 1.0..1e300: x :: output_var;\n"
            + "var 400.0..1000.0: y :: output_var;\n"
            + "constraint float_ln(x, y);\n"
            + "solve satisfy;\n";
    String[] out = run(model);
    assertFalse(out[0].contains("=====UNSATISFIABLE====="), out[0]);
    assertTrue(out[0].contains("=====UNKNOWN====="), out[0]);
  }

  @Test
  void setOverTheWholeIntegerRangeIsSolvedWithoutMirroringItsElements() throws IOException {
    // LCG mirrors each open element of a set by a 0/1 variable: a billion of them ran out of memory
    String model =
        "var set of -536870910..536870909: s :: output_var;\n"
            + "var 0..10: c :: output_var;\n"
            + "constraint set_card(s, c);\n"
            + "constraint set_in(-536870910, s);\n"
            + "constraint set_in(536870909, s);\n"
            + "solve minimize c;\n";
    String[] out = run(model, "--lcg", "on");
    assertTrue(out[0].contains("c = 2;") && out[0].contains("=========="), out[0] + out[1]);
  }

  @Test
  void comparisonWithAConstantBeyondTheRangeIsDecided() throws IOException {
    // no variable reaches a constant beyond JaCoP's integer range; the comparisons threw
    // "Constant ... outside variable bounds" for these valid models
    String[][] cases = {
      {"int_le(x, 999000001)", "x = 0; x = 1;"},
      {"int_ne(999000001, x)", "x = 0; x = 1;"},
      {"int_lt(x, -999000001)", ""},
      {"int_le_reif(x, 999000001, b)", "b = true; x = 0; b = true; x = 1;"},
      {"int_eq_reif(-999000001, x, b)", "b = false; x = 0; b = false; x = 1;"},
      {"int_le_imp(x, -999000001, b)", "b = false; x = 0; b = false; x = 1;"}
    };
    for (String[] c : cases) {
      String model =
          "var 0..1: x :: output_var;\nvar bool: b;\n"
              + "constraint "
              + c[0]
              + ";\nsolve satisfy;\n";
      if (c[0].contains(", b)")) {
        model = model.replace("var bool: b;", "var bool: b :: output_var;");
      }
      Set<String> expected =
          c[1].isEmpty()
              ? Set.of("=====UNSATISFIABLE=====")
              : new TreeSet<>(
                  Arrays.asList(c[1].split(" (?=" + (c[0].contains(", b)") ? "b" : "x") + ")")));
      assertEquals(expected, solveAll(model), model);
    }
  }

  @Test
  void listDomainWithValuesBeyondTheRangeIsNarrowed() throws IOException {
    // {1, 2000000000} kept 2000000000 beyond JaCoP's range: x + y <= 5 wrapped around and accepted
    // x = y = 2000000000, and x = 10^9 * y was reported unsatisfiable though x = 2*10^9, y = 2
    // holds
    String sum =
        "var {1,2000000000}: x :: output_var;\n"
            + "var {1,2000000000}: y :: output_var;\n"
            + "constraint int_lin_le([1,1],[x,y],5);\n"
            + "solve satisfy;\n";
    assertEquals(Set.of("x = 1; y = 1;"), solveAll(sum));
    String product =
        "var {2,2000000000}: x :: output_var;\n"
            + "var -10..10: y :: output_var;\n"
            + "constraint int_lin_eq([1,-1000000000],[x,y],0);\n"
            + "solve satisfy;\n";
    String[] out = run(product);
    assertFalse(out[0].contains("=====UNSATISFIABLE====="), out[0]);
  }

  @Test
  void verboseStatisticsOfLcgWithRestartsPrintTheSolution() throws IOException {
    // --restart with LCG keeps a restart calculator but no restart search: printing the verbose
    // statistics of a solution read the restarts of that missing search (NullPointerException)
    String model =
        "var 1..3: x :: output_var;\n"
            + "var 1..3: y :: output_var;\n"
            + "constraint int_lt(x,y);\n"
            + "solve minimize y;\n";
    String[] out = run(model, "-v", "--lcg", "on", "--restart", "luby", "-t", "5000");
    assertTrue(out[0].contains("y = 2;") && out[0].contains("=========="), out[0] + out[1]);
  }

  @Test
  void objectivePresolveKeepsTheExactlyOneSetDefiningTheObjective() throws IOException {
    // x + y + z = 1 was read as the definition of the objective x and as an exactly-one set; the
    // shift by that set gave the equation x = x, which replaced the definition: x = y = z = 0
    for (String sense : new String[] {"minimize", "maximize"}) {
      String model =
          "var 0..1: x :: output_var;\n"
              + "var 0..1: y :: output_var;\n"
              + "var 0..1: z :: output_var;\n"
              + "constraint int_lin_eq([1,1,1],[x,y,z],1);\n"
              + "solve "
              + sense
              + " x;\n";
      String[] out = run(model);
      int ones = 0;
      for (String v : new String[] {"x", "y", "z"}) {
        if (out[0].contains(v + " = 1;")) {
          ones++;
        }
      }
      assertEquals(1, ones, out[0] + out[1]);
      assertTrue(out[0].contains("x = " + (sense.equals("minimize") ? 0 : 1) + ";"), out[0]);
    }
  }

  @Test
  void portfolioDoesNotWaitForAStuckThreadPastTheTimeOut() throws InterruptedException {
    // a thread in a start-up phase that does not look at the time-out (the root LP, the trail of
    // lazy clause generation) held the run for up to 10 s after the answer was printed
    CountDownLatch release = new CountDownLatch(1);
    Thread stuck =
        new Thread(
            () -> {
              boolean done = false;
              while (!done) {
                try {
                  done = release.await(60, TimeUnit.SECONDS);
                } catch (InterruptedException _) {
                  // a phase that ignores interrupts
                }
              }
            });
    stuck.setDaemon(true);
    stuck.start();
    try {
      long start = System.nanoTime();
      Portfolio.join(List.of(stuck), System.currentTimeMillis());
      long millis = (System.nanoTime() - start) / 1_000_000;
      assertTrue(stuck.isAlive());
      // 0.3 s after the time-out; 10 s before
      assertTrue(millis < 5_000, millis + " ms");
      // a thread that ends is waited for
      Thread quick = new Thread(() -> {});
      quick.start();
      Portfolio.join(List.of(quick), 0);
      assertFalse(quick.isAlive());
    } finally {
      release.countDown();
    }
  }

  // options whose time-out passes after a given number of checks, once armed: a phase that looks at
  // the clock is stopped at a point that does not depend on the speed of the machine
  private static final class CheckCountingOptions extends Options {
    boolean armed;
    long checks;
    long passAfter = Long.MAX_VALUE;

    CheckCountingOptions(String[] args) {
      super(args);
    }

    // every check reads the clock, so the counts do not depend on the sampling of the set-up
    @Override
    public int timeOutCheckStride() {
      return 1;
    }

    @Override
    public boolean timeOutPassed() {
      if (!armed) {
        return false;
      }
      checks++;
      return checks > passAfter;
    }
  }

  // the parsed items of a model, as Constraints reads them before any constraint is posted
  private static SimpleNode parsedItems(Parser parser) throws ParseException {
    parser.pred_decl_items();
    parser.var_decl_items();
    parser.constraint_items();
    SimpleNode tree = new SimpleNode(ParserTreeConstants.JJTMODEL);
    Node constraints = parser.jjtree.popNode();
    tree.jjtAddChild(parser.jjtree.popNode(), 0);
    tree.jjtAddChild(constraints, 1);
    return tree;
  }

  @Test
  void cliqueSearchOfTheAlldifferentDetectorStopsAtTheTimeOut() throws IOException, ParseException {
    // the time-out was checked while the constraints were scanned, not in the search for cliques
    // of disequalities that follows (4.5 s on hidato_table)
    StringBuilder model = new StringBuilder();
    int n = 8;
    for (int i = 0; i < n; i++) {
      model.append("var 0..9: x").append(i).append(";\n");
    }
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        model.append("constraint int_ne(x").append(i).append(", x").append(j).append(");\n");
      }
    }
    model.append("solve satisfy;\n");
    Path fzn = tmp.resolve("cliques.fzn");
    Files.writeString(fzn, model.toString(), StandardCharsets.UTF_8);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      for (boolean stop : new boolean[] {false, true}) {
        CheckCountingOptions opt =
            new CheckCountingOptions(new String[] {"-t", "60000", fzn.toString()});
        try (java.io.FileInputStream input = new java.io.FileInputStream(fzn.toFile())) {
          Parser parser = new Parser(input);
          parser.setOptions(opt);
          parser.cc.setOptions(opt);
          SimpleNode tree = parsedItems(parser);
          Support support = parser.cc.support;
          opt.armed = true;
          // the scan of the constraints checks once per constraint
          int scanChecks = n * (n - 1) / 2;
          if (stop) {
            opt.passAfter = scanChecks;
          }
          AlldifferentDetector detector = new AlldifferentDetector(support);
          if (stop) {
            // the time-out passes after the scan, in the clique search
            assertThrows(ModelTimeOut.class, () -> detector.detect(tree));
          } else {
            detector.detect(tree);
            assertEquals(n * (n - 1) / 2, detector.replaced().size());
            assertTrue(opt.checks > scanChecks, opt.checks + " checks");
          }
        }
      }
    } finally {
      System.setOut(originalOut);
    }
  }

  @Test
  void propagationUnderLazyClauseGenerationStopsAtTheTimeOut() throws IOException {
    // b = true makes x < y < z < x, which fails only after the bounds have crept one unit per step
    // across the wide domains, in one propagation of the store under lazy clause generation: it
    // ran 14 s past -t 1000 in process and ran out of memory, since the trail records every step
    // (a crawl of the propagation while the model is built stops at the time-out since 8004e83cc)
    String model =
        "var -500000000..500000000: x :: output_var;\n"
            + "var -500000000..500000000: y :: output_var;\n"
            + "var -500000000..500000000: z :: output_var;\n"
            + "var 1..3: a :: output_var;\n"
            + "var 1..3: c :: output_var;\n"
            + "var bool: b :: output_var;\n"
            + "constraint int_lin_le_reif([1,-1,1],[x,y,a],0,b);\n"
            + "constraint int_lin_le([1,-1,1],[y,z,c],0);\n"
            + "constraint int_lin_le([1,-1],[z,x],-1);\n"
            + "solve :: bool_search([b],input_order,indomain_max,complete) satisfy;\n";
    long start = System.nanoTime();
    // a shorter time-out can pass while the model is built, before the search
    String out = run(model, "-t", "3000", "--lcg", "on")[0];
    long millis = (System.nanoTime() - start) / 1_000_000;
    // the propagation stopped at the deadline is no failure: b = false has solutions
    assertTrue(out.contains("=====UNKNOWN====="), out);
    assertFalse(out.contains("=====UNSATISFIABLE====="), out);
    // about 3 s; 40 s and an out of memory error before
    assertTrue(millis < 15_000, millis + " ms");
    // narrower domains: the propagation fails within the time-out, and b = false is the answer
    String narrow = model.replace("-500000000..500000000", "-2000..2000");
    out = run(narrow, "-t", "60000", "--lcg", "on")[0];
    assertTrue(out.contains("b = false;\n----------\n"), out);
  }

  @Test
  void roundOfCommonSubexpressionsStopsAtTheTimeOut() throws IOException, ParseException {
    // the time-out was checked once per round over the constraints, which takes seconds on a large
    // model
    StringBuilder model = new StringBuilder();
    int n = 600;
    for (int i = 0; i <= n; i++) {
      model.append("var 0..9: x").append(i).append(";\n");
    }
    for (int i = 0; i < n; i++) {
      model
          .append("constraint int_lin_le([1,-1],[x")
          .append(i)
          .append(", x")
          .append(i + 1)
          .append("], 0);\n");
    }
    model.append("solve satisfy;\n");
    Path fzn = tmp.resolve("cse.fzn");
    Files.writeString(fzn, model.toString(), StandardCharsets.UTF_8);
    for (boolean stop : new boolean[] {false, true}) {
      CheckCountingOptions opt =
          new CheckCountingOptions(new String[] {"-t", "60000", fzn.toString()});
      try (java.io.FileInputStream input = new java.io.FileInputStream(fzn.toFile())) {
        Parser parser = new Parser(input);
        parser.setOptions(opt);
        parser.cc.setOptions(opt);
        SimpleNode tree = parsedItems(parser);
        opt.armed = true;
        // nothing merges: one round, checked once at its start
        if (stop) {
          opt.passAfter = 1;
        }
        CommonSubexpressions cse = new CommonSubexpressions(parser.cc.support, Set.of());
        if (stop) {
          assertThrows(ModelTimeOut.class, () -> cse.detect(tree));
        } else {
          cse.detect(tree);
          assertTrue(cse.replaced().isEmpty());
          assertTrue(opt.checks > 1, opt.checks + " checks");
        }
      }
    }
  }

  /**
   * A portfolio reads the model before any of its threads starts, without looking at the time-out:
   * road_33 (86 MB) answered 1.9 s after -t 2000 from Portfolio.readModel on a slow disk. A model
   * that never arrives (a pipe no one writes) held the run for good; a command-line run ends a
   * second after its time-out, with UNKNOWN, as one thread does.
   */
  @Test
  void commandLinePortfolioEndsAtItsTimeOutWhileReading() throws IOException, InterruptedException {
    Path fifo = tmp.resolve("never.fzn");
    Process mkfifo;
    try {
      mkfifo = new ProcessBuilder("mkfifo", fifo.toString()).start();
    } catch (IOException e) {
      org.junit.jupiter.api.Assumptions.abort("no mkfifo: " + e.getMessage());
      return;
    }
    org.junit.jupiter.api.Assumptions.assumeTrue(
        mkfifo.waitFor(30, TimeUnit.SECONDS) && mkfifo.exitValue() == 0, "no named pipe");
    Path java = Path.of(System.getProperty("java.home"), "bin", "java");
    Path log = tmp.resolve("never.out");
    ProcessBuilder pb =
        new ProcessBuilder(
            java.toString(),
            "-cp",
            System.getProperty("java.class.path"),
            "org.jacop.fz.Fz2jacop",
            "-p",
            "2",
            "-t",
            "500",
            fifo.toString());
    pb.redirectErrorStream(true);
    pb.redirectOutput(log.toFile());
    // a writer that never writes nor closes the pipe: the run can open the model, and reading it
    // waits for good, as for a large model on a slow disk
    CountDownLatch testOver = new CountDownLatch(1);
    Thread writer =
        new Thread(
            () -> {
              try (OutputStream _ = Files.newOutputStream(fifo)) {
                testOver.await();
              } catch (IOException _) {
                // the test is over
              } catch (InterruptedException _) {
                Thread.currentThread().interrupt();
              }
            });
    writer.setDaemon(true);
    writer.start();
    Process p = pb.start();
    boolean ended = p.waitFor(60, TimeUnit.SECONDS);
    if (!ended) {
      p.destroyForcibly();
      p.waitFor(10, TimeUnit.SECONDS);
    }
    testOver.countDown();
    String out = Files.readString(log, StandardCharsets.UTF_8);
    assertTrue(ended, "still reading 60 s after -t 500: " + out);
    assertEquals(0, p.exitValue(), out);
    assertTrue(out.contains("=====UNKNOWN=====\n%% =====TIME-OUT====="), out);
  }

  /**
   * The watchdog of a portfolio prints the answer the run lacks once: the best solution, or
   * UNKNOWN, with the time-out; nothing once the answer is out, and no solution after its own.
   */
  @Test
  void portfolioWatchdogPrintsTheAnswerOnce() throws InterruptedException {
    Options options = new Options(new String[] {"-p", "2", "-t", "1000", "m.fzn"});
    int[] halts = new int[1];
    Runnable halt = () -> halts[0]++;
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream out = new PrintStream(buffer, true, StandardCharsets.UTF_8);

    Portfolio none = new Portfolio(options);
    none.timeLimit(out, System.currentTimeMillis(), halt);
    none.timeLimit(out, System.currentTimeMillis(), halt);
    assertEquals(
        "=====UNKNOWN=====\n%% =====TIME-OUT=====\n", buffer.toString(StandardCharsets.UTF_8));
    assertEquals(1, halts[0]);

    buffer.reset();
    Portfolio solved = new Portfolio(options);
    Portfolio.Worker w = solved.new Worker("w", List.of());
    w.solution("x = 7;\n----------\n", 7, false, new String[0], new int[0]);
    solved.timeLimit(out, System.currentTimeMillis(), halt);
    // a thread that finds a better solution once the watchdog fired is too late
    w.solution("x = 5;\n----------\n", 5, false, new String[0], new int[0]);
    solved.timeLimit(out, System.currentTimeMillis(), halt);
    assertEquals(
        "x = 7;\n----------\n%% =====TIME-OUT=====\n", buffer.toString(StandardCharsets.UTF_8));
    assertEquals(2, halts[0]);

    // started, it fires on its own after the delay
    buffer.reset();
    CountDownLatch fired = new CountDownLatch(1);
    PrintStream saved = System.out;
    Portfolio stuck = new Portfolio(options);
    try {
      System.setOut(out);
      stuck.startWatchdog(10, fired::countDown);
    } finally {
      System.setOut(saved);
    }
    assertTrue(fired.await(30, TimeUnit.SECONDS));
    assertEquals(
        "=====UNKNOWN=====\n%% =====TIME-OUT=====\n", buffer.toString(StandardCharsets.UTF_8));
  }

  @Test
  void freeSearchFirstKeepsTheClausesOfLcg() throws IOException {
    // a sum of four squares runs free search without learning before LCG when a time-out is given;
    // the clauses collected for LCG were not in its store, so it ignored b and printed x = 1
    String model =
        """
        var 0..3: x :: output_var;
        var -3..3: d;
        var -2..3: m;
        var 0..9: s1;
        var 2..13: u;
        var 0..168: s2;
        var 0..4: v;
        var 0..16: s3;
        var -5..7: w;
        var 0..49: s4;
        var -260..260: obj :: output_var;
        var bool: b :: output_var;
        constraint int_lin_eq([-1,2],[d,x],3);
        constraint int_max(d,-2,m);
        constraint int_times(m,m,s1);
        constraint int_times(u,u,s2);
        constraint int_pow(v,2,s3);
        constraint int_pow(w,2,s4);
        constraint int_lin_eq([1,1,1,3,-1],[s1,s2,s3,s4,obj],0);
        constraint int_le_reif(x, 0, b);
        constraint bool_clause([b], []);
        solve minimize obj;
        """;
    String out = run(model, "-t", "5000", "--lcg", "on")[0];
    assertTrue(out.endsWith("x = 0;\nobj = 8;\nb = true;\n----------\n==========\n"), out);
  }

  @Test
  void knapsackSurrogateKeepsBooleanItemsApart() throws IOException {
    // every Boolean variable has store index -1, so the detector merged d9 and d11 (bool2int
    // aliases of b3 and b7) into one item of the surrogate knapsack and refuted the model
    String model =
        """
        var 0..1: x0 :: output_var;
        var 0..1: x2 :: output_var;
        var bool: b3 :: output_var;
        var 0..1: x4 :: output_var;
        var 0..1: x6 :: output_var;
        var bool: b7 :: output_var;
        var 0..1: d8 :: output_var;
        var 0..1: d9 :: output_var;
        var 0..1: d10 :: output_var;
        var 0..1: d11 :: output_var;
        constraint bool2int(b3,d9);
        constraint bool2int(b7,d11);
        constraint int_lin_le([7,1,2],[x2,d9,x0],7);
        constraint int_lin_le([-2,-9,-7,-2,-4,-6,-1,-9],[x0,d8,x2,d9,x4,d10,x6,d11],-34);
        solve satisfy;
        """;
    // brute force: x2 = 1, x0 = d9 = 0, d8 = x4 = d10 = d11 = 1, x6 free
    assertEquals(2, solveAll(model).size());
  }

  @Test
  void maxCliqueKeepsConflictsOfAVariableDeclaredEqualToAVertex() throws IOException {
    // the sum names a = v0 and the conflicts name v0: the model was taken for pure maximum clique,
    // its conflicts were left to the bound, which holds those between vertices only, and z = 9
    StringBuilder model = new StringBuilder();
    for (int i = 0; i < 10; i++) {
      model.append("var 0..1: v").append(i).append(";\n");
    }
    model.append("var 0..1: a = v0;\nvar 0..10: z :: output_var;\n");
    for (int i = 1; i < 10; i++) {
      model.append("constraint int_lin_le([1,1],[v0,v").append(i).append("],1);\n");
    }
    model.append("constraint int_lin_le([1,1],[v1,v2],1);\n");
    model.append(
        "constraint int_lin_eq([1,1,1,1,1,1,1,1,1,1,-1],[a,v1,v2,v3,v4,v5,v6,v7,v8,v9,z],0);\n");
    model.append("solve maximize z;\n");
    for (String lcg : new String[] {"on", "off"}) {
      String out = run(model.toString(), "--lcg", lcg)[0];
      // v0 = 0 and one of v1, v2: 8
      assertTrue(out.endsWith("z = 8;\n----------\n==========\n"), out);
    }
  }

  @Test
  void emptySearchArraysSearchNothing() throws IOException {
    // MiniZinc may write a search over no variable or a sequence of no search; seq_search([]),
    // priority_search over [] and set_search or float_search over [] threw an exception
    String model =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
        constraint int_lt(x, y);
        solve :: %s satisfy;
        """;
    for (String ann :
        new String[] {
          "seq_search([])",
          "seq_search([seq_search([]), int_search([y], input_order, indomain_max, complete)])",
          "priority_search([], [], input_order, complete)",
          "set_search([], input_order, indomain_min, complete)",
          "float_search([], 0.1, input_order, indomain_split, complete)",
          "seq_search([float_search([], 0.1, input_order, indomain_split, complete),"
              + " int_search([x, y], input_order, indomain_min, complete)])"
        }) {
      String out = run(String.format(model, ann), "-a")[0];
      assertEquals(3, out.split("----------", -1).length - 1, ann + "\n" + out);
      assertTrue(out.contains("=========="), ann + "\n" + out);
    }
  }

  @Test
  void unknownVariableSelectionIsInputOrder() throws IOException {
    // the warning said input_order was used, and the search threw a NullPointerException
    String[] r =
        run(
            """
            var 1..3: x :: output_var;
            var 1..3: y :: output_var;
            constraint int_lt(x, y);
            solve :: int_search([x, y], no_such_heuristic, indomain_min, complete) satisfy;
            """,
            "-a");
    assertTrue(r[1].contains("no_such_heuristic"), r[1]);
    assertEquals(
        "x = 1;\ny = 2;\n----------\nx = 1;\ny = 3;\n----------\nx = 2;\ny = 3;\n----------\n==========\n",
        r[0]);
  }

  @Test
  void nestedSequenceSearchFollowsItsFirstSearch() throws IOException {
    // the master of seq_search([seq_search([a, b])]) was labelled with the selection of b: the
    // search branched on y before x, and a random selection shared by both searches printed a
    // solution with a variable not fixed ("Variable is not grounded in the solution")
    String order =
        run(
            """
            var 1..2: x :: output_var;
            var 1..2: y :: output_var;
            solve :: seq_search([seq_search([int_search([x], input_order, indomain_min, \
            complete), int_search([y], input_order, indomain_max, complete)])]) satisfy;
            """,
            "-a")[0];
    assertEquals(
        """
        x = 1;
        y = 2;
        ----------
        x = 1;
        y = 1;
        ----------
        x = 2;
        y = 2;
        ----------
        x = 2;
        y = 1;
        ----------
        ==========
        """,
        order);
    String out =
        run(
            """
            var 1..3: a :: output_var;
            var 1..2: k :: output_var;
            var -20..20: w :: output_var;
            solve :: seq_search([seq_search([int_search([w], input_order, indomain_min, \
            complete), int_search([k,w,a], random, indomain_min, complete)])]) satisfy;
            """,
            "-a")[0];
    assertEquals(41 * 2 * 3, out.split("----------", -1).length - 1, out);
    assertTrue(out.endsWith("==========\n"), out);
  }

  @Test
  void onRestartWithRestartsKeepsTheClausesOfLcg() throws IOException {
    // on_restart with restarts searches without learning, but the clauses collected for LCG were
    // never posted in the store: the at most one of a, b, c was ignored
    String model =
        """
        var 1..5: st :: output_var;
        var bool: a :: output_var;
        var bool: b :: output_var;
        var bool: c :: output_var;
        constraint jacop_on_restart_status(st);
        constraint bool_clause([],[a,b]);
        constraint bool_clause([],[b,c]);
        constraint bool_clause([],[a,c]);
        solve :: bool_search([a,b,c], input_order, indomain_max, complete) satisfy;
        """;
    for (String[] options :
        new String[][] {
          {"--lcg", "on", "--restart", "luby", "--lp", "off"},
          {"--lcg", "on", "-f", "--restart", "luby", "--lp", "off"}
        }) {
      String out = run(model, options)[0];
      assertTrue(out.contains("a = true;\nb = false;\nc = false;\n----------\n"), out);
    }
  }

  @Test
  void onRestartWithRestartsFailsOnAClauseFalseAtTheRoot() throws IOException {
    // the table fixes a and b before the clauses of a = b are posted for the restart search: its
    // first run failed at the root, the next runs forgot it and printed a = false, b = true
    String model =
        """
        var 1..5: st :: output_var;
        var bool: a :: output_var;
        var bool: b :: output_var;
        constraint jacop_on_restart_status(st);
        constraint bool_eq(a,b);
        constraint jacop_table_bool([a,b],[false,true]);
        solve :: bool_search([a,b], input_order, indomain_max, complete) satisfy;
        """;
    String out = run(model, "--lcg", "on", "--restart", "luby", "--lp", "off")[0];
    assertEquals("=====UNSATISFIABLE=====\n", out);
  }

  @Test
  void variablesNamedLikeGeneratedOnesKeepTheirConstraints() throws IOException {
    // the closed cardinality creates counters named counter0 and counter1, which hid the model's
    // own counter0 and counter1 from the store's constraints: the components missed the link
    // counter0 + counter1 <= 3, fixed counter0 = 2 with its own component and refuted the model
    String model =
        """
        var 1..2: a :: output_var;
        var 1..2: counter0 :: output_var;
        var 1..2: counter1 :: output_var;
        var 1..2: p1;
        var 1..2: p2;
        var 1..2: p3;
        var bool: r;
        var bool: s12;
        var bool: s13;
        var bool: s23;
        var 1..2: y1;
        var 1..2: y2;
        constraint int_ne(a, counter0);
        constraint int_lin_le([1,1],[counter0,counter1],3);
        constraint int_eq_reif(counter1, 1, r);
        constraint int_ne_reif(p1, p2, s12);
        constraint int_ne_reif(p1, p3, s13);
        constraint int_ne_reif(p2, p3, s23);
        constraint bool_clause([s12],[r]);
        constraint bool_clause([s13],[r]);
        constraint bool_clause([s23],[r]);
        constraint jacop_global_cardinality_low_up_closed([y1,y2],[1,2],[0,0],[2,2]);
        solve satisfy;
        """;
    // r = 1 puts three pigeons p1..p3 into two holes, so counter1 = 2, counter0 = 1 and a = 2
    String out = run(model)[0];
    assertEquals("a = 2;\ncounter0 = 1;\ncounter1 = 2;\n----------\n", out);
    assertEquals(1, solveAll(model).size());
  }

  @Test
  void variablesNamedLikeLatticeVariablesKeepTheirConstraints() throws IOException {
    // the market split system x1..x7 is reformulated over lattice variables named _lattice0_0,
    // _lattice0_1, ..., which hid the model's own _lattice0_0 and _lattice0_1 from the store's
    // constraints: the components missed _lattice0_0 + _lattice0_1 <= 3 and refuted the model
    String model =
        """
        var 0..1: x1;
        var 0..1: x2;
        var 0..1: x3;
        var 0..1: x4;
        var 0..1: x5;
        var 0..1: x6;
        var 0..1: x7;
        var 1..2: a :: output_var;
        var 1..2: _lattice0_0 :: output_var;
        var 1..2: _lattice0_1 :: output_var;
        var 1..2: p1;
        var 1..2: p2;
        var 1..2: p3;
        var bool: r;
        var bool: s12;
        var bool: s13;
        var bool: s23;
        var 1..2: y1;
        var 1..2: y2;
        constraint int_lin_eq([12,23,37,41,53,17,29],[x1,x2,x3,x4,x5,x6,x7],119);
        constraint int_lin_eq([31,13,27,19,11,43,22],[x1,x2,x3,x4,x5,x6,x7],99);
        constraint int_ne(a, _lattice0_0);
        constraint int_lin_le([1,1],[_lattice0_0,_lattice0_1],3);
        constraint int_eq_reif(_lattice0_1, 1, r);
        constraint int_ne_reif(p1, p2, s12);
        constraint int_ne_reif(p1, p3, s13);
        constraint int_ne_reif(p2, p3, s23);
        constraint bool_clause([s12],[r]);
        constraint bool_clause([s13],[r]);
        constraint bool_clause([s23],[r]);
        solve satisfy;
        """;
    // r = 1 puts three pigeons p1..p3 into two holes, so _lattice0_1 = 2, _lattice0_0 = 1, a = 2
    String out = run(model)[0];
    assertEquals("a = 2;\n_lattice0_0 = 1;\n_lattice0_1 = 2;\n----------\n", out);
  }

  @Test
  void anObjectiveThatIsNoIdentifierOfTheModelIsAnError() throws IOException {
    // minimizing an undeclared q was solved as satisfaction (and -a printed every solution, -p 2
    // no ==========), maximizing it threw a NullPointerException
    for (String sense : new String[] {"minimize", "maximize"}) {
      String model = "var 1..3: x :: output_var;\nsolve " + sense + " q;\n";
      for (String[] options : new String[][] {{}, {"-a"}, {"-p", "2"}}) {
        String[] out = run(model, options);
        assertEquals("", out[0], sense + " " + Arrays.toString(options));
        assertTrue(out[1].contains("%% Error: Symbol \"q\""), out[1]);
        assertEquals(1, lastStatus);
      }
    }
    // a parameter as objective is still solved
    assertEquals(
        "x = 1;\n----------\n==========\n",
        run("var 1..3: x :: output_var;\nint: c = 2;\nsolve minimize c;\n")[0]);
  }

  @Test
  void anUndefinedSymbolIsAnErrorOfTheModel() throws IOException {
    // an undeclared y threw a RuntimeException out of the run, a stack trace on the command line,
    // where -p 2 printed a message
    String model = "var 1..3: x :: output_var;\nconstraint int_le(x, y);\nsolve satisfy;\n";
    for (String[] options : new String[][] {{}, {"-p", "2"}}) {
      String[] out = run(model, options);
      assertEquals("", out[0], Arrays.toString(options));
      assertTrue(out[1].contains("%% Error: Symbol \"y\""), out[1]);
      assertEquals(1, lastStatus);
    }
  }

  @Test
  void aParameterInTheArrayOfASearchAnnotationIsAConstant() throws IOException {
    // a parameter in the array of a search was looked up as a variable only: the null in its place
    // threw a NullPointerException in every variable selection but input_order, and in set_search
    // and float_search
    String ints =
        "var 1..3: x :: output_var;\nint: c = 2;\n"
            + "solve :: int_search([c, x], first_fail, indomain_max, complete) satisfy;\n";
    assertEquals("x = 3;\n----------\n", run(ints)[0]);
    assertEquals(3, solveAll(ints).size());
    String sets =
        "var set of 1..3: s :: output_var;\nset of int: p = {1};\n"
            + "solve :: set_search([s, p], first_fail, indomain_min, complete) satisfy;\n";
    assertEquals(8, solveAll(sets).size());
    String floats =
        "var 1.0..3.0: f :: output_var;\nfloat: p = 1.0;\n"
            + "solve :: float_search([f, p], 0.1, input_order, indomain_split, complete) satisfy;\n";
    assertTrue(run(floats)[0].endsWith("----------\n"), run(floats)[0]);
  }

  @Test
  void boolSearchWithIndomainMiddleOrMedianLabelsTheBooleans() throws IOException {
    // indomain_middle and indomain_median refused the bounds domain of a Boolean variable under
    // jacop.asserts.enabled, although they label it like any other domain (as they did without it)
    for (String value : List.of("indomain_middle", "indomain_median")) {
      String model =
          """
          var bool: a :: output_var;
          var bool: b :: output_var;
          var bool: c :: output_var;
          constraint bool_clause([a,b],[c]);
          solve :: bool_search([a,b,c], input_order, %s, complete) satisfy;
          """
              .formatted(value);
      assertEquals(7, solveAll(model).size(), value);
    }
  }

  /**
   * The shutdown hook of a portfolio (a run with -s killed by SIGTERM) prints the answer while the
   * threads still run: a solution a thread finds after it is not printed under -a, after the
   * status.
   */
  @Test
  void portfolioPrintsNoSolutionAfterItsAnswerAtShutdown() {
    Options options = new Options(new String[] {"-p", "2", "-a", "-t", "1000", "m.fzn"});
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream out = new PrintStream(buffer, true, StandardCharsets.UTF_8);
    PrintStream saved = System.out;
    try {
      System.setOut(out);
      Portfolio portfolio = new Portfolio(options);
      Portfolio.Worker w = portfolio.new Worker("w", List.of());
      portfolio.printAtShutdown(out, System.currentTimeMillis());
      w.solution("x = 5;\n----------\n", 5, false, new String[0], new int[0]);
    } finally {
      System.setOut(saved);
    }
    assertEquals(
        "=====UNKNOWN=====\n%% =====TIME-OUT=====\n", buffer.toString(StandardCharsets.UTF_8));
  }

  /**
   * The shutdown hook of a run with -s (SIGTERM) prints the answer while the search runs: once the
   * search printed its answer, the hook prints no second one after its status (the best solution
   * again after ==========, 2 of 63 runs killed near their end).
   */
  @Test
  void theShutdownHookPrintsNoSecondAnswer() throws IOException, ParseException {
    Path fzn = tmp.resolve("hook.fzn");
    Files.writeString(
        fzn,
        """
        var 0..9: x :: output_var;
        var 0..9: y :: output_var;
        constraint int_lin_le([1, 1], [x, y], 12);
        constraint int_ne(x, y);
        solve :: int_search([x, y], input_order, indomain_min, complete) maximize x;
        """,
        StandardCharsets.UTF_8);
    Options opt =
        new Options(new String[] {"-s", "--lcg", "off", "--presolve", "off", fzn.toString()});
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8);
        java.io.FileInputStream input = new java.io.FileInputStream(fzn.toFile())) {
      System.setOut(capture);
      Parser parser = new Parser(input);
      parser.setOptions(opt);
      parser.model();
      new RunWhenShuttingDown(parser).run();
    } finally {
      System.setOut(originalOut);
    }
    String out = buffer.toString(StandardCharsets.UTF_8);
    assertEquals(1, out.split("----------", -1).length - 1, out);
    assertTrue(out.strip().contains("==========\n"), out);
    assertEquals(out.indexOf("x = 9;"), out.lastIndexOf("x = 9;"), out);
  }

  @Test
  void anInvalidOptionValueIsAnErrorOfTheCommandLine() throws IOException {
    // -t abc and the others threw a NumberFormatException out of the run, a stack trace
    String model = "var 1..3: x :: output_var;\nsolve satisfy;\n";
    Map<List<String>, String> options =
        Map.of(
            List.of("-t", "abc"),
            "option -t: abc is not a valid number",
            List.of("-p", "x"),
            "option -p: x is not a valid number",
            List.of("-n", "q"),
            "option -n: q is not a valid number",
            List.of("-d", "z"),
            "option -d: z is not a valid number",
            List.of("-r", "1.5"),
            "option -r: 1.5 is not a valid number",
            List.of("--gap", "x"),
            "--gap x: not a number",
            List.of("-p", "2", "--free-config", "portfolio-split=x"),
            "option --free-config portfolio-split=x: not a number");
    for (Map.Entry<List<String>, String> o : options.entrySet()) {
      String[] out = run(model, o.getKey().toArray(new String[0]));
      assertEquals("", out[0], o.getKey().toString());
      assertEquals("%% Error: " + o.getValue() + "\n", out[1], o.getKey().toString());
      assertEquals(1, lastStatus, o.getKey().toString());
    }
    String valid = run(model, "-n", "1")[0];
    assertTrue(valid.startsWith("x = 1;\n----------\n"), valid);
  }

  @Test
  void anEmptyOutputArrayIsPrintedUnderAsserts() throws IOException {
    // output_array([1..0]) of an empty array, which MiniZinc writes, made IntervalDomain(1, 0) and
    // failed under jacop.asserts.enabled (as the tests run); without it the array was printed
    assertEquals(
        "x = 1;\nb = array1d({}, []);\n----------\n",
        run(
            "var 1..3: x :: output_var;\n"
                + "array [1..0] of var int: b :: output_array([1..0]) = [];\nsolve satisfy;\n")[0]);
  }

  @Test
  void symmetryBreakingDoesNotChannelSetsWithElementsFarApart() throws IOException {
    // the channel of a set variable that symmetries move makes one Boolean per value from the
    // smallest to the largest element of its upper bound: 300,001 here (and out of memory for
    // {-100000000, 100000000}), so such sets keep a colour of their own
    String out =
        run(
            "var set of {0, 300000}: s0 :: output_var;\n"
                + "var set of {0, 300000}: s1 :: output_var;\n"
                + "constraint set_union(s0, s1, {0, 300000});\n"
                + "solve :: set_search([s0, s1], input_order, indomain_min, complete) satisfy;\n",
            "-s",
            "-v",
            "--symmetry",
            "on")[0];
    assertTrue(out.contains("s0 = {0, 300000};"), out);
    assertTrue(out.contains("%%%mzn-stat: symmetryConstraints=0\n"), out);
  }

  @Test
  void setVariablesThatAreNotOutputAreCompleted() throws IOException {
    // after the search on the output variables the completion search labelled only the integer and
    // Boolean variables left: s0 = {-5} with b0 = false was printed, although s1 != {-5} makes s1
    // empty and so a subset of s2
    String model =
        "var set of {-5, 0}: s0 :: output_var;\n"
            + "var set of -5..-5: s1;\n"
            + "var set of {-5, 0}: s2;\n"
            + "var bool: b0 :: output_var;\n"
            + "constraint set_superset_reif(s2, s1, b0);\n"
            + "constraint set_ne(s1, s0);\n"
            + "solve :: set_search([s0], input_order, indomain_min, complete) satisfy;\n";
    List<String> all = solveAllInOrder(model, "--lcg", "off");
    assertEquals(7, all.size(), all.toString());
    assertFalse(all.contains("b0 = false; s0 = -5..-5;"), all.toString());
  }

  @Test
  void floatVariablesThatAreNotOutputAreCompleted() throws IOException {
    // the completion search after the search on the output variables labelled only the integer
    // and Boolean variables: a = 1 was printed, although it asks f * g >= 0.1 with g = -f
    String model =
        "var 0..1: a :: output_var;\n"
            + "var -1.0..1.0: f;\n"
            + "var -1.0..1.0: g;\n"
            + "var -1.0..1.0: h;\n"
            + "var bool: b;\n"
            + "constraint float_lin_eq([1.0, 1.0], [f, g], 0.0);\n"
            + "constraint float_times(f, g, h);\n"
            + "constraint int_eq_reif(a, 1, b);\n"
            + "constraint float_le_reif(0.1, h, b);\n"
            + "solve :: int_search([a], input_order, indomain_min, complete) satisfy;\n";
    List<String> all = solveAllInOrder(model, "--lcg", "off");
    assertEquals(List.of("a = 0;"), all, all.toString());
  }

  @Test
  void floatObjectiveImprovesFromSolutionToSolution() throws IOException {
    // with precision 0.01 the objective of a solution is an interval up to 0.01 wide, printed as
    // its middle; each next solution had only to raise its minimum by one float, so the printed
    // objective went down: 5.8786, 5.8775, 5.8757
    String model =
        "var -1000.0..1000.0: x :: output_var;\n"
            + "var -10.0..10.0: y :: output_var;\n"
            + "var -2..2: i :: output_var;\n"
            + "var -1000.0..1000.0: fi;\n"
            + "var -1.0e9..1.0e9: obj :: output_var;\n"
            + "constraint int2float(i, fi);\n"
            + "constraint float_lin_le([2.63,2.76,-2.14],[x,y,fi],6.07);\n"
            + "constraint float_lin_le([1.75,0.9,-2.71],[x,y,fi],-3.27);\n"
            + "constraint float_lin_eq([-1.09,2.77,0.86],[x,y,fi],6.16);\n"
            + "constraint float_lin_eq([0.53,-2.22,-0.49,-1.0],[x,y,fi,obj],0.0);\n"
            + "solve :: float_search([x,y],0.01,input_order,indomain_split,complete)"
            + " maximize obj;\n";
    List<String> all = solveAllInOrder(model, "--lcg", "off");
    double last = Double.NEGATIVE_INFINITY;
    for (String solution : all) {
      Matcher m = Pattern.compile("obj = ([-0-9.Ee]+);").matcher(solution);
      assertTrue(m.find(), solution);
      double obj = Double.parseDouble(m.group(1));
      assertTrue(obj > last, all.toString());
      last = obj;
    }
  }

  @Test
  void statisticsCountTheSolutionsReportedWithACompletionOfHiddenFloats() throws IOException {
    // the search on a, the completion of b and the float completion of f, g and h each counted
    // solutions of their own, and the statistics took the completion's count: solutions=2 for
    // the one solution a = 0
    String model =
        "var 0..1: a :: output_var;\n"
            + "var -1.0..1.0: f;\n"
            + "var -1.0..1.0: g;\n"
            + "var -1.0..1.0: h;\n"
            + "var bool: b;\n"
            + "constraint float_lin_eq([1.0, 1.0], [f, g], 0.0);\n"
            + "constraint float_times(f, g, h);\n"
            + "constraint int_eq_reif(a, 1, b);\n"
            + "constraint float_le_reif(0.1, h, b);\n"
            + "solve :: int_search([a], input_order, indomain_min, complete) satisfy;\n";
    String out = run(model, "-a", "-s", "--lcg", "off")[0];
    assertEquals(1, out.lines().filter(l -> l.equals("----------")).count(), out);
    assertTrue(out.contains("%%%mzn-stat: solutions=1\n"), out);
  }

  @Test
  void floatVariablesThatAreNotOutputAreCompletedUnderAFloatObjective() throws IOException {
    // the float completion was left out under a float objective: a = 1 with obj = 1.0 was printed
    // as the optimum, although a = 1 asks f * g >= 0.1 with g = -f
    String model =
        "var 0..1: a :: output_var;\n"
            + "var -1.0..1.0: f;\n"
            + "var -1.0..1.0: g;\n"
            + "var -1.0..1.0: h;\n"
            + "var 0.0..1.0: obj :: output_var;\n"
            + "var bool: b;\n"
            + "constraint int2float(a, obj);\n"
            + "constraint float_lin_eq([1.0, 1.0], [f, g], 0.0);\n"
            + "constraint float_times(f, g, h);\n"
            + "constraint int_eq_reif(a, 1, b);\n"
            + "constraint float_le_reif(0.1, h, b);\n"
            + "solve :: int_search([a], input_order, indomain_min, complete) maximize obj;\n";
    List<String> all = solveAllInOrder(model, "--lcg", "off");
    assertEquals(List.of("a = 0; obj = 0.0;"), all, all.toString());
  }

  @Test
  void floatPowWithASingletonExponentKeepsItsSolutions() throws IOException {
    // with precision 0.01 the exponent 1.995..2.004 counted as the constant 1.995, its lower end,
    // and 10^1.995 = 98.86 is outside z: UNSATISFIABLE, although 10^2 = 100 is a solution
    String model =
        "var 10.0..10.0: x :: output_var;\n"
            + "var 1.995..2.004: y :: output_var;\n"
            + "var 99.5..100.5: z :: output_var;\n"
            + "constraint float_pow(x, y, z);\n"
            + "solve satisfy;\n";
    String out = run(model, "--precision", "0.01")[0];
    assertTrue(out.contains("----------"), out);
  }

  @Test
  void floatDomainBeyondTheFloatRangeHasNoValue() throws IOException {
    // 1.5e308..1.5e308 is above JaCoP's float range 1e150: the bounds became 1.5e308..1e150, an
    // inverted domain, and x = 7.5E307 (outside the declared domain) was printed as a solution
    String model =
        "var 1.5e308..1.5e308: x :: output_var;\n"
            + "var -1.0..1.0: y :: output_var;\n"
            + "constraint float_le(y, 0.5);\n"
            + "solve satisfy;\n";
    String out = run(model)[0];
    assertFalse(out.contains("x = "), out);
    assertTrue(out.contains("=====UNKNOWN====="), out);
  }

  @Test
  void theBinCompletionHintLeavesTheRootSolveOfTheRelaxationAtTheRoot() throws IOException {
    // the hint fixed the objective to its bound at a level of its own, where propagation failed
    // before the linear relaxation, queued since its imposition, ran: removing the level dropped
    // it from the queue, and its first solve came at a probe of LCG's root, whose bounds its cuts
    // took as the root's; -f reported 7 instead of the optimum 3
    StringBuilder model = new StringBuilder();
    for (int i = 0; i <= 10; i++) {
      model.append("var 0..1: s").append(i).append(" :: output_var;\n");
    }
    model.append("var 1..9: it :: output_var;\n");
    for (int b = 0; b <= 8; b++) {
      model.append("var 0..1: ld").append(b).append(" :: output_var;\n");
    }
    model
        .append("var 0..39: obj :: output_var;\n")
        .append("constraint int_lin_le([-3,-4],[s9,s0],-5);\n")
        .append("constraint int_lin_le([-4,-1,-3],[s5,s1,s8],-3);\n")
        .append("constraint jacop_bin_packing([it],[ld0,ld1,ld2,ld3,ld4,ld5,ld6,ld7,ld8],[1],1);\n")
        .append("constraint int_lin_eq([1,4,4,4,5,1,5,5,5,1,3,1,-1],")
        .append("[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ld0,obj],0);\n")
        .append("solve minimize obj;\n");
    for (String[] options :
        new String[][] {{"-f", "--lcg", "on"}, {"--lcg", "on"}, {"--lcg", "off", "--lp", "off"}}) {
      String out = run(model.toString(), options)[0];
      assertTrue(
          out.contains("obj = 3;\n----------\n=========="), String.join(" ", options) + ": " + out);
    }
  }

  @Test
  void binPackingCostBoundSkipsLoadsWhereTheCostIsUndefined() throws IOException {
    // y = T[load - 1] is undefined for loads 0 and 1, which LoadFunctionDetector marks with
    // Long.MIN_VALUE; the enumeration took that as a cost, its sums wrapped, it cut the packing of
    // cost -6 and posted the sum of the costs >= -4, so every search reported the optimum 0
    StringBuilder model = new StringBuilder();
    model
        .append("var 1..3: b0 :: output_var;\n")
        .append("var {1,3}: b1 :: output_var;\n")
        .append("var 1..1: b2 :: output_var;\n")
        .append("var 1..3: b3 :: output_var;\n")
        .append("var 1..3: b4 :: output_var;\n");
    for (int p = 0; p < 3; p++) {
      model
          .append("var 0..13: l")
          .append(p)
          .append(" :: output_var;\n")
          .append("var -5..20: d")
          .append(p)
          .append(";\n")
          .append("var -10..20: y")
          .append(p)
          .append(" :: output_var;\n");
    }
    model
        .append("var -100..100: obj :: output_var;\n")
        .append("constraint jacop_bin_packing([b0,b1,b2,b3,b4],[l0,l1,l2],[3,2,2,3,3],1);\n");
    for (int p = 0; p < 3; p++) {
      model
          .append("constraint int_lin_eq([1,-1],[l")
          .append(p)
          .append(",d")
          .append(p)
          .append("],1);\n")
          .append("constraint array_int_element(d")
          .append(p)
          .append(",[6,-2,9,7,4,-2,-4,3,0,8,-3,-4],y")
          .append(p)
          .append(");\n");
    }
    model
        .append("constraint int_lin_eq([1,1,1,-1],[y0,y1,y2,obj],0);\n")
        .append("solve minimize obj;\n");
    for (String[] options : new String[][] {{"--lcg", "on"}, {"--lcg", "off"}, {"-f"}}) {
      String out = run(model.toString(), options)[0];
      assertTrue(
          out.contains("obj = -6;\n----------\n=========="),
          String.join(" ", options) + ": " + out);
    }
  }

  void aSearchOverUndeclaredSymbolsOrSymbolsOfAnotherTypeIsAnError() throws IOException {
    // the thread that followed the annotation threw a NullPointerException (or ignored an
    // undeclared q under input_order), while -f and the other threads of -p 2 solved the model
    String head = "var 1..3: x :: output_var;\nvar set of 1..3: s :: output_var;\n";
    Map<String, String> searches =
        Map.of(
            "int_search(qq, input_order, indomain_min, complete)",
            "\"qq\" does not",
            "int_search([x, q], input_order, indomain_min, complete)",
            "\"q\" does not",
            "int_search([x, q], first_fail, indomain_min, complete)",
            "\"q\" does not",
            "int_search([s], input_order, indomain_min, complete)",
            "\"s\" in int_search",
            "set_search([x], input_order, indomain_min, complete)",
            "\"x\" in set_search",
            "float_search([x], 0.1, input_order, indomain_split, complete)",
            "\"x\" in float_search",
            "seq_search([int_search([x], input_order, indomain_min, complete),"
                + " int_search([q], input_order, indomain_min, complete)])",
            "\"q\" does not");
    for (Map.Entry<String, String> search : searches.entrySet()) {
      String model = head + "solve :: " + search.getKey() + " satisfy;\n";
      for (String[] options : new String[][] {{}, {"-f"}, {"-p", "2"}}) {
        String[] out = run(model, options);
        String what = search.getKey() + " " + Arrays.toString(options);
        assertEquals("", out[0], what);
        assertTrue(out[1].contains("%% Error: Symbol " + search.getValue()), what + out[1]);
        assertEquals(1, lastStatus, what);
      }
    }
    // a Boolean in int_search and an integer in bool_search are still searched
    assertEquals(
        6,
        solveAll(
                "var 1..3: x :: output_var;\nvar bool: b :: output_var;\n"
                    + "solve :: seq_search([int_search([b], input_order, indomain_min, complete),"
                    + " bool_search([x], input_order, indomain_min, complete)]) satisfy;\n")
            .size());
  }

  @Test
  void constraintArgumentsOfAnotherTypeNumberOrLengthAreAnError() throws IOException {
    // a set where an integer is expected threw a ClassCastException, an undeclared array of
    // coefficients a NullPointerException (and -p 2 printed a message instead), int_le with three
    // arguments was solved as int_le with two, coefficients beyond the variables were dropped
    String head =
        "var 1..3: x :: output_var;\nvar 1..3: y :: output_var;\nvar bool: b :: output_var;\n";
    Map<String, String> constraints =
        Map.of(
            "int_le(x, {1,2})",
            "Argument 2 of constraint int_le is not of type var int",
            "int_lin_le(w, [x], 3)",
            "Symbol \"w\" does not have assigned value",
            "int_le(x, y, 3)",
            "Constraint int_le has 3 arguments, its predicate takes 2",
            "int_lin_le([1,1,1], [x,y], 3)",
            "Arguments 1 and 2 of constraint int_lin_le",
            "array_bool_and([b, {1}], b)",
            "Argument 1 of constraint array_bool_and",
            "int_lin_eq([1], x, 3)",
            "Argument 2 of constraint int_lin_eq",
            "jacop_regular([x], 1, 3, [1,0], 1, {1}, 1)",
            "The arguments of constraint jacop_regular do not fit",
            "bool_and(x, b, b)",
            "Argument 1 of constraint bool_and is not of type var bool",
            // a transition to a state the automaton does not have was an internal error
            "jacop_regular([x], 1, 1, [2], 1, {1}, 1)",
            "The arguments of constraint jacop_regular do not fit",
            "jacop_networkflow([1,2], [x], [x, y], [0,0], x)",
            "Arguments 2 and 3 of constraint jacop_networkflow");
    for (Map.Entry<String, String> c : constraints.entrySet()) {
      String model = head + "constraint " + c.getKey() + ";\nsolve satisfy;\n";
      for (String[] options :
          new String[][] {{}, {"-f"}, {"--lcg", "on"}, {"-p", "2"}, {"--presolve", "on"}}) {
        String[] out = run(model, options);
        String what = c.getKey() + " " + Arrays.toString(options);
        assertEquals("", out[0], what);
        assertTrue(out[1].contains("%% Error: " + c.getValue()), what + out[1]);
        assertFalse(out[1].contains("Exception"), what + out[1]);
        assertEquals(1, lastStatus, what);
      }
    }
    // a Boolean where an integer is expected, a 0..1 integer where a Boolean is, are still read:
    // b = 0 with any y and x in 1..2, or b = 1 with y = 1 and x = 2
    assertEquals(
        5,
        solveAll(
                head.replace("1..3: y", "0..1: y")
                    + "constraint int_lt(b, x);\n"
                    + "constraint bool_and(y, b, b);\nconstraint int_le(x, 2);\nsolve satisfy;\n")
            .size());
    // a network without arcs threw a NoSuchElementException; its cost is 0
    assertEquals(
        Set.of("c = 0;"),
        solveAll(
            "var 0..3: c :: output_var;\nconstraint jacop_networkflow([], [], [], [0], c);\n"
                + "solve satisfy;\n"));
  }
}
