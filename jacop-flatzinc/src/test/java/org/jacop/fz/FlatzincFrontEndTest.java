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
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.StringJoiner;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.jacop.floats.core.FloatDomain;
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

  @Test
  void completionSearchBacktracksToTheLastConflict() throws IOException {
    // The variables the annotation leaves out are labelled by a search JaCoP adds. Without last
    // conflict it tried every assignment of a1..a8 before finding that z1..z4 never fit (3072
    // failures); with it z is branched on first again after each failure (kidney-exchange,
    // MiniZinc Challenge 2023: 4.7 million nodes against Choco's 22 thousand).
    String out = run(pigeonsAfterFreeVariables(3), "-s")[0];
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    int failures = Integer.parseInt(out.replaceAll("(?s).*%%%mzn-stat: failures=(\\d+).*", "$1"));
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
    assertTrue(out.contains("x = 1.4142135623730951;"), out);
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
    int[] var = new int[k];
    for (int i = 0; i < k; i++) {
      lo[i] = bools ? 0 : rnd.nextInt(7) - 3;
      hi[i] = bools ? 1 : lo[i] + rnd.nextInt(4);
      var[i] = i > 0 && rnd.nextInt(5) == 0 ? var[rnd.nextInt(i)] : i;
    }
    StringBuilder fzn = new StringBuilder();
    StringJoiner args = new StringJoiner(",");
    for (int i = 0; i < k; i++) {
      if (var[i] == i) {
        fzn.append(bools ? "var bool" : "var " + lo[i] + ".." + hi[i]).append(": x").append(i);
        fzn.append(":: output_var;\n");
      }
      args.add("x" + var[i]);
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
        var,
        () -> {
          for (int i = 0; i < k; i++) {
            value[i] = v[var[i]];
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
            if (var[i] == i) {
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
      int i, int[] v, int[] lo, int[] hi, int[] var, Runnable check) {
    if (i == v.length) {
      check.run();
      return;
    }
    if (var[i] != i) {
      enumerateBuiltin(i + 1, v, lo, hi, var, check);
      return;
    }
    for (v[i] = lo[i]; v[i] <= hi[i]; v[i]++) {
      enumerateBuiltin(i + 1, v, lo, hi, var, check);
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
    // search proves nothing about the values cut off.
    String fzn =
        """
        var 0..4722438400: x :: output_var;
        constraint int_le(x, 3);
        solve maximize x;
        """;
    String[] out = run(fzn);
    assertEquals(0, lastStatus, out[1]);
    assertTrue(out[0].endsWith("x = 3;\n----------\n"), out[0]);
    assertTrue(out[1].contains("1 variable domain reaches beyond"), out[1]);
    assertTrue(out[1].contains("(first: x 0..4722438400)"), out[1]);

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
    // maximised, the values cut off are the better ones
    out =
        run(
            """
            var 0..2014326920: c :: output_var;
            var 1..5: y :: output_var;
            constraint int_lin_eq([1, -2], [c, y], 0);
            solve maximize c;
            """);
    assertTrue(out[0].endsWith("c = 10;\ny = 5;\n----------\n"), out[0]);
    // an array element of the objective's array narrowed too: no claim
    out =
        run(
            """
            array [1..2] of var 0..2014326920: a :: output_array([1..2]);
            constraint int_le(a[2], 4);
            solve minimize a[1];
            """);
    assertFalse(out[0].contains("=========="), out[0]);
  }

  @Test
  void domainWhollyOutsideIntegerRangeIsRejected() throws IOException {
    String[] out = run("var 600000000..700000000: x :: output_var;\nsolve satisfy;\n");
    assertEquals("", out[0]);
    assertTrue(out[1].contains("domain 600000000..700000000 at line 1"), out[1]);
    assertTrue(out[1].contains("lies outside the integer range"), out[1]);
    assertEquals(1, lastStatus);
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

    String out = run(fzn.toString(), "-t", "300")[0];
    assertTrue(!out.contains("=====UNSATISFIABLE====="), out);
    assertTrue(out.contains("=====UNKNOWN====="), out);
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
  void lcgSplitsLongLinearConstraintsAndKeepsTheOptimum() throws IOException {
    // --lcg splits a linear constraint of more than 40 terms into sums of blocks of about
    // sqrt(n) terms: the optimum stays that of the flat constraints and of the CP solver, and the
    // linear reasons, about 32 atoms on the flat sums, get below 16
    java.util.Random rnd = new java.util.Random(3);
    for (int run = 0; run < 12; run++) {
      int n = 60;
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
      String flat = lastObjective(run(model.toString(), "--lcg", "--free-config", "lcg-split=0"));
      String cp = lastObjective(run(model.toString()));
      String[] split = run(model.toString(), "--lcg", "-s");
      assertEquals(cp, flat, model.toString());
      assertEquals(cp, lastObjective(split), model.toString());
      java.util.regex.Matcher m =
          java.util.regex.Pattern.compile("%% lcg LinearInt: reasons=(\\d+) .*?avgAtoms=([0-9.]+)")
              .matcher(split[0]);
      if (m.find() && Long.parseLong(m.group(1)) > 0) {
        assertTrue(Double.parseDouble(m.group(2)) < 16, split[0]);
      }
    }
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
    // the full fixpoint of the store (#317) paid on optimisation models but not on satisfaction
    // models: nonogram non_fast_3 took 39 to 57 s instead of 4 to 6 s
    String model =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
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
    String out =
        run(
            model.toString(),
            "--lcg",
            "-f",
            "--search-statistics",
            "--free-config",
            "lcg-branching=activity")[0];
    assertTrue(out.strip().contains("=========="), out);
    String late = out.substring(out.indexOf("lcgLateVariables=") + 17);
    // obj, the objective, and the block sums of the two long constraints
    assertTrue(Integer.parseInt(late.substring(0, late.indexOf('\n')).strip()) > 10, out);
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
    String out = run(model.toString(), "--lcg", "-f", "-debug")[0];
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
      String out = run(model.toString(), "--lcg", "-t", "100")[0];
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
  void defaultLcgIsLeftOutForFloatModelsAndAllSolutionsOfSatisfactionProblems() throws IOException {
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
      // asked for, LCG is still reported as ignored
      assertTrue(run(sat, "-a", "--lcg")[0].contains("--lcg ignored"));
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
    return new String[] {
      out.toString(StandardCharsets.UTF_8), err.toString(StandardCharsets.UTF_8)
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
}
