/*
 * LocalSearchFlatzincTest.java
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

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of local search before free search (--free-config ls). Under --lcg the clauses of the model
 * go to the SAT solver, not to the store, so local search must evaluate them itself: a solution
 * that violated one, checked only in the store, gave a wrong optimum on amaze.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class LocalSearchFlatzincTest {

  @TempDir Path tmp;

  // a smallest vertex cover of a cycle of six vertices: 3
  private static final String COVER =
      """
      var bool: x1:: output_var;
      var bool: x2:: output_var;
      var bool: x3:: output_var;
      var bool: x4:: output_var;
      var bool: x5:: output_var;
      var bool: x6:: output_var;
      var 0..6: cost:: output_var:: is_defined_var;
      constraint bool_clause([x1,x2],[]);
      constraint bool_clause([x2,x3],[]);
      constraint bool_clause([x3,x4],[]);
      constraint bool_clause([x4,x5],[]);
      constraint bool_clause([x5,x6],[]);
      constraint bool_clause([x6,x1],[]);
      constraint bool_lin_eq([1,1,1,1,1,1],[x1,x2,x3,x4,x5,x6],cost):: defines_var(cost);
      """;

  private static final Pattern COST = Pattern.compile("cost = (\\d+);");

  @Test
  void optimumUnderLcg() throws IOException {
    // -a as MiniZinc passes it for optimisation: local search runs and its solutions are printed
    String out =
        run(
            COVER + "solve minimize cost;\n",
            "--lcg",
            "-f",
            "-a",
            "--search-statistics",
            "-t",
            "5000");
    assertFalse(out.contains("lsSolutions=0") || !out.contains("lsSolutions="), out);
    checkOptimum(out);
  }

  @Test
  void optimumUnderFreeSearch() throws IOException {
    checkOptimum(
        run(COVER + "solve minimize cost;\n", "-f", "-a", "--search-statistics", "-t", "5000"));
  }

  @Test
  void satisfactionUnderLcgPrintsAValidSolution() throws IOException {
    String out =
        run(
            COVER + "constraint int_le(cost,3);\nsolve satisfy;\n",
            "--lcg",
            "-f",
            "--search-statistics",
            "-t",
            "5000");
    assertTrue(out.contains("lsSolutions=1"), out);
    boolean[] x = new boolean[7];
    for (int i = 1; i <= 6; i++) {
      x[i] = out.contains("x" + i + " = true;");
    }
    for (int i = 1; i <= 6; i++) {
      assertTrue(x[i] || x[i % 6 + 1], "edge " + i + " uncovered: " + out);
    }
  }

  /**
   * The redundant constraints the FlatZinc layer adds next to the model's own are marked implied
   * and local search leaves them out: the cumulative projections of a diffn, and the all different
   * of a circuit, unless the model itself states that all different.
   */
  @Test
  void redundantConstraintsAreNotEvaluated() throws IOException {
    StringBuilder squares = new StringBuilder("array [1..4] of int: s = [2,2,2,2];\n");
    for (int i = 1; i <= 4; i++) {
      squares.append("var 0..2: x").append(i).append(":: output_var;\n");
      squares.append("var 0..2: y").append(i).append(":: output_var;\n");
    }
    squares.append("constraint jacop_diff2_strict([x1,x2,x3,x4],[y1,y2,y3,y4],s,s);\n");
    squares.append("solve satisfy;\n");
    String out = run(squares.toString(), "--lcg", "off", "-f", "-debug", "--search-statistics");
    assertTrue(out.contains("I:Cumulative=2"), out);
    assertTrue(out.contains("lsSolutions=1"), out);

    int n = 30;
    StringBuilder tour = new StringBuilder();
    StringBuilder next = new StringBuilder("[");
    for (int i = 1; i <= n; i++) {
      tour.append("var 1..").append(n).append(": v").append(i).append(":: output_var;\n");
      next.append(i > 1 ? "," : "").append('v').append(i);
    }
    next.append(']');
    tour.append("constraint jacop_circuit(").append(next).append(");\n");
    out = run(tour + "solve satisfy;\n", "--lcg", "off", "-f", "-debug", "--search-statistics");
    assertTrue(out.contains("I:Alldistinct=1"), out);
    assertTrue(out.contains("lsSolutions=1"), out);
    // stated by the model too, the all different is the model's
    String both = tour + "constraint jacop_alldistinct(" + next + ");\nsolve satisfy;\n";
    out = run(both, "--lcg", "off", "-f", "-debug", "--search-statistics");
    assertFalse(out.contains("I:Alldistinct"), out);
    assertTrue(out.contains("lsSolutions=1"), out);
  }

  /**
   * Local search leaves out the symmetry breaking constraints JaCoP adds to a colouring of a cycle
   * (value precedence, lex-leader of the rotations) and the solution it prints is a colouring.
   */
  @Test
  void symmetryBreakingIsNotEvaluated() throws IOException {
    int n = 12;
    StringBuilder model = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      model.append("var 1..4: x").append(i).append(":: output_var;\n");
    }
    for (int i = 1; i <= n; i++) {
      model.append("constraint int_ne(x").append(i).append(",x").append(i % n + 1).append(");\n");
      model.append("constraint int_ne(x").append(i).append(",x");
      model.append((i + 1) % n + 1).append(");\n");
    }
    model.append("solve satisfy;\n");
    String out =
        run(
            model.toString(),
            "--symmetry",
            "on",
            "--lcg",
            "off",
            "-f",
            "-debug",
            "--search-statistics",
            "-t",
            "5000");
    assertTrue(out.contains("S:SeqPrecedeChain=1"), out);
    assertTrue(out.contains("lsSolutions=1"), out);
    int[] x = new int[n + 1];
    Matcher m = Pattern.compile("x(\\d+) = (\\d+);").matcher(out);
    while (m.find()) {
      x[Integer.parseInt(m.group(1))] = Integer.parseInt(m.group(2));
    }
    for (int i = 1; i <= n; i++) {
      assertTrue(x[i] != x[i % n + 1] && x[i] != x[(i + 1) % n + 1], out);
    }
  }

  /** Columns are sorted, interchangeable values renamed by first use, and lex-leaders descended. */
  @Test
  void canonicalizerMovesToTheLexLeader() {
    Store store = new Store();
    IntVar[] v = new IntVar[6];
    for (int i = 0; i < v.length; i++) {
      v[i] = new IntVar(store, "v" + i, 0, 9);
    }
    SymmetryCanonicalizer columns = new SymmetryCanonicalizer();
    columns.chain(null, new IntVar[][] {{v[0], v[1]}, {v[2], v[3]}, {v[4], v[5]}});
    int[] values = {5, 1, 2, 7, 2, 3};
    assertTrue(columns.canonicalize(v, values));
    assertArrayEquals(new int[] {2, 3, 2, 7, 5, 1}, values);

    SymmetryCanonicalizer precede = new SymmetryCanonicalizer();
    precede.precedence(null, new IntVar[] {v[0], v[1], v[2], v[3]}, new int[] {1, 2, 3});
    values = new int[] {3, 3, 1, 2, 0, 0};
    assertTrue(precede.canonicalize(v, values));
    assertArrayEquals(new int[] {1, 1, 2, 3, 0, 0}, values);

    // v0 <=lex v1 for the symmetry that swaps v0 with v1 and v2 with v3
    SymmetryCanonicalizer lex = new SymmetryCanonicalizer();
    lex.lex(
        null,
        new IntVar[] {v[0]},
        new IntVar[] {v[1]},
        false,
        new IntVar[] {v[0], v[1], v[2], v[3]},
        new IntVar[] {v[1], v[0], v[3], v[2]});
    values = new int[] {4, 2, 8, 9, 0, 0};
    assertTrue(lex.canonicalize(v, values));
    assertArrayEquals(new int[] {2, 4, 9, 8, 0, 0}, values);
  }

  private static void checkOptimum(String out) {
    List<Integer> costs = new ArrayList<>();
    Matcher m = COST.matcher(out);
    while (m.find()) {
      costs.add(Integer.parseInt(m.group(1)));
    }
    assertTrue(!costs.isEmpty(), out);
    for (int k = 1; k < costs.size(); k++) {
      assertTrue(costs.get(k) < costs.get(k - 1), out);
    }
    assertEquals(3, costs.get(costs.size() - 1), out);
    assertTrue(out.contains("=========="), out);
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = Arrays.copyOf(options, options.length + 3);
    args[options.length] = "--free-config";
    args[options.length + 1] = "ls=0.5,ls-patience=0";
    args[options.length + 2] = fzn.toString();
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
