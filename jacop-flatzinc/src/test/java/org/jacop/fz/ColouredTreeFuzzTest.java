/*
 * ColouredTreeFuzzTest.java
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
import java.util.Random;
import java.util.StringJoiner;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random small FlatZinc models of minimum spanning trees with colour limits, written as MiniZinc
 * writes {@code weighted_spanning_tree} with {@code sum(e in colour c)(es[e]) <= cap[c]}
 * (jacop_wst, bool2int and int_lin_le), sometimes with degree limits as well, so that the front end
 * posts a {@link org.jacop.constraints.graph.ColouredSpanningTreeBound}. Each model is solved with
 * the detection on (no LCG, LCG with the explanation checker, LCG with free search) and compared
 * with the optimum with the detection off and no LCG.
 *
 * <pre>
 * mvn -Pmin -pl jacop-flatzinc test -Dtest=ColouredTreeFuzzTest -Dcolouredtreefuzz.trials=1500
 * </pre>
 */
class ColouredTreeFuzzTest {

  private static final int TRIALS = Integer.getInteger("colouredtreefuzz.trials", 60);
  private static final long SEED = Long.getLong("colouredtreefuzz.seed", 20261108L);

  @TempDir Path tmp;

  private int detected;

  private static String fzn(Random r) {
    int n = 3 + r.nextInt(5);
    int m = n - 1 + r.nextInt(2 * n);
    int colourNo = 1 + r.nextInt(3);
    int[] from = new int[m];
    int[] to = new int[m];
    int[] w = new int[m];
    int[] colour = new int[m];
    for (int e = 0; e < m; e++) {
      // the first n-1 edges make a random spanning tree, so most graphs are connected
      from[e] = e < n - 1 ? e + 2 : 1 + r.nextInt(n);
      to[e] = e < n - 1 ? 1 + r.nextInt(e + 1) : 1 + r.nextInt(n);
      w[e] = r.nextInt(10);
      colour[e] = r.nextInt(colourNo);
    }
    StringBuilder sb = new StringBuilder();
    sb.append("array [1..").append(m).append("] of int: from = ").append(list(from)).append(";\n");
    sb.append("array [1..").append(m).append("] of int: to = ").append(list(to)).append(";\n");
    sb.append("array [1..").append(m).append("] of int: w = ").append(list(w)).append(";\n");
    StringJoiner es = new StringJoiner(",", "[", "]");
    for (int e = 0; e < m; e++) {
      sb.append("var bool: es").append(e).append(" :: output_var;\n");
      sb.append("var 0..1: i").append(e).append(";\n");
      es.add("es" + e);
    }
    int total = Arrays.stream(w).sum();
    sb.append("array [1..").append(m).append("] of var bool: es :: output_array([1..");
    sb.append(m).append("]) = ").append(es).append(";\n");
    sb.append("var 0..").append(total).append(": K :: output_var;\n");
    List<String> constraints = new ArrayList<>();
    for (int e = 0; e < m; e++) {
      constraints.add("constraint bool2int(es" + e + ",i" + e + ");");
    }
    constraints.add("constraint jacop_wst(" + n + ",from,to,w,es,K);");
    for (int c = 0; c < colourNo; c++) {
      sum(constraints, colour, c, n, r);
    }
    if (r.nextInt(3) == 0) {
      // degree limits, whose edge sets overlap the colour classes
      for (int v = 1; v <= n; v++) {
        StringJoiner ones = new StringJoiner(",", "[", "]");
        StringJoiner vars = new StringJoiner(",", "[", "]");
        for (int e = 0; e < m; e++) {
          if (from[e] == v || to[e] == v) {
            ones.add("1");
            vars.add("i" + e);
          }
        }
        if (vars.length() > 2) {
          constraints.add("constraint int_lin_le(" + ones + "," + vars + ",2);");
        }
      }
    }
    for (String c : constraints) {
      sb.append(c).append('\n');
    }
    sb.append("solve minimize K;\n");
    return sb.toString();
  }

  // a limit that restricts a tree: below the size of the colour class and below n-1
  private static void sum(List<String> constraints, int[] colour, int c, int n, Random r) {
    StringJoiner ones = new StringJoiner(",", "[", "]");
    StringJoiner vars = new StringJoiner(",", "[", "]");
    int size = 0;
    for (int e = 0; e < colour.length; e++) {
      if (colour[e] == c) {
        ones.add("1");
        vars.add("i" + e);
        size++;
      }
    }
    if (size > 0) {
      int cap = r.nextInt(Math.min(size, n - 1));
      constraints.add("constraint int_lin_le(" + ones + "," + vars + "," + cap + ");");
    }
  }

  private static String list(int[] a) {
    StringJoiner j = new StringJoiner(",", "[", "]");
    for (int x : a) {
      j.add(Integer.toString(x));
    }
    return j.toString();
  }

  // the objective of the last solution, -1 for UNSAT, null when the run did not finish
  private Integer solve(String model, String... options) throws IOException {
    Path file = tmp.resolve("case.fzn");
    Files.writeString(file, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      List<String> args = new ArrayList<>(Arrays.asList(options));
      args.add(file.toString());
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    String out = buffer.toString(StandardCharsets.UTF_8);
    if (out.contains("% ColouredTreeDetector:")) {
      detected++;
    }
    if (out.contains("=====UNSATISFIABLE=====")) {
      return -1;
    }
    if (!out.contains("==========")) {
      return null;
    }
    Integer last = null;
    for (String line : out.split("\\R")) {
      if (line.startsWith("K = ")) {
        last = Integer.parseInt(line.substring(4, line.length() - 1).trim());
      }
    }
    return last;
  }

  @Test
  void colouredTreesHaveTheOptimumOfTheDecomposition() throws IOException {
    Random r = new Random(SEED);
    List<String> failures = new ArrayList<>();
    int satisfiable = 0;
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < 5; trial++) {
        String model = fzn(r);
        Integer expected;
        System.setProperty("org.jacop.fz.colouredTree", "false");
        try {
          expected = solve(model, "--lcg", "off");
        } finally {
          System.clearProperty("org.jacop.fz.colouredTree");
        }
        if (expected != null && expected >= 0) {
          satisfiable++;
        }
        System.setProperty("jacop.lcg.check", "true");
        try {
          String[][] runs = {{"--lcg", "off", "-debug"}, {"-debug"}, {"-f", "-debug"}};
          for (String[] options : runs) {
            Integer got = solve(model, options);
            if (got == null || !got.equals(expected)) {
              failures.add(
                  "trial "
                      + trial
                      + " "
                      + String.join(" ", options)
                      + ": expected "
                      + expected
                      + ", got "
                      + got
                      + "\n"
                      + model);
            }
          }
        } finally {
          System.clearProperty("jacop.lcg.check");
        }
      }
    } catch (IllegalStateException e) {
      failures.add(e.getMessage());
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
    // every model has a limit that restricts the tree, so the three runs with -debug report the
    // constraint for each satisfiable model, unless it is solved while it is read
    assertTrue(
        detected >= 2 * satisfiable,
        detected + " detections, " + satisfiable + " satisfiable models");
  }
}
