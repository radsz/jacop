/*
 * ZeroOneParityTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.concurrent.TimeUnit;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * Equations over 0/1 variables in the XOR system ({@code XorSystemDetector}): the even colouring of
 * K5 with a slack per vertex (each vertex has 3 of its 4 edges plus its slack, as in the
 * evencolouring models of the PB competition), whose rows sum to an odd parity of the slacks, also
 * written as pairs of opposite inequalities; exactly-one rows stay out; and random models of 0/1
 * equations, some as inequality pairs, have the optimum of enumeration with and without the rows.
 */
@Timeout(value = 120, unit = TimeUnit.SECONDS)
class ZeroOneParityTest {

  private static final int TRIALS = Integer.getInteger("zeroOneParity.trials", 60);

  @TempDir Path tmp;

  // the edges of K5 at each vertex: e_ij for i < j
  private static String evenColouring(boolean asPairs) {
    StringBuilder sb = new StringBuilder();
    List<String> edges = new ArrayList<>();
    for (int i = 0; i < 5; i++) {
      for (int j = i + 1; j < 5; j++) {
        edges.add("e" + i + j);
        sb.append("var 0..1: e").append(i).append(j).append(";\n");
      }
    }
    for (int v = 0; v < 5; v++) {
      sb.append("var 0..1: s").append(v).append(";\n");
    }
    sb.append("var 0..15: obj :: output_var;\n");
    for (int v = 0; v < 5; v++) {
      List<String> row = new ArrayList<>();
      for (String e : edges) {
        if (e.indexOf((char) ('0' + v)) > 0) {
          row.add(e);
        }
      }
      row.add("s" + v);
      String vars = String.join(", ", row);
      if (asPairs) {
        sb.append("constraint int_lin_le([1,1,1,1,1], [").append(vars).append("], 3);\n");
        sb.append("constraint int_lin_le([-1,-1,-1,-1,-1], [").append(vars).append("], -3);\n");
      } else {
        sb.append("constraint int_lin_eq([1,1,1,1,1], [").append(vars).append("], 3);\n");
      }
    }
    sb.append("constraint int_lin_eq([1,2,3,4,5,-1], [s0, s1, s2, s3, s4, obj], 0);\n");
    sb.append("solve minimize obj;\n");
    return sb.toString();
  }

  @Test
  void evenColouringRowsFormOneSystem() throws IOException {
    String out = run(evenColouring(false), "-debug");
    assertTrue(out.contains("% XorSystem: 1 systems, 5 rows"), out);
    // the slacks have odd parity: one of them is 1, the first the cheapest
    assertEquals(Integer.valueOf(1), solve(evenColouring(false)));
  }

  // a xor b xor c = 1 written as the four clauses that exclude its even points, and r = not a
  // (as a soft literal of a MaxSAT model is the negation of an output): a tree of two rows, which
  // unit propagation already solves, so no system is posted (security-witness of the MaxSAT
  // Evaluation 2021 had 63,636 such pairs, each a system visited at every backtrack)
  @Test
  void negationNextToClauseXorPostsNoSystem() throws IOException {
    String model =
        "var bool: a;\nvar bool: b;\nvar bool: c;\nvar bool: r;\n"
            + "var 0..1: v :: output_var;\n"
            + "constraint bool_clause([a, b, c], []);\n"
            + "constraint bool_clause([a], [b, c]);\n"
            + "constraint bool_clause([b], [a, c]);\n"
            + "constraint bool_clause([c], [a, b]);\n"
            + "constraint bool_not(a, r);\n"
            + "constraint bool2int(r, v);\n"
            + "solve minimize v;\n";
    String out = run(model, "-debug", "--search-statistics");
    assertTrue(out.contains("%%%mzn-stat: xorAcyclicSystems=1"), out);
    assertTrue(!out.contains("% XorSystem: "), out);
    assertTrue(out.contains("v = 0;"), out);
  }

  @Test
  void opposedInequalitiesAreEquations() throws IOException {
    String out = run(evenColouring(true), "-debug");
    assertTrue(out.contains("% XorSystem: 1 systems, 5 rows"), out);
    assertEquals(Integer.valueOf(1), solve(evenColouring(true)));
  }

  @Test
  void exactlyOneRowsStayOut() throws IOException {
    String model =
        "var 0..1: a;\nvar 0..1: b;\nvar 0..1: c;\nvar 0..1: d;\n"
            + "constraint int_lin_eq([1,1,1], [a, b, c], 1);\n"
            + "constraint int_lin_eq([1,1,1], [b, c, d], 2);\n"
            + "constraint int_lin_eq([1,1,1], [a, c, d], 1);\n"
            + "solve satisfy;\n";
    assertTrue(!run(model, "-debug").contains("% XorSystem:"));
  }

  // rows of 0/1 equations sum(x_row) = k, some as two inequalities; minimise a weighted sum
  private record Model(int n, int[][] rows, int[] rhs, boolean[] pairs, int[] weights) {}

  private static Model randomModel(Random r) {
    int n = 5 + r.nextInt(8);
    int m = 2 + r.nextInt(n);
    int[][] rows = new int[m][];
    int[] rhs = new int[m];
    boolean[] pairs = new boolean[m];
    for (int i = 0; i < m; i++) {
      int k = 3 + r.nextInt(Math.min(n - 2, 4));
      int[] perm = r.ints(0, n).distinct().limit(k).toArray();
      rows[i] = perm;
      rhs[i] = 1 + r.nextInt(k - 1);
      pairs[i] = r.nextBoolean();
    }
    int[] w = new int[n];
    for (int j = 0; j < n; j++) {
      w[j] = 1 + r.nextInt(4);
    }
    return new Model(n, rows, rhs, pairs, w);
  }

  private static int bruteForce(Model m) {
    int best = -1;
    for (int s = 0; s < 1 << m.n; s++) {
      boolean ok = true;
      for (int i = 0; i < m.rows.length && ok; i++) {
        int sum = 0;
        for (int c : m.rows[i]) {
          sum += (s >> c) & 1;
        }
        ok = sum == m.rhs[i];
      }
      if (ok) {
        int cost = 0;
        for (int j = 0; j < m.n; j++) {
          cost += ((s >> j) & 1) * m.weights[j];
        }
        if (best < 0 || cost < best) {
          best = cost;
        }
      }
    }
    return best;
  }

  private static String fzn(Model m) {
    StringBuilder sb = new StringBuilder();
    int total = 0;
    for (int j = 0; j < m.n; j++) {
      sb.append("var 0..1: x").append(j).append(";\n");
      total += m.weights[j];
    }
    sb.append("var 0..").append(total).append(": obj :: output_var;\n");
    for (int i = 0; i < m.rows.length; i++) {
      String vars =
          String.join(", ", Arrays.stream(m.rows[i]).mapToObj(c -> "x" + c).toArray(String[]::new));
      String ones = String.join(",", java.util.Collections.nCopies(m.rows[i].length, "1"));
      String minus = String.join(",", java.util.Collections.nCopies(m.rows[i].length, "-1"));
      if (m.pairs[i]) {
        sb.append("constraint int_lin_le([" + ones + "], [" + vars + "], " + m.rhs[i] + ");\n");
        sb.append("constraint int_lin_le([" + minus + "], [" + vars + "], " + -m.rhs[i] + ");\n");
      } else {
        sb.append("constraint int_lin_eq([" + ones + "], [" + vars + "], " + m.rhs[i] + ");\n");
      }
    }
    StringBuilder w = new StringBuilder();
    StringBuilder x = new StringBuilder();
    for (int j = 0; j < m.n; j++) {
      w.append(m.weights[j]).append(",");
      x.append("x").append(j).append(", ");
    }
    sb.append("constraint int_lin_eq([" + w + "-1], [" + x + "obj], 0);\n");
    sb.append("solve minimize obj;\n");
    return sb.toString();
  }

  @Test
  void randomZeroOneEquationsHaveTheOptimumOfEnumeration() throws IOException {
    Random r = new Random(20261115L);
    List<String> failures = new ArrayList<>();
    System.setProperty("jacop.lcg.check", "true");
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < 3; trial++) {
        Model m = randomModel(r);
        int expected = bruteForce(m);
        String model = fzn(m);
        for (String[] options : new String[][] {{"--lcg"}, {"--lcg", "-f"}, {"--lcg", "off"}}) {
          Integer got = solve(model, options);
          if (got == null || got != expected) {
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
      }
    } finally {
      System.clearProperty("jacop.lcg.check");
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
  }

  // the objective of the last solution, -1 for UNSAT, null when the run did not finish
  private Integer solve(String model, String... options) throws IOException {
    String out = run(model, options);
    if (out.contains("=====UNSATISFIABLE=====")) {
      return -1;
    }
    if (!out.contains("==========")) {
      return null;
    }
    Integer last = null;
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = Integer.parseInt(line.substring(6, line.length() - 1).trim());
      }
    }
    return last;
  }

  private String run(String model, String... options) throws IOException {
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
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
