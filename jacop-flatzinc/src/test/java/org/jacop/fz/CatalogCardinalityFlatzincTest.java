/*
 * CatalogCardinalityFlatzincTest.java
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
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the FlatZinc side of the catalog cardinality constraints: the builtins jacop_same,
 * jacop_used_by, jacop_symmetric_gcc and jacop_cardinality_matrix of the MiniZinc library, and the
 * detection of 0/1 matrices with bounded row and column sums, which posts a redundant SymmetricGCC.
 * Solutions must not change.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class CatalogCardinalityFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.symmetricGcc";

  @TempDir Path tmp;

  // an n x m 0/1 matrix with sums over its rows and columns, as MiniZinc writes them
  private static String randomMatrix(Random random, boolean builtin) {
    int n = 2 + random.nextInt(2);
    int m = 2 + random.nextInt(2);
    StringBuilder fzn = new StringBuilder();
    StringBuilder all = new StringBuilder();
    for (int r = 0; r < n; r++) {
      for (int c = 0; c < m; c++) {
        fzn.append("var 0..1: b").append(r).append('_').append(c).append(";\n");
        all.append(all.length() == 0 ? "" : ",").append('b').append(r).append('_').append(c);
      }
    }
    fzn.append("array [1..")
        .append(n * m)
        .append("] of var int: b:: output_array([1..")
        .append(n * m)
        .append("]) = [")
        .append(all)
        .append("];\n");
    StringBuilder rows = new StringBuilder();
    StringBuilder cols = new StringBuilder();
    for (int r = 0; r < n; r++) {
      int lo = random.nextInt(2);
      fzn.append("var ").append(lo).append("..").append(lo + random.nextInt(2)).append(": r");
      fzn.append(r).append(";\n");
      rows.append(r == 0 ? "" : ",").append('r').append(r);
    }
    for (int c = 0; c < m; c++) {
      int lo = random.nextInt(2);
      fzn.append("var ").append(lo).append("..").append(lo + random.nextInt(2)).append(": k");
      fzn.append(c).append(";\n");
      cols.append(c == 0 ? "" : ",").append('k').append(c);
    }
    for (int r = 0; r < n; r++) {
      sum(fzn, random, r, -1, n, m);
    }
    for (int c = 0; c < m; c++) {
      sum(fzn, random, -1, c, n, m);
    }
    if (builtin) {
      fzn.append("constraint jacop_symmetric_gcc(b,")
          .append(m)
          .append(",[")
          .append(rows)
          .append("],[")
          .append(cols)
          .append("]);\n");
    }
    fzn.append("solve satisfy;\n");
    return fzn.toString();
  }

  // one line: = its counter, or bounds by a constant
  private static void sum(StringBuilder fzn, Random random, int row, int col, int n, int m) {
    int length = row >= 0 ? m : n;
    StringBuilder vars = new StringBuilder();
    for (int i = 0; i < length; i++) {
      int r = row >= 0 ? row : i;
      int c = row >= 0 ? i : col;
      vars.append(i == 0 ? "" : ",").append('b').append(r).append('_').append(c);
    }
    String counter = row >= 0 ? "r" + row : "k" + col;
    int[] ones = new int[length];
    Arrays.fill(ones, 1);
    String coefficients = Arrays.toString(ones).replace(" ", "");
    if (random.nextBoolean()) {
      fzn.append("constraint int_lin_eq(")
          .append(coefficients.replace("]", ",-1]"))
          .append(",[")
          .append(vars)
          .append(',')
          .append(counter)
          .append("],0);\n");
    } else {
      fzn.append("constraint int_lin_le(")
          .append(coefficients)
          .append(",[")
          .append(vars)
          .append("],")
          .append(random.nextInt(length + 1))
          .append(");\n");
      // the counter still has to be the sum
      fzn.append("constraint int_lin_eq(")
          .append(coefficients.replace("]", ",-1]"))
          .append(",[")
          .append(vars)
          .append(',')
          .append(counter)
          .append("],0);\n");
    }
  }

  @Test
  void detectedMatrixKeepsAllSolutions() throws IOException {
    Random random = new Random(11);
    int detected = 0;
    int satisfiable = 0;
    for (int trial = 0; trial < 150; trial++) {
      String model = randomMatrix(random, false);
      String on = run(model, true, "-a", "-debug");
      detected += on.contains("SymmetricGCC") ? 1 : 0;
      Set<String> expected = solutions(run(model, false, "-a"));
      satisfiable += expected.isEmpty() ? 0 : 1;
      assertEquals(expected, solutions(on), "trial " + trial + "\n" + model);
    }
    // a model found infeasible while it is read never reaches the detection
    assertTrue(
        detected >= satisfiable && satisfiable >= 50,
        "detected " + detected + " satisfiable " + satisfiable);
  }

  @Test
  void builtinKeepsAllSolutions() throws IOException {
    Random random = new Random(12);
    for (int trial = 0; trial < 100; trial++) {
      String with = randomMatrix(random, true);
      String without = with.replaceAll("constraint jacop_symmetric_gcc[^\n]*\n", "");
      assertEquals(
          solutions(run(without, false, "-a")),
          solutions(run(with, false, "-a")),
          "trial " + trial + "\n" + with);
    }
  }

  @Test
  void sameAndUsedBy() throws IOException {
    String header =
        """
        var 1..3: x0;
        var 1..3: x1;
        var 2..3: x2;
        var 1..1: y0;
        var 1..3: y1;
        var 1..3: y2;
        array [1..6] of var int: v:: output_array([1..6]) = [x0,x1,x2,y0,y1,y2];
        """;
    String same = header + "constraint jacop_same([x0,x1,x2],[y0,y1,y2]);\nsolve satisfy;\n";
    // x2 is not 1, so x0 or x1 is the 1 of y0: 2 ways; the other two values of x are those of y1,
    // y2 in either order
    Set<String> solutions = solutions(run(same, false, "-a"));
    for (String s : solutions) {
      int[] v = values(s);
      int[] a = {v[0], v[1], v[2]};
      int[] b = {v[3], v[4], v[5]};
      Arrays.sort(a);
      Arrays.sort(b);
      assertTrue(Arrays.equals(a, b), s);
    }
    assertEquals(brute(false), solutions.size());
    String usedBy = header + "constraint jacop_used_by([x0,x1,x2],[y0,y1]);\nsolve satisfy;\n";
    assertEquals(brute(true), solutions(run(usedBy, false, "-a")).size());
  }

  // the number of solutions of the header's domains, by enumeration
  private static int brute(boolean usedBy) {
    int count = 0;
    for (int x0 = 1; x0 <= 3; x0++) {
      for (int x1 = 1; x1 <= 3; x1++) {
        for (int x2 = 2; x2 <= 3; x2++) {
          for (int y1 = 1; y1 <= 3; y1++) {
            for (int y2 = 1; y2 <= 3; y2++) {
              int[] c = new int[4];
              c[x0]++;
              c[x1]++;
              c[x2]++;
              c[1]--;
              c[y1]--;
              if (!usedBy) {
                c[y2]--;
              }
              boolean ok = Arrays.stream(c).allMatch(k -> usedBy ? k >= 0 : k == 0);
              count += ok ? 1 : 0;
            }
          }
        }
      }
    }
    return count;
  }

  @Test
  void cardinalityMatrix() throws IOException {
    // a 2 x 2 matrix over 1..2 where value 1 occurs once in every row and column
    String fzn =
        """
        var 1..2: a;
        var 1..2: b;
        var 1..2: c;
        var 1..2: d;
        array [1..4] of var int: x:: output_array([1..4]) = [a,b,c,d];
        constraint jacop_cardinality_matrix(x,2,[1],[1,1],[1,1]);
        solve satisfy;
        """;
    Set<String> solutions = solutions(run(fzn, false, "-a"));
    assertEquals(2, solutions.size(), solutions.toString());
  }

  private static int[] values(String solution) {
    String list = solution.substring(solution.indexOf('[') + 1, solution.indexOf(']'));
    return Arrays.stream(list.split(",")).mapToInt(s -> Integer.parseInt(s.strip())).toArray();
  }

  private String run(String model, boolean detection, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, Boolean.toString(detection));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    Arrays.stream(s.strip().split("\\R"))
                        .filter(l -> !l.isBlank() && !l.startsWith("%"))
                        .toList()))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
