/*
 * XcspTableFlatzincTest.java
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
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks jacop_short_table_int (a table whose value star matches any value) and
 * jacop_negative_table_int (forbidden tuples), which JaCoP's mznlib posts for the short and
 * negative tables of the XCSP3 bench, against brute force on random tables over variables with
 * holes, with repeated variables in the scope and with and without lazy clause generation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class XcspTableFlatzincTest {

  private static final int STAR = -9;

  @TempDir Path tmp;

  @Test
  void rowOfStarsAllowsEverything() throws IOException {
    int[][] rows = {{1, STAR}, {STAR, STAR}};
    String fzn = model(new int[] {0, 1}, 2, rows, true);
    assertEquals(16, solveAll(fzn).size());
  }

  @Test
  void repeatedVariableNeedsEqualValues() throws IOException {
    // x0 occurs twice: the row (1, 3) cannot match, the row (3, *) gives x0 = 3
    int[][] rows = {{1, 3}, {3, STAR}};
    String fzn = model(new int[] {0, 0}, 1, rows, true);
    assertEquals(Set.of("x = array1d(1..1, [3]);"), solveAll(fzn));
  }

  @Test
  void randomShortTablesMatchBruteForce() throws IOException {
    randomTables(true, 20261101);
  }

  @Test
  void randomNegativeTablesMatchBruteForce() throws IOException {
    randomTables(false, 20261102);
  }

  private void randomTables(boolean positive, long seed) throws IOException {
    Random random = new Random(seed);
    for (int run = 0; run < 30; run++) {
      int vars = 1 + random.nextInt(3);
      int arity = 1 + random.nextInt(4);
      int[] scope = new int[arity];
      for (int i = 0; i < arity; i++) {
        scope[i] = random.nextInt(vars);
      }
      int[][] rows = new int[random.nextInt(6)][arity];
      for (int[] row : rows) {
        for (int i = 0; i < arity; i++) {
          row[i] = positive && random.nextInt(3) == 0 ? STAR : random.nextInt(5);
        }
      }
      Set<String> expected = new TreeSet<>();
      enumerate(new int[vars], 0, scope, rows, positive, expected);
      String fzn = model(scope, vars, rows, positive);
      String message = "run " + run + "\n" + fzn;
      assertEquals(expected, solveAll(fzn), message);
      assertEquals(expected, solveAll(fzn, "--lcg", "off"), message);
    }
  }

  private static boolean allowed(int[] x, int[] scope, int[] row) {
    for (int i = 0; i < scope.length; i++) {
      if (row[i] != STAR && x[scope[i]] != row[i]) {
        return false;
      }
    }
    return true;
  }

  // the variables range over {0, 1, 3, 4}: 2 is a hole
  private static void enumerate(
      int[] x, int i, int[] scope, int[][] rows, boolean positive, Set<String> out) {
    if (i == x.length) {
      boolean match = Arrays.stream(rows).anyMatch(row -> allowed(x, scope, row));
      if (match == positive) {
        out.add(
            Arrays.stream(x)
                .mapToObj(String::valueOf)
                .collect(Collectors.joining(", ", "x = array1d(1.." + x.length + ", [", "]);")));
      }
      return;
    }
    for (int v : new int[] {0, 1, 3, 4}) {
      x[i] = v;
      enumerate(x, i + 1, scope, rows, positive, out);
    }
  }

  private static String model(int[] scope, int vars, int[][] rows, boolean positive) {
    StringBuilder fzn = new StringBuilder();
    fzn.append(
        positive
            ? "predicate jacop_short_table_int(array [int] of var int: x,array [int] of int: t,"
                + "int: star);\n"
            : "predicate jacop_negative_table_int(array [int] of var int: x,"
                + "array [int] of int: t);\n");
    for (int i = 0; i < vars; i++) {
      fzn.append("var {0,1,3,4}: x").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(vars)
        .append("] of var int: x:: output_array([1..")
        .append(vars)
        .append("]) = ")
        .append(
            IntStream.range(0, vars)
                .mapToObj(i -> "x" + i)
                .collect(Collectors.joining(",", "[", "]")))
        .append(";\n");
    String cells =
        Arrays.stream(rows)
            .flatMapToInt(Arrays::stream)
            .mapToObj(String::valueOf)
            .collect(Collectors.joining(",", "[", "]"));
    String xs =
        Arrays.stream(scope).mapToObj(i -> "x" + i).collect(Collectors.joining(",", "[", "]"));
    fzn.append("constraint jacop_")
        .append(positive ? "short" : "negative")
        .append("_table_int(")
        .append(xs)
        .append(',')
        .append(cells)
        .append(positive ? "," + STAR : "")
        .append(");\nsolve satisfy;\n");
    return fzn.toString();
  }

  private String solve(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private Set<String> solveAll(String model, String... options) throws IOException {
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = "-a";
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(solve(model, args).split("----------"))
        .map(String::strip)
        .filter(s -> s.startsWith("x = "))
        .forEach(solutions::add);
    return solutions;
  }
}
