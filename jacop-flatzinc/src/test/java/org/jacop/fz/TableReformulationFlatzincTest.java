/*
 * TableReformulationFlatzincTest.java
 * <p>
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tables with free columns, functional dependencies, Cartesian tables, constant or star-only
 * columns of short tables, and tables over the same variables are posted as smaller parts or merged
 * ({@code TableReformulation}, {@code TableScopeMerger}): every solution and every optimum must
 * stay, with and without LCG.
 */
class TableReformulationFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.tableReformulation";

  @TempDir Path tmp;

  /**
   * A random model over a few variables with holes: tables built as joins of a random core table
   * with dependent columns (a function of a core column, sometimes the identity), free columns (a
   * product with a set of values) and constant columns, the columns shuffled, sometimes one row
   * dropped so the structure breaks; some tables are posted twice over the same variables in
   * another order, and some are short tables.
   */
  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int nv = 4 + random.nextInt(4);
    List<String> names = new ArrayList<>();
    for (int i = 0; i < nv; i++) {
      String x = "x" + i;
      names.add(x);
      int hole = 1 + random.nextInt(3);
      fzn.append("var {")
          .append(
              IntStream.rangeClosed(0, 4)
                  .filter(v -> v != hole)
                  .mapToObj(String::valueOf)
                  .collect(Collectors.joining(",")))
          .append("}: ")
          .append(x)
          .append(";\n");
    }
    fzn.append("array [1..")
        .append(nv)
        .append("] of var int: x:: output_array([1..")
        .append(nv)
        .append("]) = ")
        .append(names.stream().collect(Collectors.joining(",", "[", "]")))
        .append(";\n");
    if (optimise) {
      fzn.append("var 0..1000: obj:: output_var;\n");
    }
    List<String> constraints = new ArrayList<>();
    int tables = 1 + random.nextInt(3);
    for (int t = 0; t < tables; t++) {
      int arity = 2 + random.nextInt(Math.min(4, nv - 1));
      List<Integer> scope = new ArrayList<>(IntStream.range(0, nv).boxed().toList());
      java.util.Collections.shuffle(scope, random);
      scope = scope.subList(0, arity);
      int[][] rows = structuredTable(random, arity);
      if (random.nextInt(4) == 0) {
        constraints.add(shortTable(random, scope, rows));
        continue;
      }
      constraints.add(table(scope, rows));
      if (random.nextInt(3) == 0) {
        // the same variables in another order, with a random subset of the rows
        Integer[] perm = IntStream.range(0, arity).boxed().toArray(Integer[]::new);
        java.util.Collections.shuffle(Arrays.asList(perm), random);
        List<Integer> scope2 = new ArrayList<>();
        for (int c = 0; c < arity; c++) {
          scope2.add(scope.get(perm[c]));
        }
        List<int[]> rows2 = new ArrayList<>();
        for (int[] row : rows) {
          if (random.nextInt(4) != 0) {
            int[] r = new int[arity];
            for (int c = 0; c < arity; c++) {
              r[c] = row[perm[c]];
            }
            rows2.add(r);
          }
        }
        if (rows2.isEmpty()) {
          rows2.add(rows[0]);
        }
        constraints.add(table(scope2, rows2.toArray(new int[0][])));
      }
    }
    if (random.nextBoolean()) {
      constraints.add("constraint int_lin_le([1,1],[x0,x1]," + (2 + random.nextInt(5)) + ")");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      int[] w = IntStream.range(0, nv).map(i -> 1 + random.nextInt(5)).toArray();
      int[] a = Arrays.copyOf(w, nv + 1);
      a[nv] = -1;
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(a).replace(" ", ""))
          .append(",")
          .append(
              IntStream.rangeClosed(0, nv)
                  .mapToObj(i -> i < nv ? "x" + i : "obj")
                  .collect(Collectors.joining(",", "[", "]")))
          .append(",0);\n");
      fzn.append("solve :: int_search(x,input_order,indomain_min,complete) maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  // a core table joined with dependent, free and constant columns, the columns shuffled
  private static int[][] structuredTable(Random random, int arity) {
    int core = 1 + random.nextInt(Math.min(2, arity));
    List<int[]> rows = new ArrayList<>();
    int coreRows = 1 + random.nextInt(8);
    for (int r = 0; r < coreRows; r++) {
      int[] row = new int[core];
      for (int c = 0; c < core; c++) {
        row[c] = random.nextInt(5);
      }
      rows.add(row);
    }
    for (int c = core; c < arity; c++) {
      int kind = random.nextInt(4);
      List<int[]> next = new ArrayList<>();
      if (kind == 0) {
        // free: a product with a set of values
        int[] set = IntStream.range(0, 5).filter(v -> random.nextInt(2) == 0).toArray();
        if (set.length == 0) {
          set = new int[] {random.nextInt(5)};
        }
        for (int[] row : rows) {
          for (int v : set) {
            int[] r = Arrays.copyOf(row, c + 1);
            r[c] = v;
            next.add(r);
          }
        }
      } else {
        // a function of an earlier column (the identity sometimes), or a constant
        int from = random.nextInt(c);
        int[] f = IntStream.range(0, 5).map(v -> random.nextInt(5)).toArray();
        boolean identity = kind == 1;
        int constant = kind == 2 ? random.nextInt(5) : -1;
        for (int[] row : rows) {
          int[] r = Arrays.copyOf(row, c + 1);
          r[c] = constant >= 0 ? constant : identity ? row[from] : f[row[from]];
          next.add(r);
        }
      }
      rows = next;
    }
    if (rows.size() > 1 && random.nextInt(4) == 0) {
      rows.remove(random.nextInt(rows.size()));
    }
    Integer[] perm = IntStream.range(0, arity).boxed().toArray(Integer[]::new);
    java.util.Collections.shuffle(Arrays.asList(perm), random);
    int[][] out = new int[rows.size()][arity];
    for (int r = 0; r < out.length; r++) {
      for (int c = 0; c < arity; c++) {
        out[r][c] = rows.get(r)[perm[c]];
      }
    }
    return out;
  }

  private static String table(List<Integer> scope, int[][] rows) {
    return "constraint jacop_table_int("
        + scope.stream().map(i -> "x" + i).collect(Collectors.joining(",", "[", "]"))
        + ","
        + Arrays.stream(rows)
            .flatMapToInt(Arrays::stream)
            .mapToObj(String::valueOf)
            .collect(Collectors.joining(",", "[", "]"))
        + ")";
  }

  // a short table: some cells are stars, and a column is sometimes all stars
  private static String shortTable(Random random, List<Integer> scope, int[][] rows) {
    int star = 99;
    int starColumn = random.nextInt(2) == 0 ? random.nextInt(scope.size()) : -1;
    return "constraint jacop_short_table_int("
        + scope.stream().map(i -> "x" + i).collect(Collectors.joining(",", "[", "]"))
        + ","
        + Arrays.stream(rows)
            .flatMapToInt(
                row ->
                    IntStream.range(0, row.length)
                        .map(
                            c ->
                                c == starColumn || random.nextInt(6) == 0 && c != 0
                                    ? star
                                    : row[c]))
            .mapToObj(String::valueOf)
            .collect(Collectors.joining(",", "[", "]"))
        + ","
        + star
        + ")";
  }

  @Test
  void reformulatedTablesKeepAllSolutions() throws IOException {
    Random random = new Random(21);
    int reformulated = 0;
    int merged = 0;
    int trials = Integer.getInteger("tableReformulation.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String out = run(model, true, "-a", "-debug");
      reformulated += out.contains("table reformulation") ? 1 : 0;
      merged += out.contains("table scope merger") ? 1 : 0;
      assertEquals(
          solutions(run(model, false, "-a")), solutions(out), "trial " + trial + "\n" + model);
    }
    assertTrue(reformulated > trials / 3, "reformulated " + reformulated);
    assertTrue(merged > trials / 20, "merged " + merged);
  }

  @Test
  void reformulatedTablesKeepOptimaUnderLcg() throws IOException {
    Random random = new Random(22);
    int trials = Integer.getInteger("tableReformulation.trials", 300) * 2 / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"));
      assertEquals(
          expected, optimum(run(model, true, "--lcg", "on")), "trial " + trial + "\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on", "-f")),
          "trial " + trial + " -f\n" + model);
    }
  }

  private String run(String model, boolean reformulation, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (!reformulation) {
      System.setProperty(PROPERTY, "false");
    }
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

  // the value of obj in the last solution, or the status when there is none
  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out);
    return last;
  }
}
