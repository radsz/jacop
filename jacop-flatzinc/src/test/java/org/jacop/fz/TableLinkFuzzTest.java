/*
 * TableLinkFuzzTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random small FlatZinc models of positive tables over overlapping scopes, compared with
 * enumeration. Tables that share two or more variables are linked by {@link
 * org.jacop.fz.constraints.TableLinkDetector} for pairwise consistency. Each model is solved for
 * all its solutions and for the least weighted sum, with the links on and off, with and without
 * free search.
 *
 * <pre>
 * mvn -Pmin -pl jacop-flatzinc test -Dtest=TableLinkFuzzTest -Dtablelinks.trials=3000
 * </pre>
 */
class TableLinkFuzzTest {

  private static final int TRIALS = Integer.getInteger("tablelinks.trials", 150);
  private static final long SEED = Long.getLong("tablelinks.seed", 20261108L);

  private static final String LINKS = "org.jacop.fz.tableLinks";

  @TempDir Path tmp;

  private record Model(int n, int d, int[] weights, int[][] scopes, int[][][] tuples) {}

  private static Model randomModel(Random r) {
    int n = 3 + r.nextInt(5);
    int d = 2 + r.nextInt(3);
    int[] weights = new int[n];
    for (int i = 0; i < n; i++) {
      weights[i] = 1 + r.nextInt(5);
    }
    int m = 2 + r.nextInt(4);
    int[][] scopes = new int[m][];
    int[][][] tuples = new int[m][][];
    for (int c = 0; c < m; c++) {
      int k = 2 + r.nextInt(Math.min(3, n - 1));
      // a later table often reuses variables of an earlier one, so scopes overlap
      List<Integer> pool = new ArrayList<>();
      if (c > 0 && r.nextInt(4) > 0) {
        for (int v : scopes[r.nextInt(c)]) {
          pool.add(v);
        }
      }
      List<Integer> scope = new ArrayList<>();
      while (scope.size() < k) {
        int v =
            !pool.isEmpty() && r.nextBoolean() ? pool.remove(r.nextInt(pool.size())) : r.nextInt(n);
        if (!scope.contains(v)) {
          scope.add(v);
        }
      }
      scopes[c] = scope.stream().mapToInt(Integer::intValue).toArray();
      int all = (int) Math.pow(d, k);
      double density = 0.2 + 0.6 * r.nextDouble();
      List<int[]> rows = new ArrayList<>();
      for (int t = 0; t < all; t++) {
        if (r.nextDouble() < density) {
          int[] row = new int[k];
          int x = t;
          for (int j = 0; j < k; j++) {
            row[j] = x % d;
            x /= d;
          }
          rows.add(row);
        }
      }
      if (rows.isEmpty()) {
        rows.add(new int[k]);
      }
      tuples[c] = rows.toArray(new int[0][]);
    }
    return new Model(n, d, weights, scopes, tuples);
  }

  // the least weighted sum (-1 when there is no solution) and the number of solutions
  private static int[] bruteForce(Model m) {
    int best = -1;
    int count = 0;
    int total = (int) Math.pow(m.d, m.n);
    int[] a = new int[m.n];
    for (int s = 0; s < total; s++) {
      int x = s;
      for (int i = 0; i < m.n; i++) {
        a[i] = x % m.d;
        x /= m.d;
      }
      boolean ok = true;
      for (int c = 0; c < m.scopes.length && ok; c++) {
        boolean found = false;
        for (int[] row : m.tuples[c]) {
          boolean match = true;
          for (int j = 0; j < row.length && match; j++) {
            match = a[m.scopes[c][j]] == row[j];
          }
          if (match) {
            found = true;
            break;
          }
        }
        ok = found;
      }
      if (ok) {
        count++;
        int cost = 0;
        for (int i = 0; i < m.n; i++) {
          cost += m.weights[i] * a[i];
        }
        if (best < 0 || cost < best) {
          best = cost;
        }
      }
    }
    return new int[] {best, count};
  }

  private static String fzn(Model m, boolean optimise) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < m.n; i++) {
      sb.append("var 0..").append(m.d - 1).append(": x").append(i).append(" :: output_var;\n");
    }
    int max = 0;
    for (int w : m.weights) {
      max += w * (m.d - 1);
    }
    sb.append("var 0..").append(max).append(": obj :: output_var;\n");
    for (int c = 0; c < m.scopes.length; c++) {
      StringBuilder vars = new StringBuilder();
      for (int j = 0; j < m.scopes[c].length; j++) {
        vars.append(j > 0 ? ", " : "").append("x").append(m.scopes[c][j]);
      }
      StringBuilder rows = new StringBuilder();
      for (int[] row : m.tuples[c]) {
        for (int v : row) {
          rows.append(rows.length() > 0 ? ", " : "").append(v);
        }
      }
      sb.append("constraint jacop_table_int([")
          .append(vars)
          .append("], [")
          .append(rows)
          .append("]);\n");
    }
    StringBuilder ws = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < m.n; i++) {
      ws.append(m.weights[i]).append(", ");
      xs.append("x").append(i).append(", ");
    }
    sb.append("constraint int_lin_eq([")
        .append(ws)
        .append("-1], [")
        .append(xs)
        .append("obj], 0);\n");
    sb.append(optimise ? "solve minimize obj;\n" : "solve satisfy;\n");
    return sb.toString();
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

  // the number of solutions printed by a run for all solutions, or -1 when it did not finish
  private int count(String model, String... options) throws IOException {
    String out = run(model, options);
    if (out.contains("=====UNSATISFIABLE=====")) {
      return 0;
    }
    if (!out.contains("==========")) {
      return -1;
    }
    return out.split("----------", -1).length - 1;
  }

  private String withLinks(boolean on, Run run) throws IOException {
    System.setProperty(LINKS, Boolean.toString(on));
    try {
      return run.get();
    } finally {
      System.clearProperty(LINKS);
    }
  }

  private interface Run {
    String get() throws IOException;
  }

  @Test
  void sharedPairIsPairwiseConsistent() throws IOException {
    // (a, b, c) allows (0, 0, 1) and (1, 1, 0); (a, b, d) allows (0, 1, 0) and (1, 1, 1); only
    // a = 1, b = 1 is common, so pairwise consistency fixes a, b and c before any search
    String model =
        "var 0..1: a :: output_var;\nvar 0..1: b :: output_var;\nvar 0..1: c :: output_var;\n"
            + "var 0..1: d :: output_var;\n"
            + "constraint jacop_table_int([a, b, c], [0,0,1, 1,1,0]);\n"
            + "constraint jacop_table_int([a, b, d], [0,1,0, 1,1,1]);\n"
            + "solve satisfy;\n";
    String out = withLinks(true, () -> run(model, "-debug", "-s", "--lcg", "off"));
    assertTrue(out.contains("% table links: 1 links, 2 tables linked, 2 rows"), out);
    assertTrue(out.contains("a = 1;") && out.contains("b = 1;") && out.contains("c = 0;"), out);
    assertTrue(out.contains("%%%mzn-stat: failures=0"), out);
    // under lazy clause generation the tables are not linked
    out = withLinks(true, () -> run(model, "-debug", "-s", "--lcg"));
    assertTrue(!out.contains("% table links"), out);
  }

  @Test
  void linkedTablesHaveTheSolutionsOfEnumeration() throws IOException {
    Random r = new Random(SEED);
    List<String> failures = new ArrayList<>();
    for (int trial = 0; trial < TRIALS && failures.size() < 5; trial++) {
      Model m = randomModel(r);
      int[] expected = bruteForce(m);
      String all = fzn(m, false);
      String opt = fzn(m, true);
      for (boolean on : new boolean[] {true, false}) {
        for (String[] options : new String[][] {{"--lcg", "off"}, {"--lcg", "off", "-f"}}) {
          String what = trial + (on ? " links " : " no links ") + Arrays.toString(options);
          String[] counting = Arrays.copyOf(options, options.length + 1);
          counting[options.length] = "-a";
          int got = Integer.parseInt(withLinks(on, () -> Integer.toString(count(all, counting))));
          if (got != expected[1]) {
            failures.add(
                "trial " + what + ": " + expected[1] + " solutions, got " + got + "\n" + all);
          }
          String best = withLinks(on, () -> String.valueOf(solve(opt, options)));
          if (!best.equals(Integer.toString(expected[0]))) {
            failures.add("trial " + what + ": optimum " + expected[0] + ", got " + best);
          }
        }
      }
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
  }
}
