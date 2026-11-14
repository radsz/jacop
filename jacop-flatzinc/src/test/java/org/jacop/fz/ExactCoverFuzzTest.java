/*
 * ExactCoverFuzzTest.java
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
 * Random exact cover models written as equalities {@code y_1 + ... + y_k = 1} over 0/1 variables,
 * with a weighted objective and a few side clauses, solved with and without the {@link
 * org.jacop.constraints.ExactCover} the front end adds, in and out of LCG with the explanation
 * checker on, against enumeration.
 */
class ExactCoverFuzzTest {

  private static final int TRIALS = Integer.getInteger("exactcoverfuzz.trials", 150);
  private static final long SEED = Long.getLong("exactcoverfuzz.seed", 20261108L);

  @TempDir Path tmp;

  // option o covers the elements of mask[o] and costs weight[o]; clauses as pairs of options
  private static final class Model {
    final int n;
    final int[] mask;
    final int[] weight;
    final int[][] clauses;

    Model(int n, int[] mask, int[] weight, int[][] clauses) {
      this.n = n;
      this.mask = mask;
      this.weight = weight;
      this.clauses = clauses;
    }
  }

  private static Model randomModel(Random r) {
    int n = 4 + r.nextInt(6);
    int m = n + r.nextInt(12);
    int[] mask = new int[m];
    int[] weight = new int[m];
    for (int o = 0; o < m; o++) {
      // small options, so that covers exist; every element gets at least one singleton sometimes
      int bits = 0;
      int size = 1 + r.nextInt(3);
      for (int k = 0; k < size; k++) {
        bits |= 1 << r.nextInt(n);
      }
      mask[o] = bits;
      weight[o] = r.nextInt(5);
    }
    int[][] clauses = new int[r.nextInt(3)][];
    for (int i = 0; i < clauses.length; i++) {
      clauses[i] = new int[] {r.nextInt(m), r.nextInt(m)};
    }
    return new Model(n, mask, weight, clauses);
  }

  // the least cost of an exact cover, or -1 when there is none
  private static int bruteForce(Model m) {
    int[] best = {-1};
    search(m, 0, 0, 0, 0, best);
    return best[0];
  }

  // options from o on, with the elements covered and the options chosen so far
  private static void search(Model m, int o, int covered, long chosen, int cost, int[] best) {
    if (o == m.mask.length) {
      if (covered != (1 << m.n) - 1) {
        return;
      }
      for (int[] cl : m.clauses) {
        if ((chosen >> cl[0] & 1) == 0 && (chosen >> cl[1] & 1) == 0) {
          return;
        }
      }
      if (best[0] < 0 || cost < best[0]) {
        best[0] = cost;
      }
      return;
    }
    search(m, o + 1, covered, chosen, cost, best);
    if ((covered & m.mask[o]) == 0) {
      search(m, o + 1, covered | m.mask[o], chosen | 1L << o, cost + m.weight[o], best);
    }
  }

  private static String fzn(Model m) {
    int options = m.mask.length;
    StringBuilder sb = new StringBuilder();
    for (int o = 0; o < options; o++) {
      sb.append("var bool: x").append(o).append(" :: output_var;\n");
      sb.append("var 0..1: y").append(o).append(";\n");
    }
    sb.append("var 0..1000: obj :: output_var;\n");
    for (int o = 0; o < options; o++) {
      sb.append("constraint bool2int(x").append(o).append(", y").append(o).append(");\n");
    }
    for (int e = 0; e < m.n; e++) {
      List<Integer> cover = new ArrayList<>();
      for (int o = 0; o < options; o++) {
        if ((m.mask[o] >> e & 1) == 1) {
          cover.add(o);
        }
      }
      if (cover.isEmpty()) {
        // no option covers e: the model has no solution
        sb.append("constraint bool_eq(true, false);\n");
        continue;
      }
      String ones = String.join(", ", cover.stream().map(o -> "1").toList());
      if (e % 2 == 0) {
        sb.append("constraint int_lin_eq([")
            .append(ones)
            .append("], [")
            .append(String.join(", ", cover.stream().map(o -> "y" + o).toList()))
            .append("], 1);\n");
      } else {
        sb.append("constraint bool_lin_eq([")
            .append(ones)
            .append("], [")
            .append(String.join(", ", cover.stream().map(o -> "x" + o).toList()))
            .append("], 1);\n");
      }
    }
    for (int[] cl : m.clauses) {
      sb.append("constraint bool_clause([x")
          .append(cl[0])
          .append(", x")
          .append(cl[1])
          .append("], []);\n");
    }
    StringBuilder coefs = new StringBuilder();
    StringBuilder ys = new StringBuilder();
    for (int o = 0; o < options; o++) {
      coefs.append(m.weight[o]).append(", ");
      ys.append("y").append(o).append(", ");
    }
    sb.append("constraint int_lin_eq([")
        .append(coefs)
        .append("-1], [")
        .append(ys)
        .append("obj], 0);\n");
    sb.append("solve minimize obj;\n");
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

  @Test
  void coverModelsHaveTheOptimumOfEnumeration() throws IOException {
    Random r = new Random(SEED);
    List<String> failures = new ArrayList<>();
    System.setProperty("jacop.lcg.check", "true");
    // the detection is tested in every mode, also where it is off by default
    System.setProperty("org.jacop.fz.exactCover", "true");
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < 5; trial++) {
        Model m = randomModel(r);
        int expected = bruteForce(m);
        String model = fzn(m);
        String[][] runs = {{"--lcg"}, {"--lcg", "-f"}, {"--lcg", "off"}, {"--lcg", "off", "-f"}};
        for (String[] options : runs) {
          check(failures, trial, String.join(" ", options), expected, solve(model, options), model);
        }
        System.setProperty("org.jacop.fz.exactCover", "false");
        try {
          check(failures, trial, "without ExactCover", expected, solve(model, "--lcg"), model);
        } finally {
          System.setProperty("org.jacop.fz.exactCover", "true");
        }
      }
    } catch (IllegalStateException e) {
      failures.add(e.getMessage());
    } finally {
      System.clearProperty("jacop.lcg.check");
      System.clearProperty("org.jacop.fz.exactCover");
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
  }

  private static void check(
      List<String> failures, int trial, String run, int expected, Integer got, String model) {
    if (got == null || got != expected) {
      failures.add(
          "trial " + trial + " " + run + ": expected " + expected + ", got " + got + "\n" + model);
    }
  }
}
