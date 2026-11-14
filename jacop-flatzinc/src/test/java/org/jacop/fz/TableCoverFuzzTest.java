/*
 * TableCoverFuzzTest.java
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
 * Random tilings written as tables and an all different, as XCSP3 Pentominoes are, solved with and
 * without the {@link org.jacop.constraints.TableCover} the front end adds, in and out of LCG with
 * the explanation checker on; the number of solutions of a tiling is enumerated by brute force.
 */
class TableCoverFuzzTest {

  private static final int TRIALS = Integer.getInteger("tablecoverfuzz.trials", 150);
  private static final long SEED = Long.getLong("tablecoverfuzz.seed", 20261108L);

  // the largest number of cells and of tuples of a group, beyond 3
  private static final int CELLS = Integer.getInteger("tablecoverfuzz.cells", 8);
  private static final int TUPLES = Integer.getInteger("tablecoverfuzz.tuples", 8);

  @TempDir Path tmp;

  // cells 0..cells-1 (and one spare cell when not exact); groups of variables with their tuples
  private static final class Tiling {
    final int cells;
    final boolean exact;
    final int[][][] tuples;

    Tiling(int cells, boolean exact, int[][][] tuples) {
      this.cells = cells;
      this.exact = exact;
      this.tuples = tuples;
    }
  }

  private static Tiling random(Random r) {
    int cells = 4 + r.nextInt(CELLS - 3);
    boolean exact = r.nextInt(3) > 0;
    List<int[][]> groups = new ArrayList<>();
    int used = 0;
    while (used < cells) {
      int k = Math.min(cells - used, 1 + r.nextInt(4));
      int m = 1 + r.nextInt(TUPLES);
      int[][] t = new int[m][k];
      for (int i = 0; i < m; i++) {
        // sorted cells as in a placement, sometimes a repeated one
        for (int j = 0; j < k; j++) {
          t[i][j] = r.nextInt(exact ? cells : cells + 1);
        }
        Arrays.sort(t[i]);
      }
      groups.add(t);
      used += k;
    }
    return new Tiling(cells, exact, groups.toArray(new int[0][][]));
  }

  // the number of solutions: a tuple per group, no cell twice
  private static int count(Tiling t, int g, long used) {
    if (g == t.tuples.length) {
      return 1;
    }
    int total = 0;
    for (int[] u : distinct(t.tuples[g])) {
      long mask = 0;
      boolean ok = true;
      for (int c : u) {
        ok &= (mask >> c & 1) == 0 && (used >> c & 1) == 0;
        mask |= 1L << c;
      }
      if (ok) {
        total += count(t, g + 1, used | mask);
      }
    }
    return total;
  }

  private static List<int[]> distinct(int[][] tuples) {
    List<int[]> out = new ArrayList<>();
    for (int[] u : tuples) {
      if (out.stream().noneMatch(v -> Arrays.equals(u, v))) {
        out.add(u);
      }
    }
    return out;
  }

  private static String fzn(Tiling t) {
    StringBuilder sb = new StringBuilder();
    int max = t.exact ? t.cells - 1 : t.cells;
    List<String> all = new ArrayList<>();
    for (int g = 0; g < t.tuples.length; g++) {
      for (int j = 0; j < t.tuples[g][0].length; j++) {
        String x = "x" + g + "_" + j;
        sb.append("var 0..").append(max).append(": ").append(x).append(" :: output_var;\n");
        all.add(x);
      }
    }
    for (int g = 0; g < t.tuples.length; g++) {
      List<String> xs = new ArrayList<>();
      for (int j = 0; j < t.tuples[g][0].length; j++) {
        xs.add("x" + g + "_" + j);
      }
      List<String> values = new ArrayList<>();
      for (int[] u : t.tuples[g]) {
        for (int c : u) {
          values.add(Integer.toString(c));
        }
      }
      sb.append("constraint jacop_table_int([")
          .append(String.join(", ", xs))
          .append("], [")
          .append(String.join(", ", values))
          .append("]);\n");
    }
    sb.append("constraint jacop_alldiff([").append(String.join(", ", all)).append("]);\n");
    sb.append("solve satisfy;\n");
    return sb.toString();
  }

  // the number of solutions found with -a, or -1 when the run did not finish
  private int solutions(String model, String... options) throws IOException {
    String out = run(model, options);
    if (out.contains("=====UNSATISFIABLE=====")) {
      return 0;
    }
    if (!out.contains("==========")) {
      return -1;
    }
    return out.split("----------", -1).length - 1;
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
  void tilingsHaveTheSolutionsOfEnumeration() throws IOException {
    Random r = new Random(SEED);
    List<String> failures = new ArrayList<>();
    System.setProperty("jacop.lcg.check", "true");
    // the detection is tested in every mode, also where it is off by default
    System.setProperty("org.jacop.fz.tableCover", "true");
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < 5; trial++) {
        Tiling t = random(r);
        int expected = count(t, 0, 0L);
        String model = fzn(t);
        String[][] runs = {{"-a", "--lcg"}, {"-a", "--lcg", "-f"}, {"-a", "--lcg", "off"}};
        for (String[] options : runs) {
          int got = solutions(model, options);
          if (got != expected) {
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
    } catch (IllegalStateException e) {
      failures.add(e.getMessage());
    } finally {
      System.clearProperty("jacop.lcg.check");
      System.clearProperty("org.jacop.fz.tableCover");
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
  }
}
