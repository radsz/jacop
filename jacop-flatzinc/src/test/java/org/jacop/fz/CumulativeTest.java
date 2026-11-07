/*
 * CumulativeTest.java
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
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the FlatZinc builtin jacop_cumulative(s, d, r, b) on small random instances by comparing
 * every solution JaCoP finds with a brute-force enumeration of all assignments. The instances reach
 * the different ways the builtin is posted (a single task, unary resources, ground tasks and
 * general tasks), including tasks with zero duration that may use more than the limit.
 */
class CumulativeTest {

  private static final int TRIALS = 200;

  private static final int TIMEOUT_MS = 60_000;

  @TempDir Path tmp;

  /** An argument of the constraint: a variable with domain lo..hi, or a constant when lo == hi. */
  private record Arg(String name, int lo, int hi) {

    String fzn() {
      return lo == hi ? Integer.toString(lo) : name;
    }
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void allSolutionsMatchBruteForce() throws IOException {
    Random random = new Random(2026);
    for (int trial = 0; trial < TRIALS; trial++) {
      int n = 1 + random.nextInt(3);
      boolean groundDurations = random.nextBoolean();
      boolean groundResources = random.nextBoolean();
      List<Arg> args = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        args.add(arg(random, "s" + i, 0, 3, false));
      }
      for (int i = 0; i < n; i++) {
        args.add(arg(random, "d" + i, 0, 2, groundDurations));
      }
      for (int i = 0; i < n; i++) {
        args.add(arg(random, "r" + i, 0, 3, groundResources));
      }
      int limit = 1 + random.nextInt(3);

      StringBuilder fzn = new StringBuilder();
      for (Arg a : args) {
        if (a.lo() != a.hi()) {
          fzn.append("var ")
              .append(a.lo())
              .append("..")
              .append(a.hi())
              .append(": ")
              .append(a.name())
              .append(":: output_var;\n");
        }
      }
      fzn.append("constraint jacop_cumulative(")
          .append(array(args.subList(0, n)))
          .append(",")
          .append(array(args.subList(n, 2 * n)))
          .append(",")
          .append(array(args.subList(2 * n, 3 * n)))
          .append(",")
          .append(limit)
          .append(");\nsolve satisfy;\n");

      Set<String> expected = new TreeSet<>();
      bruteForce(args, n, limit, new int[3 * n], 0, expected);

      List<String> actual = solve(fzn.toString());
      Set<String> actualSet = new TreeSet<>(actual);
      assertEquals(actual.size(), actualSet.size(), "duplicate solutions for\n" + fzn);
      assertEquals(expected, actualSet, "solutions differ for\n" + fzn);
    }
  }

  private static Arg arg(Random random, String name, int lo, int hi, boolean ground) {
    int a = lo + random.nextInt(hi - lo + 1);
    int b = ground ? a : a + random.nextInt(hi - a + 1);
    return new Arg(name, a, b);
  }

  private static String array(List<Arg> args) {
    return "[" + String.join(",", args.stream().map(Arg::fzn).toList()) + "]";
  }

  private static void bruteForce(
      List<Arg> args, int n, int limit, int[] values, int index, Set<String> solutions) {
    if (index == values.length) {
      for (int t = 0; t <= 6; t++) {
        int use = 0;
        for (int i = 0; i < n; i++) {
          if (values[i] <= t && t < values[i] + values[n + i]) {
            use += values[2 * n + i];
          }
        }
        if (use > limit) {
          return;
        }
      }
      StringBuilder sol = new StringBuilder();
      for (int i = 0; i < values.length; i++) {
        Arg a = args.get(i);
        if (a.lo() != a.hi()) {
          sol.append(a.name()).append("=").append(values[i]).append(";");
        }
      }
      solutions.add(sol.toString());
      return;
    }
    Arg a = args.get(index);
    for (int v = a.lo(); v <= a.hi(); v++) {
      values[index] = v;
      bruteForce(args, n, limit, values, index + 1, solutions);
    }
  }

  /** Solves the model for all solutions and returns each one in canonical form. */
  private List<String> solve(String model) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);

    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try {
      System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
      new Fz2jacop().callMain(new String[] {"-a", fzn.toString()});
    } finally {
      System.setOut(originalOut);
    }

    List<String> lines = captured.toString(StandardCharsets.UTF_8).lines().toList();
    List<String> solutions = new ArrayList<>();
    if (lines.contains("=====UNSATISFIABLE=====")) {
      return solutions;
    }
    assertTrue(
        lines.contains("=========="), "search did not complete for\n" + model + "\n" + lines);

    // output variables are printed in declaration order, matching the brute-force order
    StringBuilder current = new StringBuilder();
    for (String line : lines) {
      String l = line.trim();
      if ("----------".equals(l)) {
        solutions.add(current.toString());
        current.setLength(0);
      } else if (l.contains("=") && !l.startsWith("=") && !l.startsWith("%")) {
        String name = l.substring(0, l.indexOf('=')).trim();
        String value = l.substring(l.indexOf('=') + 1, l.lastIndexOf(';')).trim();
        current.append(name).append("=").append(value).append(";");
      }
    }
    return solutions;
  }
}
