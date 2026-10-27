/*
 * KnapsackFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.jacop.fz.constraints.KnapsackDetector;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the detection of multi-dimensional knapsacks in the FlatZinc front end, which posts a
 * redundant Knapsack on a surrogate of the capacity rows: the solutions and optima must match those
 * of the model without it.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class KnapsackFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.knapsack";

  @TempDir Path tmp;

  // a profit as an equation, a lower bound (int_lin_le with negative coefficients) or an objective
  private enum Kind {
    EQUATION,
    LOWER_BOUND,
    OBJECTIVE
  }

  private static String randomModel(Random random, Kind kind) {
    int n = 4 + random.nextInt(6);
    int m = 1 + random.nextInt(3);
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..1: x").append(i).append(";\n");
    }
    String xs = IntStream.range(0, n).mapToObj(i -> "x" + i).collect(Collectors.joining(","));
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");
    for (int r = 0; r < m; r++) {
      int[] w = new int[n];
      long sum = 0;
      for (int i = 0; i < n; i++) {
        w[i] = random.nextInt(4) == 0 ? 0 : 1 + random.nextInt(20);
        sum += w[i];
      }
      int[] vars = IntStream.range(0, n).filter(i -> w[i] > 0).toArray();
      if (vars.length < 2) {
        continue;
      }
      fzn.append(linear(Arrays.stream(vars).map(i -> w[i]).toArray(), vars, "le"))
          .append(",")
          .append(sum * (3 + random.nextInt(5)) / 10)
          .append(");\n");
    }
    int[] p = IntStream.range(0, n).map(i -> 1 + random.nextInt(30)).toArray();
    int[] all = IntStream.range(0, n).toArray();
    int target = (int) (Arrays.stream(p).sum() * (4 + random.nextInt(5)) / 10.0);
    if (kind == Kind.OBJECTIVE) {
      // a lower bound on the objective, as branch and bound gives, lets the relaxation prune
      fzn.insert(0, "var " + target + "..1000: obj:: output_var;\n");
    }
    switch (kind) {
      case EQUATION -> fzn.append(linear(p, all, "")).append(",").append(target).append(");\n");
      case LOWER_BOUND ->
          fzn.append(linear(Arrays.stream(p).map(v -> -v).toArray(), all, "le"))
              .append(",")
              .append(-target)
              .append(");\n");
      case OBJECTIVE -> {
        int[] q = Arrays.copyOf(p, n + 1);
        q[n] = -1;
        fzn.append("constraint int_lin_eq(")
            .append(Arrays.toString(q).replace(" ", ""))
            .append(",[")
            .append(xs)
            .append(",obj],0);\n");
      }
    }
    fzn.append(kind == Kind.OBJECTIVE ? "solve maximize obj;\n" : "solve satisfy;\n");
    return fzn.toString();
  }

  // "constraint int_lin_eq(a,[x...]" (or int_lin_<kind>) without the right hand side
  private static String linear(int[] a, int[] vars, String kind) {
    return "constraint int_lin_"
        + (kind.isEmpty() ? "eq" : kind)
        + "("
        + Arrays.toString(a).replace(" ", "")
        + ","
        + Arrays.stream(vars).mapToObj(i -> "x" + i).collect(Collectors.joining(",", "[", "]"));
  }

  @Test
  void detectedKnapsackKeepsAllSolutions() throws IOException {
    Random random = new Random(7);
    int detected = 0;
    for (int trial = 0; trial < 300; trial++) {
      String model = randomModel(random, trial % 2 == 0 ? Kind.EQUATION : Kind.LOWER_BOUND);
      String out = run(model, true, "-a", "-debug");
      detected += out.contains("redundant surrogate") ? 1 : 0;
      assertEquals(
          solutions(run(model, false, "-a")), solutions(out), "trial " + trial + "\n" + model);
    }
    assertTrue(detected > 60, "detected " + detected);
  }

  @Test
  void detectedKnapsackKeepsOptima() throws IOException {
    Random random = new Random(8);
    int detected = 0;
    for (int trial = 0; trial < 200; trial++) {
      String model = randomModel(random, Kind.OBJECTIVE);
      String out = run(model, true, "-debug");
      detected += out.contains("redundant surrogate") ? 1 : 0;
      assertEquals(optimum(run(model, false)), optimum(out), "trial " + trial + "\n" + model);
    }
    assertTrue(detected > 40, "detected " + detected);
  }

  @Test
  void dualsOfOneRowGiveTheDantzigBound() {
    Random random = new Random(9);
    for (int trial = 0; trial < 500; trial++) {
      int n = 2 + random.nextInt(12);
      double[] w = new double[n];
      double[] p = new double[n];
      for (int j = 0; j < n; j++) {
        w[j] = 1 + random.nextInt(30);
        p[j] = 1 + random.nextInt(30);
      }
      double c = random.nextInt((int) Arrays.stream(w).sum() + 1);
      double[] y = KnapsackDetector.duals(new double[][] {w}, new double[] {c}, p);
      // the Lagrangian bound of the multiplier, against the LP bound by Dantzig's greedy
      double bound = y[0] * c;
      for (int j = 0; j < n; j++) {
        bound += Math.max(0, p[j] - y[0] * w[j]);
      }
      Integer[] order = IntStream.range(0, n).boxed().toArray(Integer[]::new);
      Arrays.sort(order, (a, b) -> Double.compare(p[b] / w[b], p[a] / w[a]));
      double left = c;
      double dantzig = 0;
      for (int j : order) {
        double take = Math.min(1, left / w[j]);
        dantzig += take * p[j];
        left -= take * w[j];
      }
      assertEquals(dantzig, bound, 1e-6, "trial " + trial);
    }
  }

  @Test
  void dualsOfSeveralRowsGiveTheLinearRelaxationBound() {
    Random random = new Random(10);
    for (int trial = 0; trial < 300; trial++) {
      int n = 2 + random.nextInt(8);
      int m = 1 + random.nextInt(4);
      double[][] a = new double[m][n];
      double[] b = new double[m];
      double[] p = new double[n];
      for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
          a[i][j] = random.nextInt(4) == 0 ? 0 : 1 + random.nextInt(20);
        }
        b[i] = random.nextInt((int) Arrays.stream(a[i]).sum() + 1);
      }
      for (int j = 0; j < n; j++) {
        p[j] = 1 + random.nextInt(30);
      }
      double[] y = KnapsackDetector.duals(a, b, p);
      double bound = 0;
      for (int i = 0; i < m; i++) {
        assertTrue(y[i] >= 0);
        bound += y[i] * b[i];
      }
      for (int j = 0; j < n; j++) {
        double reduced = p[j];
        for (int i = 0; i < m; i++) {
          reduced -= y[i] * a[i][j];
        }
        bound += Math.max(0, reduced);
      }
      // weak duality: never below the integer optimum, by enumeration
      double best = 0;
      for (int s = 0; s < 1 << n; s++) {
        boolean fits = true;
        for (int i = 0; i < m && fits; i++) {
          double used = 0;
          for (int j = 0; j < n; j++) {
            used += (s >> j & 1) * a[i][j];
          }
          fits = used <= b[i];
        }
        if (fits) {
          double profit = 0;
          for (int j = 0; j < n; j++) {
            profit += (s >> j & 1) * p[j];
          }
          best = Math.max(best, profit);
        }
      }
      assertTrue(bound >= best - 1e-6, "trial " + trial);
      // and at most the bound of any single row, which is a surrogate too
      for (int i = 0; i < m; i++) {
        double[] one = KnapsackDetector.duals(new double[][] {a[i]}, new double[] {b[i]}, p);
        double single = one[0] * b[i];
        for (int j = 0; j < n; j++) {
          single += Math.max(0, p[j] - one[0] * a[i][j]);
        }
        assertTrue(bound <= single + 1e-6, "trial " + trial + " row " + i);
      }
    }
  }

  @Test
  void multiKnapsackIsSolvedWithFewFailures() throws IOException {
    // mknap1-6 of the MiniZinc benchmarks; without the surrogate no solution in 20 s
    int[] c = {
      560, 1125, 300, 620, 2100, 431, 68, 328, 47, 122, 322, 196, 41, 25, 425, 4260, 416, 115, 82,
      22, 631, 132, 420, 86, 42, 103, 215, 81, 91, 26, 49, 420, 316, 72, 71, 49, 108, 116, 90, 738,
      1811, 430, 3060, 215, 58, 296, 620, 418, 47, 81
    };
    int[] b = {800, 650, 550, 550, 650};
    int[][] a = {
      {
        40, 91, 10, 30, 160, 20, 3, 12, 3, 18, 9, 25, 1, 1, 10, 280, 10, 8, 1, 1, 49, 8, 21, 6, 1,
        5, 10, 8, 2, 1, 0, 10, 42, 6, 4, 8, 0, 10, 1, 40, 86, 11, 120, 8, 3, 32, 28, 13, 2, 4
      },
      {
        16, 92, 41, 16, 150, 23, 4, 18, 6, 0, 12, 8, 2, 1, 0, 200, 20, 6, 2, 1, 70, 9, 22, 4, 1, 5,
        10, 6, 4, 0, 4, 12, 8, 4, 3, 0, 10, 0, 6, 28, 93, 9, 30, 22, 0, 36, 45, 13, 2, 2
      },
      {
        38, 39, 32, 71, 80, 26, 5, 40, 8, 12, 30, 15, 0, 1, 23, 100, 0, 20, 3, 0, 40, 6, 8, 0, 6, 4,
        22, 4, 6, 1, 5, 14, 8, 2, 8, 0, 20, 0, 0, 6, 12, 6, 80, 13, 6, 22, 14, 0, 1, 2
      },
      {
        8, 71, 30, 60, 200, 18, 6, 30, 4, 8, 31, 6, 3, 0, 18, 60, 21, 4, 0, 2, 32, 15, 31, 2, 2, 7,
        8, 2, 8, 0, 2, 8, 6, 7, 1, 0, 0, 20, 8, 14, 20, 2, 40, 6, 1, 14, 20, 12, 0, 1
      },
      {
        38, 52, 30, 42, 170, 9, 7, 20, 0, 3, 21, 4, 1, 2, 14, 310, 8, 4, 6, 1, 18, 15, 38, 10, 4, 8,
        6, 0, 0, 3, 0, 10, 6, 1, 3, 0, 3, 5, 4, 0, 30, 12, 16, 18, 3, 16, 22, 30, 4, 0
      }
    };
    int n = c.length;
    StringBuilder fzn = new StringBuilder();
    for (int j = 0; j < n; j++) {
      fzn.append("var 0..1: x").append(j).append(";\n");
    }
    String xs = IntStream.range(0, n).mapToObj(j -> "x" + j).collect(Collectors.joining(","));
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");
    for (int i = 0; i < b.length; i++) {
      int[] row = a[i];
      int[] vars = IntStream.range(0, n).filter(j -> row[j] > 0).toArray();
      fzn.append(linear(Arrays.stream(vars).map(j -> row[j]).toArray(), vars, "le"))
          .append(",")
          .append(b[i])
          .append(");\n");
    }
    fzn.append(linear(c, IntStream.range(0, n).toArray(), "")).append(",16537);\n");
    fzn.append("solve :: int_search(x,input_order,indomain_max,complete) satisfy;\n");

    String out = run(fzn.toString(), true, "-s", "-t", "20000");
    assertTrue(out.contains("----------"), out);
    Matcher failures = Pattern.compile("failures=(\\d+)").matcher(out);
    assertTrue(failures.find(), out);
    assertTrue(Long.parseLong(failures.group(1)) < 100_000, out);
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    String fzn =
        """
        var 0..1: x0;
        var 0..1: x1;
        var 0..1: x2;
        var 0..1: x3;
        var 0..1: x4;
        array [1..5] of var int: x:: output_array([1..5]) = [x0,x1,x2,x3,x4];
        constraint int_lin_le([3,4,5,6,2],[x0,x1,x2,x3,x4],10);
        constraint int_lin_le([6,5,4,3,2],[x0,x1,x2,x3,x4],10);
        constraint int_lin_eq([5,6,7,8,1],[x0,x1,x2,x3,x4],13);
        solve satisfy;
        """;
    String on = run(fzn, true, "-a", "-debug");
    // the relaxation bound 14.4 minus the reduced cost of x4 (1.9) is below 13: x4 = 0
    assertTrue(on.contains("redundant surrogate"), on);
    assertFalse(run(fzn, false, "-debug").contains("redundant surrogate"));
    assertEquals(
        Set.of("x = array1d(1..5, [0, 1, 1, 0, 0]);", "x = array1d(1..5, [1, 0, 0, 1, 0]);"),
        solutions(on));
  }

  private String run(String model, boolean detection, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (!detection) {
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
