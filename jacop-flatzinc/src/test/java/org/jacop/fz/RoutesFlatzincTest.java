/*
 * RoutesFlatzincTest.java
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
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the detection of vehicle routes in a two-index arc model with Miller-Tucker-Zemlin load
 * rows, which posts a redundant Routes: all solutions must match a brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class RoutesFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.routes";

  @TempDir Path tmp;

  @BeforeEach
  void detectionOn() {
    System.setProperty(PROPERTY, "true");
  }

  @AfterEach
  void detectionDefault() {
    System.clearProperty(PROPERTY);
  }

  /** The FlatZinc of a random routing model and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce) {}

  // customers 1..n, depot 0; arc (i, j) for i != j is x[i * (n + 1) + j]; a zero demand makes
  // the load rows allow a circuit without the depot, which the detection must leave alone
  private static Model randomModel(Random random, boolean zeroDemands) {
    // three customers, the fewest the detection takes
    int n = 3;
    // a demand below the capacity, so no load is fixed and its rows stay rows of three
    int capacity = 4 + random.nextInt(3);
    int[] demand = new int[n + 1];
    for (int j = 1; j <= n; j++) {
      demand[j] = (zeroDemands ? 0 : 1) + random.nextInt(3);
    }
    int arcs = (n + 1) * (n + 1);
    StringBuilder fzn = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    for (int a = 0; a < arcs; a++) {
      int i = a / (n + 1);
      int j = a % (n + 1);
      String domain = i == j ? "0..0" : "0..1";
      fzn.append("var ").append(domain).append(": x").append(a).append(";\n");
      xs.append(a == 0 ? "" : ",").append('x').append(a);
    }
    for (int j = 1; j <= n; j++) {
      fzn.append("var ")
          .append(Math.min(demand[j], capacity))
          .append("..")
          .append(capacity)
          .append(": u")
          .append(j)
          .append(";\n");
    }
    fzn.append("array [1..")
        .append(arcs)
        .append("] of var int: x:: output_array([1..")
        .append(arcs)
        .append("]) = [")
        .append(xs)
        .append("];\n");
    for (int v = 1; v <= n; v++) {
      for (int side = 0; side < 2; side++) {
        StringBuilder coefs = new StringBuilder();
        StringBuilder vars = new StringBuilder();
        for (int w = 0; w <= n; w++) {
          if (w != v) {
            int a = side == 0 ? v * (n + 1) + w : w * (n + 1) + v;
            coefs.append(coefs.isEmpty() ? "" : ",").append(1);
            vars.append(vars.isEmpty() ? "" : ",").append('x').append(a);
          }
        }
        fzn.append("constraint int_lin_eq([")
            .append(coefs)
            .append("],[")
            .append(vars)
            .append("],1);\n");
      }
    }
    for (int i = 1; i <= n; i++) {
      for (int j = 1; j <= n; j++) {
        if (i != j) {
          fzn.append("constraint int_lin_le([1,-1,")
              .append(capacity)
              .append("],[u")
              .append(i)
              .append(",u")
              .append(j)
              .append(",x")
              .append(i * (n + 1) + j)
              .append("],")
              .append(capacity - demand[j])
              .append(");\n");
        }
      }
    }
    fzn.append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] x = new int[arcs];
    for (long mask = 0; mask < 1L << arcs; mask++) {
      boolean ok = true;
      for (int a = 0; a < arcs; a++) {
        x[a] = (int) (mask >> a & 1);
        if (x[a] == 1 && a / (n + 1) == a % (n + 1)) {
          ok = false;
        }
      }
      if (ok && degrees(x, n) && loads(x, n, demand, capacity, new int[n + 1], 1)) {
        expected.add("x = array1d(1.." + arcs + ", " + Arrays.toString(x) + ");");
      }
    }
    return new Model(fzn.toString(), expected);
  }

  private static boolean degrees(int[] x, int n) {
    for (int v = 1; v <= n; v++) {
      int in = 0;
      int out = 0;
      for (int w = 0; w <= n; w++) {
        out += x[v * (n + 1) + w];
        in += x[w * (n + 1) + v];
      }
      if (in != 1 || out != 1) {
        return false;
      }
    }
    return true;
  }

  // whether some loads u satisfy every load row, by enumeration
  private static boolean loads(int[] x, int n, int[] demand, int capacity, int[] u, int j) {
    if (j > n) {
      for (int a = 1; a <= n; a++) {
        for (int b = 1; b <= n; b++) {
          if (a != b && u[a] - u[b] + capacity * x[a * (n + 1) + b] > capacity - demand[b]) {
            return false;
          }
        }
      }
      return true;
    }
    for (u[j] = Math.min(demand[j], capacity); u[j] <= capacity; u[j]++) {
      if (loads(x, n, demand, capacity, u, j + 1)) {
        return true;
      }
    }
    return false;
  }

  @Test
  void detectedRoutesKeepAllSolutions() throws IOException {
    Random random = new Random(11);
    int detected = 0;
    for (int trial = 0; trial < 150; trial++) {
      Model model = randomModel(random, false);
      String out = run(model.fzn(), "-a", "-debug");
      if (out.contains("% redundant Routes")) {
        detected++;
      }
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
    assertEquals(150, detected);
  }

  @Test
  void loadRowsWithZeroDemandsAreNotRoutes() throws IOException {
    // two customers of zero demand may form a circuit 1 -> 2 -> 1 that the rows allow
    Random random = new Random(5);
    for (int trial = 0; trial < 40; trial++) {
      Model model = randomModel(random, true);
      String out = run(model.fzn(), "-a", "-debug");
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
  }

  @Test
  void detectionIsOnByDefault() throws IOException {
    Model model = randomModel(new Random(3), false);
    System.clearProperty(PROPERTY);
    assertTrue(run(model.fzn(), "-debug").contains("% redundant Routes"));
    System.setProperty(PROPERTY, "false");
    assertFalse(run(model.fzn(), "-debug").contains("% redundant Routes"));
  }

  private String run(String model, String... options) throws IOException {
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

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    new TreeSet<>(
                        Arrays.stream(s.strip().split("\\R"))
                            .filter(l -> !l.isBlank() && !l.startsWith("%"))
                            .toList())))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
