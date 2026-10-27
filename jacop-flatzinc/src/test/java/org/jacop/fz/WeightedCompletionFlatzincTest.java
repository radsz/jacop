/*
 * WeightedCompletionFlatzincTest.java
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
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the detection of weighted completion times on unary resources in the FlatZinc front end,
 * which posts a redundant WeightedCompletion: the solutions and optima must match those of the
 * model without it.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class WeightedCompletionFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.weightedCompletion";

  @TempDir Path tmp;

  /**
   * A random single machine model: tasks on a cumulative that is a unary resource, some
   * precedences, end variables for some tasks, and a weighted sum of starts and ends that defines
   * (or bounds) y0.
   */
  private static String randomModel(Random random, boolean optimize) {
    int n = 2 + random.nextInt(3);
    int horizon = 6 + random.nextInt(4);
    StringBuilder fzn = new StringBuilder();
    int[] d = new int[n];
    for (int i = 0; i < n; i++) {
      d[i] = 1 + random.nextInt(3);
      fzn.append("var ")
          .append(random.nextInt(3))
          .append("..")
          .append(horizon)
          .append(": s")
          .append(i)
          .append(";\n");
      fzn.append("var 0..").append(horizon + 3).append(": e").append(i).append(";\n");
    }
    fzn.append("var ")
        .append(random.nextInt(5) - 4)
        .append("..")
        .append(optimize ? 400 : 10 * n + random.nextInt(25 * n))
        .append(": y0:: output_var;\n");
    if (random.nextInt(3) == 0) {
      fzn.append("var 0..3: y1;\n");
    }
    String ss = IntStream.range(0, n).mapToObj(i -> "s" + i).collect(Collectors.joining(","));
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: s:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(ss)
        .append("];\n");
    // a unary resource: uses 1 and capacity 1, or uses 2 and capacity 3
    boolean wide = random.nextBoolean();
    fzn.append("constraint jacop_cumulative(s,")
        .append(Arrays.toString(d).replace(" ", ""))
        .append(',')
        .append(Arrays.toString(IntStream.generate(() -> wide ? 2 : 1).limit(n).toArray()))
        .append(',')
        .append(wide ? 3 : 1)
        .append(");\n");
    for (int i = 0; i < n; i++) {
      // e = s + d
      fzn.append("constraint int_lin_eq([1,-1],[s")
          .append(i)
          .append(",e")
          .append(i)
          .append("],")
          .append(-d[i])
          .append(");\n");
    }
    if (random.nextBoolean()) {
      // a precedence s_i + d_i <= s_j
      int i = random.nextInt(n);
      int j = (i + 1) % n;
      fzn.append("constraint int_lin_le([1,-1],[s")
          .append(i)
          .append(",s")
          .append(j)
          .append("],")
          .append(-d[i])
          .append(");\n");
    }

    // sign * (sum w * x - y0 [- y1]) = sign * c, or <= c with sign 1
    boolean equation = random.nextInt(4) != 0;
    int sign = equation && random.nextBoolean() ? -1 : 1;
    StringBuilder coefficients = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (int i = 0; i < n; i++) {
      int w = random.nextInt(4);
      coefficients.append(sign * w).append(',');
      vars.append(random.nextBoolean() ? "e" : "s").append(i).append(',');
    }
    coefficients.append(-sign);
    vars.append("y0");
    if (fzn.indexOf(": y1") >= 0) {
      coefficients.append(',').append(sign);
      vars.append(",y1");
    }
    int c = random.nextInt(7) - 3;
    fzn.append("constraint int_lin_")
        .append(equation ? "eq" : "le")
        .append("([")
        .append(coefficients)
        .append("],[")
        .append(vars)
        .append("],")
        .append(sign * c)
        .append(");\n");
    fzn.append(optimize ? "solve minimize y0;\n" : "solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void detectedConstraintKeepsAllSolutions() throws IOException {
    Random random = new Random(5);
    int detected = 0;
    for (int trial = 0; trial < 200; trial++) {
      String model = randomModel(random, false);
      String out = run(model, true, "-a", "-debug");
      detected += out.contains("WeightedCompletion") ? 1 : 0;
      assertEquals(
          solutions(run(model, false, "-a")), solutions(out), "trial " + trial + "\n" + model);
    }
    assertTrue(detected > 60, "detected " + detected);
  }

  @Test
  void detectedConstraintKeepsOptima() throws IOException {
    Random random = new Random(6);
    for (int trial = 0; trial < 200; trial++) {
      String model = randomModel(random, true);
      assertEquals(
          optimum(run(model, false)), optimum(run(model, true)), "trial " + trial + "\n" + model);
    }
  }

  @Test
  void jobShopWeighsEveryMachine() throws IOException {
    // two jobs on two machines, the objective weighs the end of the last task of each job
    String fzn =
        """
        var 0..20: a1;
        var 0..20: a2;
        var 0..20: b1;
        var 0..20: b2;
        var 0..200: cost:: output_var;
        array [1..2] of var int: m1 = [a1,b2];
        array [1..2] of var int: m2 = [a2,b1];
        constraint int_lin_le([1,-1],[a1,a2],-3);
        constraint int_lin_le([1,-1],[b1,b2],-2);
        constraint jacop_cumulative(m1,[3,4],[1,1],1);
        constraint jacop_cumulative(m2,[2,2],[1,1],1);
        constraint int_lin_eq([2,1,-1],[a2,b2,cost],-8);
        solve minimize cost;
        """;
    String on = run(fzn, true, "-debug");
    assertEquals(2, on.split("% redundant WeightedCompletion", -1).length - 1, on);
    // a1 = 0, a2 = 3, b1 = 0, b2 = 3: 2 * 5 + 1 * 7
    assertEquals("17", optimum(on));
    assertEquals("17", optimum(run(fzn, false)));
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    String fzn =
        """
        var 0..9: s0;
        var 0..9: s1;
        var 0..9: s2;
        var 0..99: cost:: output_var;
        array [1..3] of var int: s:: output_array([1..3]) = [s0,s1,s2];
        constraint jacop_cumulative(s,[2,1,3],[1,1,1],1);
        constraint int_lin_eq([1,3,2,-1],[s0,s1,s2,cost],-11);
        solve minimize cost;
        """;
    String on = run(fzn, true, "-debug");
    assertTrue(on.contains("WeightedCompletion"), on);
    assertFalse(run(fzn, false, "-debug").contains("WeightedCompletion"));
    // by decreasing weight per duration: s1 = 0, s2 = 1, s0 = 4: 3 * 1 + 2 * 4 + 1 * 6
    assertEquals("17", optimum(on));
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

  // the value of y0 or cost in the last solution, or the status when there is none
  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("y0 = ") || line.startsWith("cost = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out);
    return last;
  }
}
