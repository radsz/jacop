/*
 * PortfolioSplitTest.java
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
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * LCG threads of the portfolio that divide one search tree (option portfolio-split) give the
 * answers of one thread: the same optimum, unsatisfiability and solutions that satisfy the model.
 */
@Timeout(180)
class PortfolioSplitTest {

  @TempDir Path tmp;

  // split threads alone, mixed with the portfolio, and in the default (annotation) mode
  private static final String[][] LAYOUTS = {
    {"-f", "-p", "4", "--free-config", "portfolio-split=4"},
    {"-f", "-p", "4", "--free-config", "portfolio-split=2"},
    {"-p", "3", "--free-config", "portfolio-split=2"},
  };

  @Test
  void splitThreadsFindTheOptimumOfOneThread() throws IOException {
    Random random = new Random(7);
    for (int instance = 0; instance < 3; instance++) {
      Path fzn = write(knapsack(random));
      Integer reference = objective(run("-t", "30000", "--lcg", "off", fzn.toString()));
      for (String[] layout : LAYOUTS) {
        String out = run(args(layout, fzn));
        assertTrue(out.contains("=========="), String.join(" ", layout) + "\n" + out);
        assertEquals(reference, objective(out), String.join(" ", layout) + "\n" + out);
      }
    }
  }

  @Test
  void splitThreadsJoinAndSolveALargerModel() throws IOException {
    // a knapsack of 60 items with profits close to the weights
    Path fzn = write(knapsack(new Random(5), 60, 1000, 1000, 45000));
    Integer reference = objective(run("-t", "60000", "--lcg", "off", fzn.toString()));
    for (String[] layout : new String[][] {LAYOUTS[0], LAYOUTS[1]}) {
      String out = run(args(layout, fzn));
      assertTrue(out.contains("=========="), String.join(" ", layout) + "\n" + out);
      assertEquals(reference, objective(out), String.join(" ", layout) + "\n" + out);
      // every split thread joined the tree
      Matcher joined = Pattern.compile("portfolioSplitThreads=(\\d+)").matcher(out);
      assertTrue(joined.find(), String.join(" ", layout) + "\n" + out);
      String split = layout[layout.length - 1];
      assertEquals(
          split.substring(split.indexOf('=') + 1),
          joined.group(1),
          String.join(" ", layout) + "\n" + out);
    }
  }

  @Test
  void splitThreadsProveUnsatisfiability() throws IOException {
    // an odd sum of even terms, which bounds reasoning does not see before the last variable
    StringBuilder m = new StringBuilder("array [1..6] of var 0..9: p :: output_array([1..6]);\n");
    m.append("constraint int_lin_eq([2, 4, 2, 6, 2, 2], p, 41);\n");
    m.append("constraint int_lin_le([1, -1], [p[1], p[2]], 8);\n");
    m.append("solve :: int_search(p, input_order, indomain_min, complete) satisfy;\n");
    Path fzn = write(m.toString());
    for (String[] layout : LAYOUTS) {
      String out = run(args(layout, fzn));
      assertTrue(out.contains("=====UNSATISFIABLE====="), String.join(" ", layout) + "\n" + out);
    }
  }

  @Test
  void splitThreadsGiveASolutionOfASatisfiableModel() throws IOException {
    // ten queens
    int n = 10;
    StringBuilder m =
        new StringBuilder("array [1..10] of var 1..10: q :: output_array([1..10]);\n");
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        String qi = "q[" + i + "]";
        String qj = "q[" + j + "]";
        m.append("constraint int_ne(").append(qi).append(", ").append(qj).append(");\n");
        m.append("constraint int_lin_ne([1, -1], [").append(qi).append(", ").append(qj);
        m.append("], ").append(j - i).append(");\n");
        m.append("constraint int_lin_ne([1, -1], [").append(qi).append(", ").append(qj);
        m.append("], ").append(i - j).append(");\n");
      }
    }
    m.append("solve :: int_search(q, input_order, indomain_min, complete) satisfy;\n");
    Path fzn = write(m.toString());
    for (String[] layout : LAYOUTS) {
      String out = run(args(layout, fzn));
      Matcher matcher =
          Pattern.compile("q = array1d\\(1\\.\\.10, \\[([0-9, ]+)\\]\\);").matcher(out);
      assertTrue(matcher.find(), String.join(" ", layout) + "\n" + out);
      String[] values = matcher.group(1).split(", ");
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          int qi = Integer.parseInt(values[i]);
          int qj = Integer.parseInt(values[j]);
          assertTrue(qi != qj && Math.abs(qi - qj) != j - i, out);
        }
      }
      assertFalse(out.contains("UNSATISFIABLE"), out);
    }
  }

  // a 0/1 knapsack with a conflict between pairs of items, minimising the negated profit
  private static String knapsack(Random random) {
    return knapsack(random, 14, 3, 15, 45);
  }

  private static String knapsack(
      Random random, int n, int minWeight, int weightRange, int capacity) {
    StringBuilder m = new StringBuilder();
    m.append("array [1..").append(n).append("] of var 0..1: x :: output_array([1..").append(n);
    m.append("]);\nvar -500000..0: cost :: output_var;\n");
    StringBuilder weights = new StringBuilder();
    StringBuilder profits = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      String sep = i == 1 ? "" : ", ";
      int weight = minWeight + random.nextInt(weightRange);
      weights.append(sep).append(weight);
      // profits close to the weights make the instances of many items hard
      int profit = n > 20 ? weight + random.nextInt(30) : 2 + random.nextInt(20);
      profits.append(sep).append(-profit);
      vars.append(sep).append("x[").append(i).append(']');
    }
    m.append("constraint int_lin_le([")
        .append(weights)
        .append("], [")
        .append(vars)
        .append("], ")
        .append(capacity)
        .append(");\n");
    m.append("constraint int_lin_eq([").append(profits).append(", -1], [").append(vars);
    m.append(", cost], 0);\n");
    for (int k = 0; k < 6; k++) {
      int a = 1 + random.nextInt(n);
      int b = 1 + random.nextInt(n);
      if (a != b) {
        m.append("constraint int_lin_le([1, 1], [x[").append(a).append("], x[").append(b);
        m.append("]], 1);\n");
      }
    }
    m.append("solve :: int_search(x, input_order, indomain_max, complete) minimize cost;\n");
    return m.toString();
  }

  private static Integer objective(String out) {
    Matcher matcher = Pattern.compile("(?m)^cost = (-?\\d+);").matcher(out);
    Integer last = null;
    while (matcher.find()) {
      last = Integer.parseInt(matcher.group(1));
    }
    return last;
  }

  private static String[] args(String[] layout, Path fzn) {
    List<String> a = new ArrayList<>(List.of("-t", "30000", "-s", "--search-statistics"));
    a.addAll(List.of(layout));
    a.add(fzn.toString());
    return a.toArray(new String[0]);
  }

  private Path write(String model) throws IOException {
    Path fzn = Files.createTempFile(tmp, "model", ".fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    return fzn;
  }

  private static String run(String... args) {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream o = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(o);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
