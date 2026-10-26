/*
 * StockingCostFlatzincTest.java
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
 * Checks the detection of stocking costs in the FlatZinc front end, which posts a redundant
 * StockingCost, and the jacop_stocking_cost predicate of the MiniZinc library: the solutions and
 * optima must match those of the model without it.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class StockingCostFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.stockingCost";

  @TempDir Path tmp;

  /** A random FlatZinc model and whether the detection must find it. */
  private record Model(String fzn, boolean detectable) {}

  private static Model randomModel(Random random, boolean optimize) {
    int n = 2 + random.nextInt(4);
    int capacity = random.nextInt(3) == 0 ? 2 : 1;
    StringBuilder fzn = new StringBuilder();
    boolean zero = false;
    for (int i = 0; i < n; i++) {
      int[] dom = IntStream.rangeClosed(0, 5).filter(v -> random.nextInt(4) != 0).toArray();
      if (dom.length == 0) {
        dom = new int[] {random.nextInt(6)};
      }
      zero |= dom[0] == 0;
      fzn.append("var ").append(set(dom)).append(": x").append(i).append(";\n");
    }
    int others = 1 + (random.nextInt(4) == 0 ? 1 : 0);
    for (int j = 0; j < others; j++) {
      fzn.append("var ")
          .append(random.nextInt(3) - 2)
          .append("..")
          .append(10 + random.nextInt(30))
          .append(": y")
          .append(j);
      fzn.append(j == 0 ? ":: output_var;\n" : ";\n");
    }
    String xs = IntStream.range(0, n).mapToObj(i -> "x" + i).collect(Collectors.joining(","));
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");

    boolean detectable = true;
    // the capacity: an alldifferent, or a gcc whose cover may miss a value
    if (capacity == 1 && random.nextBoolean()) {
      fzn.append("constraint jacop_alldiff(x);\n");
    } else {
      boolean missing = random.nextInt(5) == 0;
      int[] cover = IntStream.rangeClosed(missing ? 1 : 0, 5).toArray();
      // a cover without 0 bounds nothing when 0 is in a domain
      detectable &= !missing || !zero;
      fzn.append("constraint jacop_count_values_bounds(x,")
          .append(Arrays.toString(cover).replace(" ", ""))
          .append(',')
          .append(Arrays.toString(new int[cover.length]).replace(" ", ""))
          .append(',')
          .append(
              Arrays.toString(IntStream.generate(() -> capacity).limit(cover.length).toArray())
                  .replace(" ", ""))
          .append(");\n");
    }

    // the cost: sign * sum(h * x) + b * y = c, or the int_lin_le that bounds it from above
    boolean equation = random.nextInt(4) != 0;
    int sign = equation && random.nextBoolean() ? 1 : -1;
    boolean mixed = random.nextInt(8) == 0;
    detectable &= !mixed;
    int[] a = new int[n + others];
    for (int i = 0; i < n; i++) {
      a[i] = sign * (1 + random.nextInt(3));
    }
    if (mixed) {
      a[0] = -a[0];
    }
    for (int j = 0; j < others; j++) {
      a[n + j] = random.nextBoolean() ? 1 : -1;
    }
    String vars =
        xs + IntStream.range(0, others).mapToObj(j -> ",y" + j).collect(Collectors.joining());
    int c = random.nextInt(21) - 10;
    fzn.append("constraint int_lin_")
        .append(equation ? "eq" : "le")
        .append('(')
        .append(Arrays.toString(a).replace(" ", ""))
        .append(",[")
        .append(vars)
        .append("],")
        .append(c)
        .append(");\n");
    fzn.append(optimize ? "solve minimize y0;\n" : "solve satisfy;\n");
    return new Model(fzn.toString(), detectable);
  }

  private static String set(int[] values) {
    return Arrays.stream(values)
        .mapToObj(Integer::toString)
        .collect(Collectors.joining(",", "{", "}"));
  }

  @Test
  void detectedStockingCostKeepsAllSolutions() throws IOException {
    Random random = new Random(5);
    int detected = 0;
    for (int trial = 0; trial < 300; trial++) {
      Model model = randomModel(random, false);
      String out = run(model.fzn(), true, "-a", "-debug");
      boolean found = out.contains("StockingCost");
      detected += found ? 1 : 0;
      if (!model.detectable()) {
        assertFalse(found, "detected, trial " + trial + "\n" + model.fzn());
      }
      assertEquals(
          solutions(run(model.fzn(), false, "-a")),
          solutions(out),
          "trial " + trial + "\n" + model.fzn());
    }
    assertTrue(detected > 100, "detected " + detected);
  }

  @Test
  void detectedStockingCostKeepsOptima() throws IOException {
    Random random = new Random(6);
    for (int trial = 0; trial < 200; trial++) {
      Model model = randomModel(random, true);
      assertEquals(
          optimum(run(model.fzn(), false)),
          optimum(run(model.fzn(), true)),
          "trial " + trial + "\n" + model.fzn());
    }
  }

  @Test
  void predicateIsNotPostedTwice() throws IOException {
    // what the stocking_cost predicate of the MiniZinc library compiles to
    String fzn =
        """
        var 0..4: x0;
        var 0..4: x1;
        var 0..4: x2;
        var 0..20: cost:: output_var;
        array [1..3] of var int: x:: output_array([1..3]) = [x0,x1,x2];
        constraint jacop_alldiff(x);
        constraint int_lin_eq([-1,-2,-1,-1],[x0,x1,x2,cost],-15);
        constraint jacop_stocking_cost(x,[4,4,3],[1,2,1],cost,1);
        solve minimize cost;
        """;
    String out = run(fzn, true, "-debug");
    assertEquals(1, out.split("StockingCost\\d* :", -1).length - 1, out);
    // x1 (cost 2) at 4, x0 at 3, x2 at 2: 0 + 1 + 1
    assertEquals("2", optimum(out));
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    String fzn =
        """
        var 0..4: x0;
        var 0..4: x1;
        var 0..4: x2;
        var 0..20: cost:: output_var;
        array [1..3] of var int: x:: output_array([1..3]) = [x0,x1,x2];
        constraint jacop_alldiff(x);
        constraint int_lin_eq([-1,-1,-1,-1],[x0,x1,x2,cost],-12);
        solve minimize cost;
        """;
    String on = run(fzn, true, "-debug");
    assertTrue(on.contains("StockingCost"), on);
    assertFalse(run(fzn, false, "-debug").contains("StockingCost"));
    assertEquals("3", optimum(on));
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
