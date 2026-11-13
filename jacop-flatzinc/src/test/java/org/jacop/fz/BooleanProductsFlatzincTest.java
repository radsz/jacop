/*
 * BooleanProductsFlatzincTest.java
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
import java.util.Arrays;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/** Products with a 0/1 factor written as linear constraints keep the solutions and the optima. */
class BooleanProductsFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.booleanProducts";

  @TempDir Path tmp;

  /**
   * A random model: products z = x * b with x over a domain with holes and sometimes negative
   * values, b a bool (through bool2int) or a 0..1 variable, factors in either order, and a linear
   * constraint over the products and x.
   */
  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int n = 2 + random.nextInt(2);
    StringBuilder out = new StringBuilder();
    for (int i = 0; i < n; i++) {
      int lo = random.nextInt(4) - 2;
      int hole = lo + 1 + random.nextInt(2);
      fzn.append("var {");
      StringBuilder dom = new StringBuilder();
      for (int v = lo; v <= lo + 3; v++) {
        if (v != hole) {
          dom.append(dom.length() == 0 ? "" : ",").append(v);
        }
      }
      fzn.append(dom).append("}: x").append(i).append(";\n");
      if (random.nextBoolean()) {
        fzn.append("var bool: c").append(i).append(";\n");
        fzn.append("var 0..1: b").append(i).append(";\n");
      } else {
        fzn.append("var 0..1: b").append(i).append(";\n");
      }
      fzn.append("var -10..10: z").append(i).append(";\n");
      out.append(out.length() == 0 ? "" : ",")
          .append("x")
          .append(i)
          .append(",b")
          .append(i)
          .append(",z")
          .append(i);
    }
    if (optimise) {
      fzn.append("var -100..100: obj:: output_var;\n");
    }
    fzn.append("array [1..")
        .append(3 * n)
        .append("] of var int: v:: output_array([1..")
        .append(3 * n)
        .append("]) = [")
        .append(out)
        .append("];\n");
    for (int i = 0; i < n; i++) {
      if (fzn.indexOf("var bool: c" + i + ";") >= 0) {
        fzn.append("constraint bool2int(c").append(i).append(",b").append(i).append(");\n");
      }
      if (random.nextBoolean()) {
        fzn.append("constraint int_times(x")
            .append(i)
            .append(",b")
            .append(i)
            .append(",z")
            .append(i)
            .append(");\n");
      } else {
        fzn.append("constraint int_times(b")
            .append(i)
            .append(",x")
            .append(i)
            .append(",z")
            .append(i)
            .append(");\n");
      }
    }
    StringBuilder coefficients = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (int i = 0; i < n; i++) {
      coefficients
          .append(i == 0 ? "" : ",")
          .append(random.nextInt(5) - 2)
          .append(",")
          .append(random.nextInt(3) - 1);
      vars.append(i == 0 ? "" : ",").append("z").append(i).append(",x").append(i);
    }
    fzn.append("constraint int_lin_le([")
        .append(coefficients)
        .append("],[")
        .append(vars)
        .append("],")
        .append(random.nextInt(7) - 2)
        .append(");\n");
    if (optimise) {
      fzn.append("constraint int_lin_eq([");
      StringBuilder w = new StringBuilder();
      StringBuilder zs = new StringBuilder();
      for (int i = 0; i < n; i++) {
        w.append(random.nextInt(5) - 2).append(",");
        zs.append("z").append(i).append(",");
      }
      fzn.append(w).append("-1],[").append(zs).append("obj],0);\n");
      fzn.append("solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  @Test
  void productsKeepAllSolutions() throws IOException {
    Random random = new Random(41);
    int trials = Integer.getInteger("booleanProducts.trials", 200);
    int rewritten = 0;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      rewritten += run(model, true, "-debug").contains("% boolean product") ? 1 : 0;
      assertEquals(
          solutions(run(model, false, "-a")),
          solutions(run(model, true, "-a")),
          "trial " + trial + "\n" + model);
    }
    assertTrue(rewritten > trials / 2, "rewritten " + rewritten);
  }

  @Test
  void productsKeepOptima() throws IOException {
    Random random = new Random(42);
    int trials = Integer.getInteger("booleanProducts.trials", 200) / 2;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"), model);
      assertEquals(expected, optimum(run(model, true, "--lcg", "on"), model), "lcg " + model);
      assertEquals(expected, optimum(run(model, true, "--lcg", "on", "-f"), model), "-f " + model);
      assertEquals(expected, optimum(run(model, true, "--lcg", "off"), model), "cp " + model);
    }
  }

  private String run(String model, boolean products, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, Boolean.toString(products));
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
  private static String optimum(String out, String model) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out + "\n" + model);
    return last;
  }
}
