/*
 * CountPartnersFlatzincTest.java
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
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The partner constraints of {@link org.jacop.fz.constraints.CountPartnersDetector} keep the
 * solutions and the optima of random models whose counts cannot be one.
 */
class CountPartnersFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.countPartners";

  @TempDir Path tmp;

  /**
   * A random model in the shape of the XCSP3 ButtonsScissors groups: variables x over 0..d, a count
   * of each value (sometimes not of all) that cannot be one (or one or two), stated by the
   * counter's domain or by int_ne, many pairwise disequalities, sometimes an all-different over a
   * few variables, and a few precedences.
   */
  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int n = 7 + random.nextInt(3);
    int d = 2 + random.nextInt(3);
    List<String> names = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      names.add("x" + i);
      int hole = random.nextInt(4) == 0 ? random.nextInt(d + 1) : -1;
      fzn.append("var {")
          .append(
              IntStream.rangeClosed(0, d)
                  .filter(v -> v != hole)
                  .mapToObj(String::valueOf)
                  .collect(Collectors.joining(",")))
          .append("}: x")
          .append(i)
          .append(";\n");
    }
    String list = names.stream().collect(Collectors.joining(",", "[", "]"));
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = ")
        .append(list)
        .append(";\n");
    if (optimise) {
      fzn.append("var 0..").append(d).append(": obj:: output_var;\n");
    }
    StringBuilder decl = new StringBuilder();
    StringBuilder con = new StringBuilder();
    boolean all = random.nextInt(4) != 0;
    for (int v = 0; v <= d; v++) {
      if (!all && random.nextInt(3) == 0) {
        continue;
      }
      int k = random.nextInt(4) == 0 ? 3 : 2;
      boolean byNe = random.nextBoolean() && k == 2;
      String counts =
          IntStream.rangeClosed(0, n)
              .filter(c -> byNe || c == 0 || c >= k)
              .mapToObj(String::valueOf)
              .collect(Collectors.joining(","));
      decl.append("var {").append(counts).append("}: n").append(v).append(";\n");
      con.append("constraint jacop_among(")
          .append(list)
          .append(",")
          .append(v)
          .append("..")
          .append(v)
          .append(",n")
          .append(v)
          .append(");\n");
      if (byNe) {
        con.append("constraint int_ne(n").append(v).append(",1);\n");
      }
    }
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (random.nextInt(10) < 7) {
          con.append(
              random.nextBoolean()
                  ? "constraint int_ne(x" + i + ",x" + j + ");\n"
                  : "constraint int_lin_ne([1,-1],[x" + i + ",x" + j + "],0);\n");
        }
      }
    }
    if (random.nextInt(3) == 0) {
      con.append("constraint jacop_alldiff([x0,x1,x2]);\n");
    }
    for (int p = random.nextInt(3); p > 0; p--) {
      int i = random.nextInt(n);
      int j = random.nextInt(n);
      if (i != j) {
        con.append("constraint int_le(x").append(i).append(",x").append(j).append(");\n");
      }
    }
    fzn.append(decl).append(con);
    if (optimise) {
      fzn.append("constraint jacop_maximum(obj,").append(list).append(");\n");
      fzn.append("solve minimize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  @Test
  void partnersKeepAllSolutions() throws IOException {
    Random random = new Random(41);
    int posted = 0;
    int satisfiable = 0;
    int trials = Integer.getInteger("countPartners.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String debug = run(model, true, "-debug", "-n", "1");
      posted += debug.contains("% count partners") && !debug.contains(" 0 variables with") ? 1 : 0;
      Set<String> expected = solutions(run(model, false, "-a"));
      satisfiable += expected.isEmpty() ? 0 : 1;
      assertEquals(expected, solutions(run(model, true, "-a")), "trial " + trial + "\n" + model);
    }
    assertTrue(posted > trials / 2, "posted " + posted);
    assertTrue(satisfiable > trials / 10, "satisfiable " + satisfiable);
  }

  @Test
  void partnersKeepOptima() throws IOException {
    Random random = new Random(42);
    int trials = Integer.getInteger("countPartners.trials", 300) * 2 / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"), model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on", "-f"), model),
          "trial " + trial + " lcg -f\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "off", "-f"), model),
          "trial " + trial + " cp -f\n" + model);
    }
  }

  private String run(String model, boolean partners, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, Boolean.toString(partners));
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
