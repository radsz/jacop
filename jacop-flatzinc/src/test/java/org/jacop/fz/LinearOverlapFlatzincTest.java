/*
 * LinearOverlapFlatzincTest.java
 * <p>
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
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/** Linear overlap factoring keeps the solutions and the optima of random models. */
class LinearOverlapFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.linearOverlap";

  private static final String[] RELATIONS = {"eq", "le", "ne"};

  @TempDir Path tmp;

  /**
   * A random model over a few variables with holes: linear constraints that contain a common
   * sub-sum times a random factor (sometimes negative, sometimes with one coefficient changed so
   * the overlap breaks), plus other terms, a repeated variable or a constant; some are reified or
   * half-reified.
   */
  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int nv = 6 + random.nextInt(3);
    List<String> names = new ArrayList<>();
    for (int i = 0; i < nv; i++) {
      String x = "x" + i;
      names.add(x);
      int hole = 1 + random.nextInt(2);
      fzn.append("var {")
          .append(
              IntStream.rangeClosed(0, 3)
                  .filter(v -> v != hole)
                  .mapToObj(String::valueOf)
                  .collect(Collectors.joining(",")))
          .append("}: ")
          .append(x)
          .append(";\n");
    }
    fzn.append("var bool: b0;\nvar bool: b1;\n");
    fzn.append("array [1..")
        .append(nv)
        .append("] of var int: x:: output_array([1..")
        .append(nv)
        .append("]) = ")
        .append(names.stream().collect(Collectors.joining(",", "[", "]")))
        .append(";\n");
    if (optimise) {
      fzn.append("var -1000..1000: obj:: output_var;\n");
    }
    List<Integer> all = new ArrayList<>(IntStream.range(0, nv).boxed().toList());
    Collections.shuffle(all, random);
    List<Integer> common = all.subList(0, 4 + random.nextInt(2));
    int[] base = common.stream().mapToInt(i -> 1 + random.nextInt(3)).toArray();
    int rows = 2 + random.nextInt(3);
    for (int r = 0; r < rows; r++) {
      int k = (1 + random.nextInt(2)) * (random.nextBoolean() ? 1 : -1);
      List<String> vars = new ArrayList<>();
      List<Integer> coefficients = new ArrayList<>();
      int sum = 0;
      for (int t = 0; t < common.size(); t++) {
        vars.add("x" + common.get(t));
        int c = k * base[t];
        if (random.nextInt(10) == 0) {
          c += 1;
        }
        coefficients.add(c);
        sum += Math.abs(c) * 3;
      }
      for (int i : all) {
        if (!common.contains(i) && random.nextInt(3) == 0) {
          vars.add("x" + i);
          coefficients.add(random.nextInt(5) - 2);
        }
      }
      if (random.nextInt(5) == 0) {
        vars.add(vars.get(0));
        coefficients.add(1);
      }
      if (random.nextInt(5) == 0) {
        vars.add("2");
        coefficients.add(1);
      }
      String relation = RELATIONS[random.nextInt(r == 0 ? 2 : 3)];
      int rhs = random.nextInt(sum + 1) - sum / 2;
      int form = random.nextInt(4);
      String suffix = form == 0 ? "_reif" : form == 1 ? "_imp" : "";
      fzn.append("constraint int_lin_")
          .append(relation)
          .append(suffix)
          .append("(")
          .append(coefficients.toString().replace(" ", ""))
          .append(",")
          .append(vars.toString().replace(" ", ""))
          .append(",")
          .append(rhs)
          .append(suffix.isEmpty() ? "" : ",b" + random.nextInt(2))
          .append(");\n");
    }
    if (optimise) {
      int[] w = IntStream.range(0, nv).map(i -> random.nextInt(7) - 3).toArray();
      int[] a = Arrays.copyOf(w, nv + 1);
      a[nv] = -1;
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(a).replace(" ", ""))
          .append(",")
          .append(
              IntStream.rangeClosed(0, nv)
                  .mapToObj(i -> i < nv ? "x" + i : "obj")
                  .collect(Collectors.joining(",", "[", "]")))
          .append(",0);\n");
      fzn.append("solve :: int_search(x,input_order,indomain_min,complete) maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  @Test
  void factoredRowsKeepAllSolutions() throws IOException {
    Random random = new Random(31);
    int factored = 0;
    int trials = Integer.getInteger("linearOverlap.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      factored += run(model, true, "-debug").contains("% linear overlap") ? 1 : 0;
      assertEquals(
          solutions(run(model, false, "-a")),
          solutions(run(model, true, "-a")),
          "trial " + trial + "\n" + model);
    }
    assertTrue(factored > trials / 2, "factored " + factored);
  }

  @Test
  void factoredRowsKeepOptimaUnderLcg() throws IOException {
    Random random = new Random(32);
    int trials = Integer.getInteger("linearOverlap.trials", 300) * 2 / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"), model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on"), model),
          "trial " + trial + "\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on", "-f"), model),
          "trial " + trial + " -f\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "off"), model),
          "trial " + trial + " cp\n" + model);
    }
  }

  private String run(String model, boolean factoring, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, Boolean.toString(factoring));
    System.setProperty(PROPERTY + ".reified", "true");
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
      System.clearProperty(PROPERTY + ".reified");
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
