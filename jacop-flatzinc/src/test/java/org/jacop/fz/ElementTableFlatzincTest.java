/*
 * ElementTableFlatzincTest.java
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
 * Element constraints over constant arrays that share an index become one table ({@code
 * ElementTableDetector}): the merged model must keep every solution and every optimum, with and
 * without LCG, whose explanations of the table replace those of the elements.
 */
class ElementTableFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.elementTable";

  @TempDir Path tmp;

  /**
   * A random model: index variables with holes, and per index two to four elements of the kinds the
   * front end reads (array_int_element, array_var_int_element with constant entries, the nonshifted
   * form with another first index, array_bool_element), some sharing a value variable, one possibly
   * using the index itself or a constant as the value.
   */
  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> output = new ArrayList<>();
    List<String> constraints = new ArrayList<>();
    List<String> objective = new ArrayList<>();
    int indices = 1 + random.nextInt(2);
    int values = 0;
    for (int g = 0; g < indices; g++) {
      int n = 3 + random.nextInt(6);
      int first = random.nextInt(3) - 1;
      String index = "i" + g;
      // the index domain overlaps the arrays' range and has a hole
      int lo = first - random.nextInt(2);
      int hi = first + n - 1 + random.nextInt(2);
      int hole = lo + 1 + random.nextInt(Math.max(1, hi - lo - 1));
      fzn.append("var ").append(domain(lo, hi, hole)).append(": ").append(index).append(";\n");
      output.add(index);
      int elements = 2 + random.nextInt(3);
      List<String> ints = new ArrayList<>();
      List<String> bools = new ArrayList<>();
      for (int e = 0; e < elements; e++) {
        boolean bool = random.nextInt(5) == 0;
        List<String> mine = bool ? bools : ints;
        String value;
        if (!mine.isEmpty() && random.nextInt(4) == 0) {
          value = mine.get(random.nextInt(mine.size()));
        } else if (!bool && random.nextInt(8) == 0) {
          value = index;
        } else if (random.nextInt(10) == 0) {
          value = bool ? "true" : String.valueOf(random.nextInt(4));
        } else {
          value = (bool ? "b" : "v") + values++;
          fzn.append(bool ? "var bool: " : "var 0..4: ").append(value).append(";\n");
          output.add(value);
          mine.add(value);
          if (!bool) {
            objective.add(value);
          }
        }
        constraints.add(element(random, bool, index, n, first, value));
      }
    }
    String vars =
        output.stream().filter(s -> !s.startsWith("b")).collect(Collectors.joining(",", "[", "]"));
    String bools =
        output.stream().filter(s -> s.startsWith("b")).collect(Collectors.joining(",", "[", "]"));
    fzn.append("array [1..")
        .append(vars.split(",").length)
        .append("] of var int: x:: output_array([1..")
        .append(vars.split(",").length)
        .append("]) = ")
        .append(vars)
        .append(";\n");
    if (bools.length() > 2) {
      fzn.append("array [1..")
          .append(bools.split(",").length)
          .append("] of var bool: bs:: output_array([1..")
          .append(bools.split(",").length)
          .append("]) = ")
          .append(bools)
          .append(";\n");
    }
    if (optimise) {
      fzn.append("var 0..1000: obj:: output_var;\n");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      int[] w = IntStream.range(0, objective.size()).map(i -> 1 + random.nextInt(5)).toArray();
      int[] a = Arrays.copyOf(w, w.length + 1);
      a[w.length] = -1;
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(a).replace(" ", ""))
          .append(",")
          .append(
              IntStream.range(0, objective.size() + 1)
                  .mapToObj(i -> i < objective.size() ? objective.get(i) : "obj")
                  .collect(Collectors.joining(",", "[", "]")))
          .append(",0);\n");
      fzn.append("solve :: int_search(x,input_order,indomain_min,complete) maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  private static String domain(int lo, int hi, int hole) {
    if (hole <= lo || hole >= hi) {
      return lo + ".." + hi;
    }
    return "{"
        + IntStream.rangeClosed(lo, hi)
            .filter(v -> v != hole)
            .mapToObj(String::valueOf)
            .collect(Collectors.joining(","))
        + "}";
  }

  private static String element(
      Random random, boolean bool, String index, int n, int first, String value) {
    String array =
        IntStream.range(0, n)
            .mapToObj(
                k ->
                    bool ? String.valueOf(random.nextBoolean()) : String.valueOf(random.nextInt(5)))
            .collect(Collectors.joining(",", "[", "]"));
    if (bool) {
      return first == 1
          ? "constraint array_bool_element(" + index + "," + array + "," + value + ")"
          : "constraint jacop_array_var_bool_element_nonshifted("
              + index
              + ","
              + array
              + ","
              + value
              + ","
              + first
              + ")";
    }
    return switch (first == 1 ? random.nextInt(2) : 2) {
      case 0 -> "constraint array_int_element(" + index + "," + array + "," + value + ")";
      case 1 -> "constraint array_var_int_element(" + index + "," + array + "," + value + ")";
      default ->
          "constraint jacop_array_var_int_element_nonshifted("
              + index
              + ","
              + array
              + ","
              + value
              + ","
              + first
              + ")";
    };
  }

  @Test
  void mergedElementsKeepAllSolutions() throws IOException {
    Random random = new Random(11);
    int merged = 0;
    for (int trial = 0; trial < 300; trial++) {
      String model = randomModel(random, false);
      String out = run(model, true, "-a", "-debug");
      merged += out.contains("element table detector") ? 1 : 0;
      assertEquals(
          solutions(run(model, false, "-a")), solutions(out), "trial " + trial + "\n" + model);
    }
    assertTrue(merged > 150, "merged " + merged);
  }

  @Test
  void mergedElementsKeepOptimaUnderLcg() throws IOException {
    Random random = new Random(12);
    int merged = 0;
    for (int trial = 0; trial < 200; trial++) {
      String model = randomModel(random, true);
      String out = run(model, true, "--lcg", "on", "-debug");
      merged += out.contains("element table detector") ? 1 : 0;
      assertEquals(
          optimum(run(model, false, "--lcg", "off")),
          optimum(out),
          "trial " + trial + "\n" + model);
      assertEquals(
          optimum(run(model, false, "--lcg", "off")),
          optimum(run(model, true, "--lcg", "on", "-f")),
          "trial " + trial + " -f\n" + model);
    }
    assertTrue(merged > 100, "merged " + merged);
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
