/*
 * LinearIndexElementFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks {@link org.jacop.fz.constraints.LinearIndexElementDetector}: elements over constant arrays
 * whose index a linear equality defines from a few variables keep their solutions and optima when
 * they become one table.
 */
class LinearIndexElementFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.linearIndexElement";

  @TempDir Path tmp;

  /**
   * A random model: two or three variables with holes, an index defined by int_lin_eq with the
   * index at a random position and coefficient +-1 (sometimes with the domain annotation, sometimes
   * with a hole in the index domain), one to three elements of the kinds the front end reads over
   * arrays shorter or longer than the index range, some sharing a value variable, and sometimes a
   * constraint that reads the index too, so that the detection must leave it.
   */
  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> output = new ArrayList<>();
    List<String> constraints = new ArrayList<>();
    int terms = 2 + random.nextInt(2);
    String[] xs = new String[terms];
    int[] coefficients = new int[terms];
    long lo = 0;
    long hi = 0;
    for (int t = 0; t < terms; t++) {
      xs[t] = "x" + t;
      int a = 1 + random.nextInt(3);
      int b = a + 1 + random.nextInt(3);
      fzn.append("var ").append(domain(a, b, a + 1)).append(": ").append(xs[t]).append(";\n");
      output.add(xs[t]);
      coefficients[t] = (random.nextBoolean() ? 1 : -1) * (1 + random.nextInt(4));
      lo += Math.min(coefficients[t] * a, coefficients[t] * b);
      hi += Math.max(coefficients[t] * a, coefficients[t] * b);
    }
    int shift = random.nextInt(5) - 2;
    long iLo = lo + shift;
    long iHi = hi + shift;
    String indexDomain =
        random.nextInt(3) == 0 ? domain((int) iLo, (int) iHi, (int) iLo + 1) : iLo + ".." + iHi;
    fzn.append("var ").append(indexDomain).append(": i;\n");
    // i = sum c_t x_t + shift, as sum c_t x_t + sign * (-i) * ... with the index at position p
    int sign = random.nextBoolean() ? 1 : -1;
    int position = random.nextInt(terms + 1);
    List<String> vars = new ArrayList<>(Arrays.asList(xs));
    List<Integer> as = new ArrayList<>();
    for (int c : coefficients) {
      as.add(sign * c);
    }
    vars.add(position, "i");
    as.add(position, -sign);
    constraints.add(
        "constraint int_lin_eq("
            + as.stream().map(String::valueOf).collect(Collectors.joining(",", "[", "]"))
            + ","
            + String.join(",", vars).transform(s -> "[" + s + "]")
            + ","
            + (-sign * shift)
            + ")"
            + (random.nextBoolean() ? ":: domain" : ""));
    int elements = 1 + random.nextInt(3);
    List<String> values = new ArrayList<>();
    for (int e = 0; e < elements; e++) {
      String value;
      if (!values.isEmpty() && random.nextInt(4) == 0) {
        value = values.get(random.nextInt(values.size()));
      } else {
        value = "v" + values.size();
        fzn.append("var 0..6: ").append(value).append(";\n");
        output.add(value);
        values.add(value);
      }
      int first = (int) iLo + random.nextInt(3) - 1;
      int n = (int) (iHi - iLo) + random.nextInt(3) - 1;
      StringBuilder array = new StringBuilder("[");
      for (int k = 0; k < Math.max(1, n); k++) {
        array.append(k > 0 ? "," : "").append(random.nextInt(7));
      }
      array.append("]");
      String name =
          switch (random.nextInt(3)) {
            case 0 -> "jacop_array_var_int_element_nonshifted";
            case 1 -> "array_var_int_element";
            default -> "array_int_element";
          };
      if (name.equals("jacop_array_var_int_element_nonshifted")) {
        constraints.add("constraint " + name + "(i," + array + "," + value + "," + first + ")");
      } else {
        // these start at 1: shift the index into the array by the definition
        constraints.add("constraint " + name + "(i," + array + "," + value + ")");
      }
    }
    if (random.nextInt(5) == 0) {
      constraints.add("constraint int_ne(i," + (iLo + 2) + ")");
    }
    String all = String.join(",", output);
    fzn.append("array [1..")
        .append(output.size())
        .append("] of var int: x:: output_array([1..")
        .append(output.size())
        .append("]) = [")
        .append(all)
        .append("];\n");
    if (optimise) {
      fzn.append("var -100..100: obj:: output_var;\n");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      StringBuilder w = new StringBuilder("[");
      StringBuilder v = new StringBuilder("[");
      for (String s : output) {
        w.append(random.nextInt(7) - 3).append(",");
        v.append(s).append(",");
      }
      w.append("-1]");
      v.append("obj]");
      fzn.append("constraint int_lin_eq(").append(w).append(",").append(v).append(",0);\n");
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
        + java.util.stream.IntStream.rangeClosed(lo, hi)
            .filter(v -> v != hole)
            .mapToObj(String::valueOf)
            .collect(Collectors.joining(","))
        + "}";
  }

  @Test
  void tablesKeepAllSolutions() throws IOException {
    Random random = new Random(21);
    int tabled = 0;
    for (int trial = 0; trial < 300; trial++) {
      String model = randomModel(random, false);
      String out = run(model, true, "-a", "-debug");
      tabled += out.contains("linear index element detector") ? 1 : 0;
      assertEquals(
          solutions(run(model, false, "-a")), solutions(out), "trial " + trial + "\n" + model);
    }
    assertTrue(tabled > 90, "tabled " + tabled);
  }

  @Test
  void tablesKeepOptimaUnderLcg() throws IOException {
    Random random = new Random(22);
    int tabled = 0;
    for (int trial = 0; trial < 150; trial++) {
      String model = randomModel(random, true);
      String out = run(model, true, "--lcg", "on", "-debug");
      tabled += out.contains("linear index element detector") ? 1 : 0;
      String reference = optimum(run(model, false, "--lcg", "off"));
      assertEquals(reference, optimum(out), "trial " + trial + "\n" + model);
      assertEquals(
          reference,
          optimum(run(model, true, "--lcg", "on", "-f")),
          "trial " + trial + " -f\n" + model);
    }
    assertTrue(tabled > 50, "tabled " + tabled);
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
