/*
 * ZeroSumFlatzincTest.java
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random models in the form XCSP3 translations write "x = v implies the sum of some variables is
 * 0": a variable defined by a sum, used in half-reifications at the sum's least value. Zero-sum
 * detection must keep satisfiability, optima and the set of all solutions, and the values it
 * computes for the defined output variables must make a solution of the whole model.
 */
class ZeroSumFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.zeroSum";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> output = new ArrayList<>();
    int n = 4 + random.nextInt(4);
    for (int i = 0; i < n; i++) {
      // some terms do not start at 0, and some are negative, so the least value is not always 0
      int kind = random.nextInt(6);
      String domain = kind == 0 ? "1..3" : kind == 1 ? "-2..0" : kind == 2 ? "0..1" : "0..2";
      fzn.append("var ").append(domain).append(": x").append(i).append(";\n");
      output.add("x" + i);
    }
    List<String> constraints = new ArrayList<>();
    List<String> literals = new ArrayList<>();
    int sums = 1 + random.nextInt(4);
    for (int s = 0; s < sums; s++) {
      List<String> terms = new ArrayList<>();
      List<Integer> weights = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        if (random.nextInt(3) == 0) {
          terms.add("x" + i);
          weights.add(random.nextInt(4) == 0 ? -1 - random.nextInt(2) : 1 + random.nextInt(2));
        }
      }
      if (terms.size() < 2) {
        continue;
      }
      long least = 0;
      long most = 0;
      for (int k = 0; k < terms.size(); k++) {
        int[] bounds = bounds(fzn.toString(), terms.get(k));
        int w = weights.get(k);
        least += Math.min(w * bounds[0], w * bounds[1]);
        most += Math.max(w * bounds[0], w * bounds[1]);
      }
      String name = "s" + s;
      fzn.append("var ").append(least).append("..").append(most).append(": ").append(name);
      fzn.append(random.nextBoolean() ? ":: output_var" : "").append(";\n");
      if (random.nextInt(3) != 0) {
        output.add(name);
      }
      // the defined variable first or last, with the weights negated half of the time
      int sign = random.nextBoolean() ? 1 : -1;
      List<String> vars = new ArrayList<>(terms);
      List<Integer> a = new ArrayList<>();
      weights.forEach(w -> a.add(sign * w));
      vars.add(random.nextInt(vars.size() + 1), name);
      a.add(vars.indexOf(name), -sign);
      constraints.add(
          "constraint int_lin_eq("
              + a.toString().replace(" ", "")
              + ","
              + vars.toString().replace(" ", "")
              + ",0)");
      int uses = 1 + random.nextInt(2);
      for (int u = 0; u < uses; u++) {
        String b = "b" + s + "_" + u;
        fzn.append("var bool: ").append(b).append(";\n");
        String imp = random.nextBoolean() ? "int_eq_imp" : "int_le_imp";
        // mostly at the least value; sometimes above it, which must not be rewritten
        long value = random.nextInt(5) == 0 ? least + 1 : least;
        constraints.add("constraint " + imp + "(" + name + "," + value + "," + b + ")");
        // b is wanted by the literal x = v of a variable, as or(ne(x, v), eq(s, 0)) flattens
        int x = random.nextInt(n);
        int[] bounds = bounds(fzn.toString(), "x" + x);
        int v = bounds[0] + random.nextInt(bounds[1] - bounds[0] + 1);
        String r = "r" + s + "_" + u;
        fzn.append("var bool: ").append(r).append(";\n");
        constraints.add("constraint int_eq_reif(x" + x + "," + v + "," + r + ")");
        constraints.add("constraint bool_clause([" + b + "],[" + r + "])");
        literals.add(r);
      }
      if (random.nextInt(5) == 0) {
        // the defined variable is used elsewhere, which must keep it as it is
        constraints.add("constraint int_ne(" + name + "," + (least + random.nextInt(3)) + ")");
      }
    }
    fzn.append("array [1..")
        .append(output.size())
        .append("] of var int: v:: output_array([1..")
        .append(output.size())
        .append("]) = ")
        .append(output.toString().replace(" ", ""))
        .append(";\n");
    if (optimise) {
      fzn.append("var 0..100: obj:: output_var;\n");
    }
    List<String> ints = new ArrayList<>();
    for (String r : optimise ? literals : List.<String>of()) {
      fzn.append("var 0..1: i").append(r).append(";\n");
      constraints.add("constraint bool2int(" + r + ",i" + r + ")");
      ints.add("i" + r);
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise && !literals.isEmpty()) {
      int[] w = new int[ints.size() + 1];
      Arrays.fill(w, 1);
      w[ints.size()] = -1;
      ints.add("obj");
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(w).replace(" ", ""))
          .append(",")
          .append(ints.toString().replace(" ", ""))
          .append(",0);\n");
      fzn.append("solve maximize obj;\n");
    } else if (optimise) {
      fzn.append("constraint int_eq(obj,0);\nsolve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  // the bounds of a variable declared as "var lo..hi: name;"
  private static int[] bounds(String fzn, String name) {
    Matcher m = Pattern.compile("var (-?\\d+)\\.\\.(-?\\d+): " + name + ";").matcher(fzn);
    assertTrue(m.find(), name);
    return new int[] {Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2))};
  }

  @Test
  void detectionKeepsSatisfiabilityAndGivesSolutions() throws IOException {
    Random random = new Random(41);
    int fired = 0;
    int trials = Integer.getInteger("zeroSum.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String out = run(model, true, "--search-statistics");
      fired += out.contains("zeroSums=") ? 1 : 0;
      boolean sat = !out.contains("UNSATISFIABLE");
      assertEquals(
          !run(model, false).contains("UNSATISFIABLE"), sat, "trial " + trial + "\n" + model);
      if (sat) {
        assertSolution(model, out, "trial " + trial);
      }
    }
    assertTrue(fired > trials / 5, "fired " + fired);
  }

  @Test
  void detectionKeepsOptima() throws IOException {
    Random random = new Random(42);
    int trials = Integer.getInteger("zeroSum.trials", 300) * 2 / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"));
      for (String[] options :
          List.of(
              new String[] {"--lcg", "off"}, new String[] {"--lcg", "on"}, new String[] {"-f"})) {
        String out = run(model, true, options);
        assertEquals(
            expected,
            optimum(out),
            "trial " + trial + " " + Arrays.toString(options) + "\n" + model);
        if (!"UNSATISFIABLE".equals(expected)) {
          assertSolution(model, out, "trial " + trial + " " + Arrays.toString(options));
        }
      }
    }
  }

  @Test
  void allSolutionsAreUnchanged() throws IOException {
    Random random = new Random(43);
    int trials = Integer.getInteger("zeroSum.trials", 300) / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      assertEquals(
          solutions(run(model, false, "-a")),
          solutions(run(model, true, "-a")),
          "trial " + trial + "\n" + model);
    }
  }

  // the last printed solution, fixed in the model, must satisfy it without the detection
  private void assertSolution(String model, String out, String message) throws IOException {
    String[] parts = out.split("----------");
    assertTrue(parts.length >= 2, message + "\n" + out);
    Matcher m =
        Pattern.compile("v = array1d\\(1\\.\\.\\d+, \\[([^\\]]*)\\]\\);")
            .matcher(parts[parts.length - 2]);
    assertTrue(m.find(), message + "\n" + out);
    String[] values = m.group(1).split(", ");
    Matcher decl =
        Pattern.compile("output_array\\(\\[1\\.\\.\\d+\\]\\) = \\[([^\\]]*)\\]").matcher(model);
    assertTrue(decl.find());
    String[] vars = decl.group(1).split(",");
    StringBuilder fixed = new StringBuilder();
    for (int i = 0; i < vars.length; i++) {
      fixed
          .append("constraint int_eq(")
          .append(vars[i])
          .append(",")
          .append(values[i])
          .append(");\n");
    }
    String check = model.replaceFirst("solve ", fixed.toString().replace("$", "\\$") + "solve ");
    String result = run(check, false, "--lcg", "off");
    assertTrue(
        result.contains("----------") && !result.contains("UNSATISFIABLE"),
        message + ": not a solution\n" + out + "\n" + model);
  }

  private String run(String model, boolean detection, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
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
