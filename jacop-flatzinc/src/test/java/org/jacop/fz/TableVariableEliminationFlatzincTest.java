/*
 * TableVariableEliminationFlatzincTest.java
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
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random models with chains of tables, short tables and elements through auxiliary variables, as
 * MiniZinc writes nested lookups: table variable elimination must keep satisfiability and optima,
 * and the values it gives the eliminated variables must make a solution of the whole model.
 */
class TableVariableEliminationFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.tableElimination";

  private static final String STAR = "99";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> names = new ArrayList<>();
    int main = 3 + random.nextInt(3);
    for (int i = 0; i < main; i++) {
      int hole = random.nextInt(5);
      names.add("x" + i);
      fzn.append("var {")
          .append(
              IntStream.rangeClosed(0, 4)
                  .filter(v -> v != hole)
                  .mapToObj(String::valueOf)
                  .collect(Collectors.joining(",")))
          .append("}: x")
          .append(i)
          .append(";\n");
    }
    List<String> constraints = new ArrayList<>();
    int aux = 0;
    int chains = 1 + random.nextInt(4);
    for (int c = 0; c < chains; c++) {
      String from = "x" + random.nextInt(main);
      String to = "x" + random.nextInt(main);
      int links = 1 + random.nextInt(3);
      String previous = from;
      for (int l = 0; l < links; l++) {
        String next;
        if (l == links - 1 && random.nextInt(3) != 0) {
          next = to;
        } else {
          next = "a" + aux++;
          names.add(next);
          fzn.append("var 0..5: ").append(next).append(";\n");
        }
        constraints.add(link(random, previous, next, "x" + random.nextInt(main)));
        previous = next;
      }
      if (random.nextInt(4) == 0) {
        // an auxiliary variable used a third time, which must stay
        constraints.add("constraint int_ne(" + previous + ",x" + random.nextInt(main) + ")");
      }
    }
    fzn.append("array [1..")
        .append(names.size())
        .append("] of var int: v:: output_array([1..")
        .append(names.size())
        .append("]) = ")
        .append("[" + String.join(",", names) + "]")
        .append(";\n");
    if (optimise) {
      fzn.append("var 0..1000: obj:: output_var;\n");
    }
    if (random.nextBoolean()) {
      constraints.add("constraint int_lin_le([1,1],[x0,x1]," + (3 + random.nextInt(5)) + ")");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      int[] w = IntStream.range(0, main).map(i -> 1 + random.nextInt(5)).toArray();
      int[] a = Arrays.copyOf(w, main + 1);
      a[main] = -1;
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(a).replace(" ", ""))
          .append(",")
          .append(
              IntStream.rangeClosed(0, main)
                  .mapToObj(i -> i < main ? "x" + i : "obj")
                  .collect(Collectors.joining(",", "[", "]")))
          .append(",0);\n");
      fzn.append("solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  // one link of a chain between two variables: a table (binary, or ternary with a third
  // variable), a short table, or an element over a constant array
  private static String link(Random random, String a, String b, String third) {
    int kind = random.nextInt(5);
    if (kind == 0) {
      int[] array = IntStream.range(0, 6).map(i -> random.nextInt(6)).toArray();
      return "constraint array_int_element("
          + a
          + ","
          + Arrays.toString(Arrays.copyOf(array, 5)).replace(" ", "")
          + ","
          + b
          + ")";
    }
    if (kind == 1) {
      int[] array = IntStream.range(0, 6).map(i -> random.nextInt(6)).toArray();
      return "constraint jacop_array_var_int_element_nonshifted("
          + a
          + ","
          + Arrays.toString(array).replace(" ", "")
          + ","
          + b
          + ",0)";
    }
    boolean ternary = kind == 4 && !third.equals(a) && !third.equals(b);
    int arity = ternary ? 3 : 2;
    List<String> rows = new ArrayList<>();
    int count = 3 + random.nextInt(12);
    for (int r = 0; r < count; r++) {
      for (int c = 0; c < arity; c++) {
        rows.add(kind == 3 && random.nextInt(6) == 0 ? STAR : String.valueOf(random.nextInt(6)));
      }
    }
    String scope = ternary ? "[" + a + "," + b + "," + third + "]" : "[" + a + "," + b + "]";
    if (kind == 3) {
      return "constraint jacop_short_table_int("
          + scope
          + ",["
          + String.join(",", rows)
          + "],"
          + STAR
          + ")";
    }
    return "constraint jacop_table_int(" + scope + ",[" + String.join(",", rows) + "])";
  }

  @Test
  void eliminationKeepsSatisfiabilityAndGivesSolutions() throws IOException {
    Random random = new Random(31);
    int eliminated = 0;
    int trials = Integer.getInteger("tableElimination.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String out = run(model, true, "-debug");
      eliminated += out.contains("table variable elimination") ? 1 : 0;
      boolean sat = !out.contains("UNSATISFIABLE");
      assertEquals(
          !run(model, false).contains("UNSATISFIABLE"), sat, "trial " + trial + "\n" + model);
      if (sat) {
        assertSolution(model, out, "trial " + trial);
      }
    }
    assertTrue(eliminated > trials / 3, "eliminated " + eliminated);
  }

  @Test
  void eliminationKeepsOptima() throws IOException {
    Random random = new Random(32);
    int trials = Integer.getInteger("tableElimination.trials", 300) * 2 / 3;
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
    Random random = new Random(33);
    int trials = Integer.getInteger("tableElimination.trials", 300) / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      assertEquals(
          solutions(run(model, false, "-a")),
          solutions(run(model, true, "-a")),
          "trial " + trial + "\n" + model);
    }
  }

  // the last printed solution, fixed in the model, must satisfy it without elimination
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

  private String run(String model, boolean elimination, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (!elimination) {
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
