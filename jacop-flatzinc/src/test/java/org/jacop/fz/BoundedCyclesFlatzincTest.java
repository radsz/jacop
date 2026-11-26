/*
 * BoundedCyclesFlatzincTest.java
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
 * Checks the cycle formulation that {@link org.jacop.fz.constraints.CircuitCostDetector} adds to a
 * permutation whose cycle labels are packed into bins of capacity K (the kidney-exchange model of
 * the 2019 MiniZinc Challenge): the optima and the solutions stay those without it.
 */
class BoundedCyclesFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.boundedCycles";

  @TempDir Path tmp;

  /**
   * A random kidney-exchange model: n vertices, successors over the allowed arcs and the vertex
   * itself, labels equal along every arc, at most K vertices per label, and the sum of the arc
   * weights (zero on the vertex itself) maximised, minimised or only constrained.
   */
  private static String randomModel(Random random, int goal) {
    int n = 4 + random.nextInt(4);
    int k = 2 + random.nextInt(2);
    StringBuilder fzn = new StringBuilder();
    List<String> constraints = new ArrayList<>();
    String succ = IntStream.range(0, n).mapToObj(i -> "s" + i).collect(Collectors.joining(","));
    String labels = IntStream.range(0, n).mapToObj(i -> "l" + i).collect(Collectors.joining(","));
    for (int i = 0; i < n; i++) {
      List<String> values = new ArrayList<>();
      StringBuilder weights = new StringBuilder("[");
      for (int j = 0; j < n; j++) {
        boolean arc = i == j || random.nextInt(10) < 6;
        int w = i == j ? 0 : arc ? random.nextInt(20) - 4 : 0;
        if (arc) {
          values.add(String.valueOf(j + 1));
        }
        weights.append(j > 0 ? "," : "").append(w);
      }
      weights.append("]");
      fzn.append("var {").append(String.join(",", values)).append("}: s").append(i).append(";\n");
      fzn.append("var 1..").append(n).append(": l").append(i).append(";\n");
      fzn.append("var -100..100: c").append(i).append(";\n");
      constraints.add(
          "constraint jacop_array_var_int_element_nonshifted(s"
              + i
              + ",["
              + labels
              + "],l"
              + i
              + ",1)");
      constraints.add(
          "constraint jacop_array_var_int_element_nonshifted(s"
              + i
              + ","
              + weights
              + ",c"
              + i
              + ",1)");
    }
    fzn.append("var -1000..1000: obj:: output_var;\n");
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: succ:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(succ)
        .append("];\n");
    constraints.add("constraint jacop_alldiff([" + succ + "])");
    String ks =
        IntStream.range(0, n).mapToObj(i -> String.valueOf(k)).collect(Collectors.joining(","));
    String ones = IntStream.range(0, n).mapToObj(i -> "1").collect(Collectors.joining(","));
    constraints.add(
        "constraint jacop_bin_packing_capacity([" + labels + "],[" + ks + "],[" + ones + "],1)");
    String costs = IntStream.range(0, n).mapToObj(i -> "c" + i).collect(Collectors.joining(","));
    constraints.add(
        "constraint int_lin_eq(["
            + IntStream.range(0, n).mapToObj(i -> "1").collect(Collectors.joining(","))
            + ",-1],["
            + costs
            + ",obj],0)");
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    String search = ":: int_search(succ,input_order,indomain_min,complete)";
    fzn.append("solve ")
        .append(search)
        .append(
            switch (goal) {
              case 0 -> " maximize obj;\n";
              case 1 -> " minimize obj;\n";
              default -> " satisfy;\n";
            });
    return fzn.toString();
  }

  @Test
  void cyclesKeepOptima() throws IOException {
    Random random = new Random(31);
    int posted = 0;
    for (int trial = 0; trial < 150; trial++) {
      String model = randomModel(random, trial % 2);
      String out = run(model, true, "-debug");
      posted += out.contains("bounded cycles") ? 1 : 0;
      String reference = optimum(run(model, false, "--lcg", "off"));
      assertEquals(reference, optimum(out), "trial " + trial + "\n" + model);
      assertEquals(
          reference,
          optimum(run(model, true, "--lcg", "off")),
          "trial " + trial + " no lcg\n" + model);
      assertEquals(reference, optimum(run(model, true, "-f")), "trial " + trial + " -f\n" + model);
    }
    assertTrue(posted > 100, "posted " + posted);
  }

  @Test
  void cyclesKeepAllSolutions() throws IOException {
    Random random = new Random(32);
    for (int trial = 0; trial < 100; trial++) {
      String model = randomModel(random, 2);
      assertEquals(
          solutions(run(model, false, "-a", "--lcg", "off")),
          solutions(run(model, true, "-a", "--lcg", "off")),
          "trial " + trial + "\n" + model);
    }
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
