/*
 * TspRoutesFlatzincTest.java
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
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the opt-in travelling salesman mode (org.jacop.fz.tsp): a circuit without fixed successors
 * whose cost is a sum of arc costs gets a redundant Routes from its first node with arc and cost
 * rows, so that the linear relaxation separates subtour, blossom and comb cuts. The solutions and
 * the optimum with the mode must be those without it.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class TspRoutesFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.tsp";

  @TempDir Path tmp;

  @AfterEach
  void modeDefault() {
    System.clearProperty(PROPERTY);
  }

  // a circuit over n cities with random, possibly asymmetric, distances, some arcs left out, and
  // either a budget on the length (all solutions) or the length minimized
  private static String randomModel(Random random, boolean optimize) {
    int n = 5 + random.nextInt(3);
    boolean symmetric = random.nextBoolean();
    int[][] d = new int[n + 1][n + 1];
    for (int i = 1; i <= n; i++) {
      for (int j = 1; j <= n; j++) {
        if (i != j) {
          d[i][j] = symmetric && j < i ? d[j][i] : 1 + random.nextInt(20);
        }
      }
    }
    StringBuilder f = new StringBuilder();
    StringBuilder succ = new StringBuilder();
    StringBuilder ds = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      StringBuilder values = new StringBuilder();
      for (int j = 1; j <= n; j++) {
        if (j != i && random.nextInt(6) > 0) {
          values.append(values.isEmpty() ? "" : ",").append(j);
        }
      }
      if (values.isEmpty()) {
        values.append(i % n + 1);
      }
      f.append("var {").append(values).append("}: s").append(i).append(";\n");
      StringBuilder row = new StringBuilder();
      for (int j = 1; j <= n; j++) {
        row.append(j == 1 ? "" : ",").append(d[i][j]);
      }
      f.append("array [1..").append(n).append("] of int: c").append(i).append(" = [");
      f.append(row).append("];\n");
      f.append("var 0..20: d").append(i).append(";\n");
      succ.append(succ.isEmpty() ? "" : ",").append('s').append(i);
      ds.append(ds.isEmpty() ? "" : ",").append('d').append(i);
    }
    f.append("array [1..")
        .append(n)
        .append("] of var int: succ:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(succ)
        .append("];\n");
    f.append("var 0..").append(20 * n).append(": len:: output_var;\n");
    f.append("constraint jacop_circuit(succ);\n");
    for (int i = 1; i <= n; i++) {
      f.append("constraint jacop_array_var_int_element_nonshifted(s")
          .append(i)
          .append(",c")
          .append(i)
          .append(",d")
          .append(i)
          .append(",1);\n");
    }
    int[] ones = new int[n + 1];
    Arrays.fill(ones, 1);
    ones[n] = -1;
    f.append("constraint int_lin_eq(")
        .append(Arrays.toString(ones).replace(" ", ""))
        .append(",[")
        .append(ds)
        .append(",len],0);\n");
    if (optimize) {
      f.append("solve minimize len;\n");
    } else {
      f.append("constraint int_lin_le([1],[len],").append(8 * n).append(");\n");
      f.append("solve satisfy;\n");
    }
    return f.toString();
  }

  @Test
  @Timeout(120)
  void tspRoutesKeepAllSolutions() throws IOException {
    Random random = new Random(11);
    int detected = 0;
    int solved = 0;
    for (int trial = 0; trial < 30; trial++) {
      String model = randomModel(random, false);
      Set<String> without = solutions(run(model, "-a"));
      System.setProperty(PROPERTY, "true");
      String out = run(model, "-a", "-debug");
      System.clearProperty(PROPERTY);
      if (out.contains("% redundant Routes of a travelling salesman tour")) {
        detected++;
      }
      solved += without.isEmpty() ? 0 : 1;
      assertEquals(without, solutions(out), "trial " + trial + "\n" + model);
    }
    // a model that fails while it is read never reaches the detection
    assertTrue(detected >= 15, "too few detections: " + detected);
    assertTrue(solved > 5, "too few satisfiable trials: " + solved);
  }

  @Test
  @Timeout(120)
  void tspRoutesKeepTheOptimum() throws IOException {
    Random random = new Random(17);
    for (int trial = 0; trial < 30; trial++) {
      String model = randomModel(random, true);
      String without = optimum(run(model));
      System.setProperty(PROPERTY, "true");
      String with = optimum(run(model));
      String free = optimum(run(model, "-f"));
      System.clearProperty(PROPERTY);
      assertEquals(without, with, "trial " + trial + "\n" + model);
      assertEquals(without, free, "trial " + trial + " -f\n" + model);
    }
  }

  @Test
  void modeIsOffByDefault() throws IOException {
    String model = randomModel(new Random(3), true);
    assertFalse(run(model, "-debug").contains("% redundant Routes of a travelling salesman tour"));
    System.setProperty(PROPERTY, "true");
    assertTrue(run(model, "-debug").contains("% redundant Routes of a travelling salesman tour"));
  }

  // the last objective printed and whether it was proved, or the unsatisfiability
  private static String optimum(String out) {
    String last = "none";
    for (String l : out.split("\\R")) {
      if (l.startsWith("len = ") || l.contains("UNSATISFIABLE")) {
        last = l.strip();
      }
    }
    return last + (out.contains("==========") ? " proved" : "");
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
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
                    new TreeSet<>(
                        Arrays.stream(s.strip().split("\\R"))
                            .filter(l -> !l.isBlank() && !l.startsWith("%"))
                            .toList())))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
