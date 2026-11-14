/*
 * GiantTourFlatzincTest.java
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
 * Checks the detection of vehicle routes written as a giant tour (a circuit over the customers and
 * a start and an end node per vehicle, the end node of each vehicle followed by the start node of
 * the next), which posts a redundant Routes with its arc rows: the solutions with the detection
 * must be those without it.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class GiantTourFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.giantTour";

  @TempDir Path tmp;

  @AfterEach
  void detectionDefault() {
    System.clearProperty(PROPERTY);
  }

  // customers 1..c, start nodes c+1..c+v, end nodes c+v+1..c+2v; a load accumulated along the
  // tour up to a capacity, travel times accumulated into arrival times, and bounds on the total
  // travel time and on the sum of the arrival times at the end nodes
  private static String randomModel(Random random, boolean optimize) {
    int c = 3 + random.nextInt(2);
    int v = 2;
    int n = c + 2 * v;
    int[] demand = new int[n + 1];
    for (int i = 1; i <= c; i++) {
      demand[i] = 1 + random.nextInt(3);
    }
    int capacity = 3 + random.nextInt(3);
    int[][] distance = new int[n + 1][n + 1];
    int[] depot = new int[c + 1];
    for (int i = 1; i <= c; i++) {
      depot[i] = 1 + random.nextInt(4);
    }
    for (int i = 1; i <= n; i++) {
      for (int j = 1; j <= n; j++) {
        if (i <= c && j <= c) {
          distance[i][j] = i == j ? 0 : 1 + random.nextInt(4);
        } else if (i <= c) {
          distance[i][j] = depot[i];
        } else if (j <= c) {
          distance[i][j] = depot[j];
        }
      }
    }
    int horizon = 4 * (c + 1) * 2;
    StringBuilder f = new StringBuilder();
    StringBuilder succ = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      if (i > c + v) {
        // the end node of vehicle k is followed by the start node of vehicle k + 1
        int k = i - c - v;
        succ.append(succ.isEmpty() ? "" : ",").append(c + 1 + k % v);
      } else {
        f.append("var 1..").append(n).append(": s").append(i).append(";\n");
        succ.append(succ.isEmpty() ? "" : ",").append('s').append(i);
      }
    }
    StringBuilder load = new StringBuilder();
    StringBuilder arrival = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      boolean start = i > c && i <= c + v;
      String sep = load.isEmpty() ? "" : ",";
      if (start) {
        load.append(sep).append(0);
        arrival.append(sep).append(0);
      } else {
        f.append("var 0..").append(capacity).append(": l").append(i).append(";\n");
        f.append("var 0..").append(horizon).append(": t").append(i).append(";\n");
        load.append(sep).append('l').append(i);
        arrival.append(sep).append('t').append(i);
      }
    }
    f.append("array [1..")
        .append(n)
        .append("] of var int: succ:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(succ)
        .append("];\n");
    f.append("array [1..").append(n).append("] of var int: load = [").append(load).append("];\n");
    f.append("array [1..")
        .append(n)
        .append("] of var int: time = [")
        .append(arrival)
        .append("];\n");
    StringBuilder ds = new StringBuilder();
    for (int i = 1; i <= c + v; i++) {
      StringBuilder row = new StringBuilder();
      for (int j = 1; j <= n; j++) {
        row.append(j == 1 ? "" : ",").append(distance[i][j]);
      }
      f.append("array [1..").append(n).append("] of int: c").append(i).append(" = [");
      f.append(row).append("];\n");
      f.append("var 0..4: d").append(i).append(";\n");
      f.append("var int: a").append(i).append(";\n");
      ds.append(ds.isEmpty() ? "" : ",").append('d').append(i);
    }
    for (int i = 1; i <= c; i++) {
      f.append("var int: y").append(i).append(";\n");
    }
    f.append("constraint jacop_circuit(succ);\n");
    for (int i = 1; i <= c + v; i++) {
      boolean start = i > c;
      f.append("constraint jacop_array_var_int_element_nonshifted(s")
          .append(i)
          .append(",c")
          .append(i)
          .append(",d")
          .append(i)
          .append(",1);\n");
      f.append("constraint jacop_array_var_int_element_nonshifted(s")
          .append(i)
          .append(",time,a")
          .append(i)
          .append(",1);\n");
      // a = t[i] + d[i], with t[i] = 0 at a start node
      f.append(start ? "constraint int_lin_eq([1,-1],[" : "constraint int_lin_eq([1,1,-1],[")
          .append(start ? "d" + i : "t" + i + ",d" + i)
          .append(",a")
          .append(i)
          .append("],0);\n");
      if (start) {
        f.append("constraint jacop_array_var_int_element_nonshifted(s")
            .append(i)
            .append(",load,0,1);\n");
      } else {
        f.append("constraint jacop_array_var_int_element_nonshifted(s")
            .append(i)
            .append(",load,y")
            .append(i)
            .append(",1);\n");
        f.append("constraint int_lin_eq([1,-1],[l")
            .append(i)
            .append(",y")
            .append(i)
            .append("],")
            .append(-demand[i])
            .append(");\n");
      }
    }
    int budget = 0;
    for (int i = 1; i <= c; i++) {
      budget += 2 * depot[i];
    }
    budget = budget * 3 / 4;
    int[] ones = new int[c + v];
    Arrays.fill(ones, 1);
    f.append("constraint int_lin_le(")
        .append(Arrays.toString(ones).replace(" ", ""))
        .append(",[")
        .append(ds)
        .append("],")
        .append(budget)
        .append(");\n");
    StringBuilder ends = new StringBuilder();
    for (int i = c + v + 1; i <= n; i++) {
      ends.append(ends.isEmpty() ? "" : ",").append('t').append(i);
    }
    if (optimize) {
      f.append("var 0..").append(2 * horizon).append(": obj:: output_var;\n");
      f.append("constraint int_lin_eq([1,1,-1],[").append(ends).append(",obj],0);\n");
      f.append("solve minimize obj;\n");
    } else {
      f.append("constraint int_lin_le([1,1],[").append(ends).append("],").append(budget + 2);
      f.append(");\n");
      f.append("solve satisfy;\n");
    }
    return f.toString();
  }

  @Test
  @Timeout(120)
  void giantTourRoutesKeepAllSolutions() throws IOException {
    Random random = new Random(7);
    int detected = 0;
    int solved = 0;
    for (int trial = 0; trial < 25; trial++) {
      String model = randomModel(random, false);
      System.setProperty(PROPERTY, "false");
      Set<String> without = solutions(run(model, "-a"));
      System.clearProperty(PROPERTY);
      String out = run(model, "-a", "-debug");
      if (out.contains("% redundant Routes of a giant tour")) {
        detected++;
      }
      solved += without.isEmpty() ? 0 : 1;
      assertEquals(without, solutions(out), "trial " + trial + "\n" + model);
    }
    // a model that fails while it is read never reaches the detection
    assertTrue(detected >= 20, "too few detections: " + detected);
    assertTrue(solved > 5, "too few satisfiable trials: " + solved);
  }

  @Test
  @Timeout(120)
  void giantTourRoutesKeepTheOptimum() throws IOException {
    // the arc rows and the capacity cuts go to the linear relaxation, which bounds the objective
    Random random = new Random(13);
    for (int trial = 0; trial < 25; trial++) {
      String model = randomModel(random, true);
      System.setProperty(PROPERTY, "false");
      String without = optimum(run(model));
      System.clearProperty(PROPERTY);
      assertEquals(without, optimum(run(model)), "trial " + trial + "\n" + model);
    }
  }

  // the last objective printed and whether it was proved, or the unsatisfiability
  private static String optimum(String out) {
    String last = "none";
    for (String l : out.split("\\R")) {
      if (l.startsWith("obj = ") || l.contains("UNSATISFIABLE")) {
        last = l.strip();
      }
    }
    return last + (out.contains("==========") ? " proved" : "");
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    String model = randomModel(new Random(3), false);
    assertTrue(run(model, "-debug").contains("% redundant Routes of a giant tour"));
    System.setProperty(PROPERTY, "false");
    assertFalse(run(model, "-debug").contains("% redundant Routes of a giant tour"));
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
