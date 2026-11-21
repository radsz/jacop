/*
 * TspEdgeEliminationFlatzincTest.java
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
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the TSP edge elimination of the FlatZinc front end (org.jacop.fz.tspElimination, {@link
 * org.jacop.constraints.TspEdgeElimination}): on random pure symmetric travelling salesman models
 * the optimum must be the one without it, with the model's search, with free search and with the
 * TSP mode; a side constraint on the successors or an asymmetric distance turns it off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class TspEdgeEliminationFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.tspElimination";

  private static final String MARK = "% TSP edge elimination: ";

  private static final String KOPT = "org.jacop.fz.tspKOpt";

  private static final String KOPT_MARK = "% TSP k-opt dominance";

  @TempDir Path tmp;

  @AfterEach
  void modeDefault() {
    System.clearProperty(PROPERTY);
    System.clearProperty(KOPT);
    System.clearProperty("org.jacop.fz.tsp");
  }

  // a pure TSP over n cities: symmetric distances, Euclidean or random with ties, some edges
  // missing in both directions; side adds a constraint on the successors, asymmetric one distance
  private static String randomModel(Random random, boolean side, boolean asymmetric) {
    int n = 6 + random.nextInt(3);
    boolean euclid = random.nextBoolean();
    int[] px = new int[n + 1];
    int[] py = new int[n + 1];
    for (int i = 1; i <= n; i++) {
      px[i] = random.nextInt(50);
      py[i] = random.nextInt(50);
    }
    int[][] d = new int[n + 1][n + 1];
    boolean[][] missing = new boolean[n + 1][n + 1];
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        d[i][j] =
            euclid
                ? (int) Math.round(Math.hypot(px[i] - px[j], py[i] - py[j]))
                : random.nextInt(15);
        d[j][i] = d[i][j];
        missing[i][j] = random.nextInt(8) == 0;
        missing[j][i] = missing[i][j];
      }
    }
    if (asymmetric) {
      d[1][2]++;
    }
    StringBuilder f = new StringBuilder();
    StringBuilder succ = new StringBuilder();
    StringBuilder ds = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      StringBuilder values = new StringBuilder();
      for (int j = 1; j <= n; j++) {
        if (j != i && !missing[i][j]) {
          values.append(values.isEmpty() ? "" : ",").append(j);
        }
      }
      f.append("var {").append(values).append("}: s").append(i).append(";\n");
      StringBuilder row = new StringBuilder();
      for (int j = 1; j <= n; j++) {
        row.append(j == 1 ? "" : ",").append(d[i][j]);
      }
      f.append("array [1..").append(n).append("] of int: c").append(i).append(" = [");
      f.append(row).append("];\n");
      f.append("var 0..100: d").append(i).append(";\n");
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
    f.append("var 0..").append(100 * n).append(": len:: output_var;\n");
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
    if (side) {
      f.append("constraint int_lin_le([1,-1],[s1,s2],0);\n");
    }
    int[] ones = new int[n + 1];
    Arrays.fill(ones, 1);
    ones[n] = -1;
    f.append("constraint int_lin_eq(")
        .append(Arrays.toString(ones).replace(" ", ""))
        .append(",[")
        .append(ds)
        .append(",len],0);\n");
    f.append("solve :: int_search(succ,first_fail,indomain_min,complete) minimize len;\n");
    return f.toString();
  }

  @Test
  @Timeout(180)
  void eliminationKeepsTheOptimum() throws IOException {
    Random random = new Random(23);
    int fired = 0;
    for (int trial = 0; trial < 30; trial++) {
      String model = randomModel(random, false, false);
      System.setProperty(PROPERTY, "false");
      String without = optimum(run(model));
      System.clearProperty(PROPERTY);
      String out = run(model, "-debug");
      if (removed(out) > 0) {
        fired++;
      }
      assertEquals(without, optimum(out), "trial " + trial + "\n" + model);
      assertEquals(without, optimum(run(model, "-f")), "trial " + trial + " -f\n" + model);
      System.setProperty("org.jacop.fz.tsp", "true");
      assertEquals(without, optimum(run(model)), "trial " + trial + " tsp\n" + model);
      System.clearProperty("org.jacop.fz.tsp");
    }
    assertTrue(fired >= 20, "too few eliminations: " + fired);
  }

  @Test
  @Timeout(180)
  void kOptKeepsTheOptimum() throws IOException {
    Random random = new Random(31);
    for (int trial = 0; trial < 30; trial++) {
      String model = randomModel(random, false, false);
      System.clearProperty(KOPT);
      String without = optimum(run(model));
      System.setProperty(KOPT, "true");
      String out = run(model, "-debug");
      assertTrue(out.contains(KOPT_MARK), "trial " + trial);
      assertEquals(without, optimum(out), "trial " + trial + "\n" + model);
      assertEquals(without, optimum(run(model, "-f")), "trial " + trial + " -f\n" + model);
      assertEquals(
          without, optimum(run(model, "--lcg", "off")), "trial " + trial + " no lcg\n" + model);
    }
    assertFalse(run(randomModel(random, true, false), "-debug").contains(KOPT_MARK));
    System.clearProperty(KOPT);
    assertFalse(run(randomModel(random, false, false), "-debug").contains(KOPT_MARK));
    System.setProperty(KOPT, "true");
    assertFalse(run(randomModel(random, false, true), "-debug").contains(KOPT_MARK));
  }

  @Test
  void eliminationNeedsAPureSymmetricTour() throws IOException {
    Random random = new Random(29);
    for (int trial = 0; trial < 5; trial++) {
      assertFalse(
          run(randomModel(random, true, false), "-debug").contains(MARK), "side constraint");
      assertFalse(run(randomModel(random, false, true), "-debug").contains(MARK), "asymmetric");
    }
    String model = randomModel(random, false, false);
    assertTrue(run(model, "-debug").contains(MARK));
    System.setProperty(PROPERTY, "false");
    assertFalse(run(model, "-debug").contains(MARK));
  }

  // the 6-city tour of distances d where len, or a variable equal to it, may not take the value
  // hole
  private static String holeModel(int[][] d, int hole, String form) {
    int n = d.length;
    StringBuilder f = new StringBuilder();
    StringBuilder values = new StringBuilder();
    for (int v = 0; v <= 100 * n; v++) {
      if (v != hole) {
        values.append(values.isEmpty() ? "" : ",").append(v);
      }
    }
    for (int i = 1; i <= n; i++) {
      StringBuilder succ = new StringBuilder();
      for (int j = 1; j <= n; j++) {
        if (j != i) {
          succ.append(succ.isEmpty() ? "" : ",").append(j);
        }
      }
      f.append("var {").append(succ).append("}: s").append(i).append(";\n");
      f.append("array [1..").append(n).append("] of int: c").append(i).append(" = ");
      f.append(Arrays.toString(d[i - 1]).replace(" ", "")).append(";\n");
      f.append("var 0..100: d").append(i).append(";\n");
    }
    f.append("array [1..6] of var int: succ:: output_array([1..6]) = [s1,s2,s3,s4,s5,s6];\n");
    switch (form) {
      case "domain" -> f.append("var {").append(values).append("}: len:: output_var;\n");
      case "equal" ->
          f.append("var 0..600: len:: output_var;\nvar {").append(values).append("}: m = len;\n");
      default -> f.append("var 0..600: len:: output_var;\n");
    }
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
    if ("ne".equals(form)) {
      f.append("constraint int_ne(len,").append(hole).append(");\n");
    }
    f.append("constraint int_lin_eq([1,1,1,1,1,1,-1],[d1,d2,d3,d4,d5,d6,len],0);\n");
    f.append("solve :: int_search(succ,first_fail,indomain_min,complete) minimize len;\n");
    return f.toString();
  }

  @Test
  void objectiveWithAHoleKeepsTheOptimum() throws IOException {
    // the shortest tours have length 22 and 17, the next ones 23 and 19
    int[][] first = {
      {0, 2, 9, 1, 6, 8}, {2, 0, 9, 2, 8, 5}, {9, 9, 0, 7, 7, 8},
      {1, 2, 7, 0, 3, 1}, {6, 8, 7, 3, 0, 2}, {8, 5, 8, 1, 2, 0}
    };
    int[][] second = {
      {0, 3, 2, 5, 2, 8}, {3, 0, 8, 8, 7, 4}, {2, 8, 0, 2, 8, 1},
      {5, 8, 2, 0, 7, 7}, {2, 7, 8, 7, 0, 1}, {8, 4, 1, 7, 1, 0}
    };
    for (String form : new String[] {"domain", "equal", "ne"}) {
      String model = holeModel(first, 22, form);
      assertEquals("len = 23; proved", optimum(run(model)), form);
      assertFalse(run(model, "-debug").contains(MARK), form);
      System.setProperty(KOPT, "true");
      assertEquals("len = 19; proved", optimum(run(holeModel(second, 17, form))), form);
      System.clearProperty(KOPT);
    }
  }

  private static int removed(String out) {
    for (String l : out.split("\\R")) {
      if (l.startsWith(MARK)) {
        return Integer.parseInt(l.substring(MARK.length()).split(" ")[0]);
      }
    }
    return -1;
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
}
