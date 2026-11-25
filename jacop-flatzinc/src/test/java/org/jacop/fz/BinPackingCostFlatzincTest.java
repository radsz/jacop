/*
 * BinPackingCostFlatzincTest.java
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
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests the bin packing cost bounds ({@link org.jacop.fz.constraints.BinPackingCostBound}) on
 * models shaped like the balanced academic curriculum: courses with loads go to periods, each
 * curriculum is a bin packing of its courses, and the objective sums the squares of the distances
 * of the curricula's period loads to their ideal band.
 */
class BinPackingCostFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.binPackingCost";

  @TempDir Path tmp;

  /**
   * A curriculum model: {@code courses} with the given loads over {@code periods} periods, the
   * curricula given by their courses, a precedence between the first two courses.
   */
  private static String model(int periods, int[] load, int[][] curricula) {
    StringBuilder fzn = new StringBuilder();
    int n = load.length;
    for (int i = 0; i < n; i++) {
      fzn.append("var 1..").append(periods).append(": p").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: p:: output_array([1..")
        .append(n)
        .append("]) = [");
    for (int i = 0; i < n; i++) {
      fzn.append(i > 0 ? "," : "").append("p").append(i);
    }
    fzn.append("];\n");
    List<String> squares = new ArrayList<>();
    StringBuilder constraints = new StringBuilder();
    for (int c = 0; c < curricula.length; c++) {
      int total = 0;
      for (int i : curricula[c]) {
        total += load[i];
      }
      int floor = total / periods;
      int ceil = floor + (total % periods == 0 ? 0 : 1);
      StringBuilder bins = new StringBuilder();
      StringBuilder weights = new StringBuilder();
      for (int k = 0; k < curricula[c].length; k++) {
        bins.append(k > 0 ? "," : "").append("p").append(curricula[c][k]);
        weights.append(k > 0 ? "," : "").append(load[curricula[c][k]]);
      }
      StringBuilder loads = new StringBuilder();
      for (int q = 0; q < periods; q++) {
        String l = "l" + c + "_" + q;
        String a = "a" + c + "_" + q;
        String b = "b" + c + "_" + q;
        String d = "d" + c + "_" + q;
        String s = "s" + c + "_" + q;
        fzn.append("var 0..").append(total).append(": ").append(l).append(";\n");
        fzn.append("var ").append(-total).append("..").append(total).append(": ").append(a);
        fzn.append(";\nvar ").append(-total).append("..").append(total).append(": ").append(b);
        fzn.append(";\nvar 0..").append(total).append(": ").append(d).append(";\n");
        fzn.append("var 0..").append(total * total).append(": ").append(s).append(";\n");
        loads.append(q > 0 ? "," : "").append(l);
        // a = l - ceil, b = floor - l, d = max(a, b), s = d * d
        constraints.append("constraint int_lin_eq([1,-1],[").append(l).append(",").append(a);
        constraints.append("],").append(ceil).append(");\n");
        constraints.append("constraint int_lin_eq([1,1],[").append(l).append(",").append(b);
        constraints.append("],").append(floor).append(");\n");
        constraints.append("constraint int_max(").append(a).append(",").append(b).append(",");
        constraints.append(d).append(");\n");
        constraints.append("constraint int_times(").append(d).append(",").append(d).append(",");
        constraints.append(s).append(");\n");
        squares.add(s);
      }
      constraints.append("constraint jacop_bin_packing([").append(bins).append("],[");
      constraints.append(loads).append("],[").append(weights).append("],1);\n");
    }
    fzn.append("var 0..1000000: obj:: output_var;\n");
    fzn.append(constraints);
    fzn.append("constraint int_lt(p0,p1);\n");
    StringBuilder ones = new StringBuilder();
    for (int k = 0; k < squares.size(); k++) {
      ones.append("1,");
    }
    fzn.append("constraint int_lin_eq([")
        .append(ones)
        .append("-1],[")
        .append(String.join(",", squares))
        .append(",obj],0);\n");
    fzn.append("solve minimize obj;\n");
    return fzn.toString();
  }

  /**
   * Three courses of load 5 over two periods: the curriculum's total 15 has the band 7..8, the best
   * loads are 10 and 5, each 2 away from the band, so the objective is at least 8. The linear
   * relaxation and the bounds of the squares give 0 at the root; the bound of the bin packing gives
   * 8 before any search.
   */
  @Test
  void rootBoundIsTheBinPackingsMinimum() throws IOException {
    String model = model(2, new int[] {5, 5, 5}, new int[][] {{0, 1, 2}});
    String on = run(model, true, "--lcg", "-s", "--search-statistics");
    assertTrue(firstBound(on) >= 8, on);
    assertEquals("8", optimum(on, model));
    String off = run(model, false, "--lcg", "-s", "--search-statistics");
    assertTrue(firstBound(off) < 8, off);
    assertEquals("8", optimum(off, model));
    assertTrue(run(model, true, "-debug").contains("% bin packing cost bounds: 1"));
  }

  /**
   * The square of a variable of 101 values gets the 101 squares as its domain, which the costs of
   * the bin packings tabulate and the cores of LCG step through: the restriction to products
   * counted 101 * 101 pairs of factor values, above its limit of 4,096, and left 0..10,000.
   */
  @Test
  void squareOfAWideFactorHasOnlySquares() throws IOException {
    String model =
        "var 0..100: x:: output_var;\nvar 0..10000: z:: output_var;\n"
            + "constraint int_times(x,x,z);\nconstraint int_le(2,z);\n"
            + "solve :: int_search([z],input_order,indomain_min,complete) satisfy;\n";
    String out = run(model, true, "-debug");
    assertTrue(out.contains("z::{4, 9, 16, 25, 36,"), out);
  }

  /** Random curriculum models keep their optimum with the bounds, under CP, LCG and LCG -f. */
  @Test
  void boundsKeepTheOptimum() throws IOException {
    Random random = new Random(41);
    int trials = Integer.getInteger("binPackingCost.trials", 60);
    int fired = 0;
    for (int trial = 0; trial < trials; trial++) {
      int periods = 2 + random.nextInt(3);
      int n = 3 + random.nextInt(5);
      int[] load = new int[n];
      for (int i = 0; i < n; i++) {
        load[i] = 1 + random.nextInt(random.nextBoolean() ? 3 : 12);
      }
      int[][] curricula = new int[1 + random.nextInt(3)][];
      for (int c = 0; c < curricula.length; c++) {
        List<Integer> courses = new ArrayList<>();
        for (int i = 0; i < n; i++) {
          if (i < 2 || random.nextInt(3) > 0) {
            courses.add(i);
          }
        }
        curricula[c] = courses.stream().mapToInt(Integer::intValue).toArray();
      }
      String model = model(periods, load, curricula);
      fired += run(model, true, "-debug").contains("% bin packing cost bounds") ? 1 : 0;
      String expected = optimum(run(model, false, "--lcg", "off"), model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "off"), model),
          "trial " + trial + " cp\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on"), model),
          "trial " + trial + " lcg\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on", "-f"), model),
          "trial " + trial + " lcg -f\n" + model);
    }
    assertTrue(fired > trials / 3, "fired " + fired);
  }

  private String run(String model, boolean on, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = new String[options.length + 1];
    System.arraycopy(options, 0, args, 0, options.length);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, Boolean.toString(on));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  // the first objective bound the run reports, -1 when there is none
  private static long firstBound(String out) {
    for (String line : out.split("\\R")) {
      if (line.startsWith("%%%mzn-stat: objectiveBound=")) {
        return Long.parseLong(line.substring(line.indexOf('=') + 1).trim());
      }
    }
    return -1;
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
