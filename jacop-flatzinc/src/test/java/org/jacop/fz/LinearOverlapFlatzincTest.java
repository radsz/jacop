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

  /**
   * A set partitioning model whose first two rows share the sub-sum x0 + ... + x3, which the
   * factoring takes out; weight 2 on x39 makes the third row a non-set row.
   */
  private static String setPartitioning(int lastWeight) {
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < 40; i++) {
      fzn.append("var 0..1: x").append(i).append(";\n");
    }
    fzn.append("var 0..40: obj:: output_var;\n");
    fzn.append(row(IntStream.rangeClosed(0, 13), 0, 1));
    fzn.append(
        row(IntStream.concat(IntStream.rangeClosed(0, 3), IntStream.rangeClosed(14, 23)), 0, 1));
    fzn.append(
        row(IntStream.concat(IntStream.of(4, 14), IntStream.rangeClosed(24, 39)), lastWeight, 1));
    String all = IntStream.range(0, 40).mapToObj(i -> "x" + i).collect(Collectors.joining(","));
    fzn.append("constraint int_lin_eq([")
        .append(IntStream.range(0, 40).mapToObj(i -> "1").collect(Collectors.joining(",")))
        .append(",-1],[")
        .append(all)
        .append(",obj],0);\n");
    fzn.append("solve :: int_search([").append(all).append("],input_order,indomain_max,complete)");
    fzn.append(" minimize obj;\n");
    return fzn.toString();
  }

  // the row sum(x[i]) = rhs, with weight lastWeight on its last variable when it is not 0
  private static String row(IntStream columns, int lastWeight, int rhs) {
    int[] cs = columns.toArray();
    StringBuilder weights = new StringBuilder();
    for (int k = 0; k < cs.length; k++) {
      weights
          .append(k > 0 ? "," : "")
          .append(k == cs.length - 1 && lastWeight != 0 ? lastWeight : 1);
    }
    return "constraint int_lin_eq(["
        + weights
        + "],"
        + Arrays.stream(cs).mapToObj(i -> "x" + i).collect(Collectors.joining(",", "[", "]"))
        + ","
        + rhs
        + ");\n";
  }

  /**
   * The set rows that the factoring rewrites still get the LP-guided branching of set partitioning
   * relaxations under -f: the relaxation sees rows over the shared sums, so Solve asks the detector
   * whether the model's rows were set rows (CSPLib bus driver scheduling r3, optimal in 17 s with
   * it, not in 240 s without).
   */
  @Test
  void factoredSetRowsKeepLpGuidedBranching() throws IOException {
    String model = setPartitioning(0);
    assertTrue(run(model, true, "-debug").contains("% linear overlap"), "not factored");
    assertTrue(run(model, true, "--lcg", "-f", "-s", "-v").contains("lpGuided=true"), "factored");
    assertTrue(
        run(model, false, "--lcg", "-f", "-s", "-v").contains("lpGuided=true"), "not factored");
    String other = setPartitioning(2);
    assertTrue(run(other, true, "--lcg", "-f", "-s", "-v").contains("lpGuided=false"), "weight 2");
    assertEquals(solutions(run(model, false, "-f")), solutions(run(model, true, "-f")));
  }

  /**
   * A row that is a multiple of the shared sub-sum, {@code 2 * (x0 + ... + x4) <= 7}, becomes the
   * bound {@code 2 * z <= 7} of the sum's variable, which the store holds as a domain and not as a
   * constraint. The linear relaxation substitutes z back and must still get the row: it has the
   * rows of the unfactored model (MIPLIB p0548 lost 88 of its 174 rows, root cut bound 464 instead
   * of 7,325, optimum 8,691).
   */
  @Test
  void rowReducedToTheSharedSumStaysInTheRelaxation() throws IOException {
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < 8; i++) {
      fzn.append("var 0..1: x").append(i).append(";\n");
    }
    fzn.append("var 0..100: obj:: output_var;\n");
    fzn.append("constraint int_lin_le([2,2,2,2,2],[x0,x1,x2,x3,x4],7);\n");
    fzn.append("constraint int_lin_le([1,1,1,1,1,1,1],[x0,x1,x2,x3,x4,x5,x6],5);\n");
    fzn.append("constraint int_lin_le([1,1,1,1,1,1,1,1],[x0,x1,x2,x3,x4,x5,x6,x7],6);\n");
    fzn.append("constraint int_lin_eq([3,5,7,9,11,4,6,8,-1],[x0,x1,x2,x3,x4,x5,x6,x7,obj],0);\n");
    fzn.append("solve maximize obj;\n");
    String model = fzn.toString();
    String factored = run(model, true, "--lcg", "off", "-s", "-v", "--search-statistics");
    String plain = run(model, false, "--lcg", "off", "-s", "-v", "--search-statistics");
    assertTrue(run(model, true, "-debug").contains("% linear overlap"), "not factored");
    assertTrue(factored.contains("lpUnitRows=1"), factored);
    // the rows give 47.5 (x0..x4 at 3.5, x5, x6 at 1.5, x7 at 1); without 2 * z <= 7 it is 53
    assertEquals(47.5, Double.parseDouble(stat(factored, "lpRootBound")), 1e-6, factored);
    assertEquals(optimum(plain, model), optimum(factored, model));
  }

  // the first value of a statistic
  private static String stat(String out, String name) {
    for (String line : out.split("\\R")) {
      if (line.startsWith("%%%mzn-stat: " + name + "=")) {
        return line.substring(line.indexOf('=') + 1);
      }
    }
    return null;
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
