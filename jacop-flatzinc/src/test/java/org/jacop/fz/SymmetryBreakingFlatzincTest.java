/*
 * SymmetryBreakingFlatzincTest.java
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

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.IntUnaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks symmetry breaking in presolve on random models built to have symmetries: a random
 * permutation of the variables, and constraints closed under it. With symmetry breaking a model
 * must stay satisfiable or unsatisfiable, and keep its optimum; presolve runs in checking mode, so
 * every solution is also checked against the loaded model.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class SymmetryBreakingFlatzincTest {

  private static final Pattern GENERATORS = Pattern.compile("symmetryGenerators=(\\d+)");
  private static final Pattern OBJECTIVE = Pattern.compile("obj = (-?\\d+);");

  @TempDir Path tmp;

  @Test
  void pigeonholeIsRefutedWithFewFailures() throws IOException {
    int holes = 7;
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i <= holes; i++) {
      for (int h = 0; h < holes; h++) {
        fzn.append("var bool: p_").append(i).append('_').append(h).append(";\n");
      }
    }
    for (int i = 0; i <= holes; i++) {
      List<String> row = new ArrayList<>();
      for (int h = 0; h < holes; h++) {
        row.add("p_" + i + "_" + h);
      }
      fzn.append("constraint bool_clause([").append(String.join(",", row)).append("],[]);\n");
    }
    for (int h = 0; h < holes; h++) {
      for (int i = 0; i <= holes; i++) {
        for (int j = i + 1; j <= holes; j++) {
          fzn.append("constraint bool_clause([],[p_")
              .append(i)
              .append('_')
              .append(h)
              .append(",p_")
              .append(j)
              .append('_')
              .append(h)
              .append("]);\n");
        }
      }
    }
    fzn.append("solve satisfy;\n");
    String model = fzn.toString();

    String off = FlatzincTestRunner.run(tmp, model, "-s", "--presolve", "on", "--symmetry", "off");
    String on = FlatzincTestRunner.run(tmp, model, "-s", "--presolve", "check");
    assertTrue(off.contains("=====UNSATISFIABLE====="), off);
    assertTrue(on.contains("=====UNSATISFIABLE====="), on);
    // the pigeons and the holes are interchangeable: 7 + 6 generators
    assertEquals(13, generators(on));
    assertTrue(failures(on) * 10 < failures(off), on + "\n" + off);
  }

  @Test
  void allSolutionsOfASatisfactionProblemAreKept() throws IOException {
    String model =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
        constraint int_ne(x, y);
        solve satisfy;
        """;
    String out = FlatzincTestRunner.run(tmp, model, "-a", "-s", "--presolve", "check");
    assertEquals(6, FlatzincTestRunner.solutions(out).size(), out);
    assertFalse(out.contains("symmetryGenerators"), out);
  }

  @Test
  void randomSymmetricModelsKeepSatisfiabilityAndOptimum() throws IOException {
    Random random = new Random(5);
    int trials = Integer.getInteger("symmetry.trials", 300);
    int broken = 0;
    for (int trial = 0; trial < trials; trial++) {
      boolean optimise = random.nextBoolean();
      String model = randomModel(random, optimise);
      String off = FlatzincTestRunner.run(tmp, model, "--presolve", "off");
      String on = FlatzincTestRunner.run(tmp, model, "-s", "--presolve", "check");
      String what = "trial " + trial + "\n" + model + "\n" + on;
      boolean unsat = off.contains("=====UNSATISFIABLE=====");
      assertEquals(unsat, on.contains("=====UNSATISFIABLE====="), what);
      if (optimise && !unsat) {
        assertEquals(objective(off), objective(on), what);
      }
      if (generators(on) > 0) {
        broken++;
      }
    }
    assertTrue(broken > trials / 3, "broken " + broken);
  }

  private static int generators(String out) {
    Matcher m = GENERATORS.matcher(out);
    return m.find() ? Integer.parseInt(m.group(1)) : 0;
  }

  private static long failures(String out) {
    Matcher m = Pattern.compile("failures=(\\d+)").matcher(out);
    long last = -1;
    while (m.find()) {
      last = Long.parseLong(m.group(1));
    }
    return last;
  }

  private static int objective(String out) {
    Matcher m = OBJECTIVE.matcher(out);
    int last = Integer.MIN_VALUE;
    while (m.find()) {
      last = Integer.parseInt(m.group(1));
    }
    return last;
  }

  /**
   * A model over integer variables x0.. and Boolean variables b0.., with random constraints and
   * their images under a random permutation of each kind of variables.
   */
  private static String randomModel(Random random, boolean optimise) {
    int ints = 4 + random.nextInt(4);
    int bools = 3 + random.nextInt(3);
    int max = 2 + random.nextInt(2);
    int[] pi = permutation(ints, random);
    int[] pb = permutation(bools, random);

    Set<String> constraints = new LinkedHashSet<>();
    int base = 2 + random.nextInt(4);
    for (int k = 0; k < base; k++) {
      Template t = template(random, ints, bools, max);
      // the constraint and its images under the permutations until they repeat
      int[] x = t.x;
      int[] b = t.b;
      for (int step = 0; step < 60; step++) {
        constraints.add(t.text(x, b));
        x = Arrays.stream(x).map(v -> pi[v]).toArray();
        b = Arrays.stream(b).map(v -> pb[v]).toArray();
      }
    }

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < ints; i++) {
      fzn.append("var 0..").append(max).append(": x").append(i).append(" :: output_var;\n");
    }
    for (int i = 0; i < bools; i++) {
      fzn.append("var bool: b").append(i).append(" :: output_var;\n");
    }
    if (optimise) {
      fzn.append("var 0..").append(ints * max).append(": obj :: output_var;\n");
    }
    for (String c : constraints) {
      fzn.append("constraint ").append(c).append(";\n");
    }
    if (optimise) {
      List<String> ones = new ArrayList<>(Collections.nCopies(ints, "1"));
      ones.add("-1");
      List<String> xs = new ArrayList<>();
      for (int i = 0; i < ints; i++) {
        xs.add("x" + i);
      }
      xs.add("obj");
      fzn.append("constraint int_lin_eq([")
          .append(String.join(",", ones))
          .append("],[")
          .append(String.join(",", xs))
          .append("],0);\n");
      fzn.append(random.nextBoolean() ? "solve minimize obj;\n" : "solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  /** A random permutation made of a few cycles. */
  private static int[] permutation(int n, Random random) {
    List<Integer> order = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      order.add(i);
    }
    Collections.shuffle(order, random);
    int[] p = new int[n];
    for (int i = 0; i < n; i++) {
      p[i] = i;
    }
    int i = 0;
    while (i < n) {
      int len = Math.min(n - i, 1 + random.nextInt(3));
      for (int k = 0; k < len; k++) {
        p[order.get(i + k)] = order.get(i + (k + 1) % len);
      }
      i += len;
    }
    return p;
  }

  /** A constraint over integer variables x and Boolean variables b, written by text. */
  private static final class Template {
    final int[] x;
    final int[] b;
    final Text text;

    Template(int[] x, int[] b, Text text) {
      this.x = x;
      this.b = b;
      this.text = text;
    }

    String text(int[] xs, int[] bs) {
      return text.of(i -> xs[i], i -> bs[i]);
    }
  }

  private interface Text {
    String of(IntUnaryOperator x, IntUnaryOperator b);
  }

  private static Template template(Random r, int ints, int bools, int max) {
    int[] x = r.ints(4, 0, ints).toArray();
    int[] b = r.ints(3, 0, bools).toArray();
    int c0 = r.nextInt(5) - 2;
    int c1 = r.nextInt(5) - 2;
    int c2 = r.nextInt(5) - 2;
    int k = r.nextInt(2 * max + 1) - max / 2;
    int v = r.nextInt(max + 1);
    Text text =
        switch (r.nextInt(18)) {
          case 0 -> (xs, bs) -> "int_le(" + xv(xs, 0) + "," + xv(xs, 1) + ")";
          case 1 -> (xs, bs) -> "int_ne(" + xv(xs, 0) + "," + xv(xs, 1) + ")";
          case 2 ->
              (xs, bs) ->
                  "int_lin_le(["
                      + c0
                      + ","
                      + c1
                      + ","
                      + c2
                      + "],["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + ","
                      + xv(xs, 2)
                      + "],"
                      + k
                      + ")";
          case 3 -> (xs, bs) -> "int_plus(" + xv(xs, 0) + "," + xv(xs, 1) + "," + xv(xs, 2) + ")";
          case 4 -> (xs, bs) -> "int_max(" + xv(xs, 0) + "," + xv(xs, 1) + "," + xv(xs, 2) + ")";
          case 5 ->
              (xs, bs) -> "jacop_alldiff([" + xv(xs, 0) + "," + xv(xs, 1) + "," + xv(xs, 2) + "])";
          case 6 ->
              (xs, bs) ->
                  "jacop_count(["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + ","
                      + xv(xs, 2)
                      + "],"
                      + v
                      + ","
                      + xv(xs, 3)
                      + ")";
          case 7 ->
              (xs, bs) ->
                  "array_int_maximum("
                      + xv(xs, 3)
                      + ",["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + ","
                      + xv(xs, 2)
                      + "])";
          case 8 ->
              (xs, bs) -> "int_eq_reif(" + xv(xs, 0) + "," + xv(xs, 1) + "," + bv(bs, 0) + ")";
          case 9 ->
              (xs, bs) -> "bool_clause([" + bv(bs, 0) + "," + bv(bs, 1) + "],[" + bv(bs, 2) + "])";
          case 10 ->
              (xs, bs) -> "array_bool_or([" + bv(bs, 0) + "," + bv(bs, 1) + "]," + bv(bs, 2) + ")";
          case 11 ->
              (xs, bs) ->
                  "int_lin_le_reif(["
                      + c0
                      + ","
                      + c1
                      + "],["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + "],"
                      + k
                      + ","
                      + bv(bs, 0)
                      + ")";
          case 12 ->
              (xs, bs) ->
                  "jacop_cumulative(["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + ","
                      + xv(xs, 2)
                      + "],[1,"
                      + (1 + v)
                      + ",2],["
                      + (1 + v)
                      + ",1,1],2)";
          case 13 ->
              (xs, bs) -> "jacop_nvalue(" + xv(xs, 3) + ",[" + xv(xs, 0) + "," + xv(xs, 1) + "])";
          case 14 -> (xs, bs) -> "bool_xor(" + bv(bs, 0) + "," + bv(bs, 1) + "," + bv(bs, 2) + ")";
          case 15 -> (xs, bs) -> "int_times(" + xv(xs, 0) + "," + xv(xs, 1) + "," + xv(xs, 2) + ")";
          case 16 ->
              (xs, bs) ->
                  "int_lin_eq(["
                      + c0
                      + ","
                      + c1
                      + "],["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + "],"
                      + k
                      + ")";
          default -> (xs, bs) -> "bool2int(" + bv(bs, 0) + "," + xv(xs, 0) + ")";
        };
    return new Template(x, b, text);
  }

  private static String xv(IntUnaryOperator xs, int i) {
    return "x" + xs.applyAsInt(i);
  }

  private static String bv(IntUnaryOperator bs, int i) {
    return "b" + bs.applyAsInt(i);
  }
}
