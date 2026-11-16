/*
 * LinearEqualityPairsFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random models with equalities written as two opposite inequalities, scaled, with repeated and
 * fixed variables, duplicates and bounds that do not meet: turning the pairs into equalities must
 * keep every solution and every optimum.
 */
class LinearEqualityPairsFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.equalityPairs";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int n = 3 + random.nextInt(2);
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(random.nextInt(2) - 1).append("..").append(2 + random.nextInt(2));
      fzn.append(": x").append(i).append(":: output_var;\n");
    }
    fzn.append("var 1..1: one;\n");
    List<String> constraints = new ArrayList<>();
    int rows = 1 + random.nextInt(3);
    for (int r = 0; r < rows; r++) {
      List<String> vars = new ArrayList<>();
      List<Integer> coefficients = new ArrayList<>();
      int terms = 1 + random.nextInt(3);
      for (int t = 0; t < terms; t++) {
        // a repeated variable, or the fixed one, now and then
        vars.add(random.nextInt(6) == 0 ? "one" : "x" + random.nextInt(n));
        int c = random.nextInt(5) - 2;
        coefficients.add(c == 0 ? 1 : c);
      }
      int rhs = random.nextInt(7) - 3;
      constraints.add(row(coefficients, vars, rhs, 1 + random.nextInt(2), random));
      // the opposite row, sometimes scaled, with a bound that meets or not
      int k = 1 + random.nextInt(3);
      List<Integer> negated = new ArrayList<>();
      coefficients.forEach(c -> negated.add(-c * k));
      int slack = random.nextInt(4) == 0 ? random.nextInt(3) - 1 : 0;
      List<String> shuffled = new ArrayList<>(vars);
      // the same terms in another order
      if (random.nextBoolean()) {
        Collections.reverse(shuffled);
        Collections.reverse(negated);
      }
      constraints.add(row(negated, shuffled, -rhs * k + slack, 1, random));
      if (random.nextInt(4) == 0) {
        // a duplicate, looser or tighter
        constraints.add(row(coefficients, vars, rhs + random.nextInt(3) - 1, 1, random));
      }
    }
    if (optimise) {
      fzn.append("var -1000..1000: obj:: output_var;\n");
      StringBuilder a = new StringBuilder("[");
      StringBuilder v = new StringBuilder("[");
      for (int i = 0; i < n; i++) {
        a.append(random.nextInt(5) - 2).append(',');
        v.append('x').append(i).append(',');
      }
      a.append("-1]");
      v.append("obj]");
      constraints.add("constraint int_lin_eq(" + a + "," + v + ",0)");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      fzn.append(random.nextBoolean() ? "solve maximize obj;\n" : "solve minimize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  // a*x <= rhs, with every coefficient and the bound multiplied by scale (the bound plus a part
  // of the scale, which rounding by the gcd removes)
  private static String row(List<Integer> a, List<String> vars, int rhs, int scale, Random random) {
    List<Integer> scaled = new ArrayList<>();
    a.forEach(c -> scaled.add(c * scale));
    int bound = rhs * scale + (scale > 1 ? random.nextInt(scale) : 0);
    return "constraint int_lin_le("
        + scaled.toString().replace(" ", "")
        + ","
        + vars.toString().replace(" ", "")
        + ","
        + bound
        + ")";
  }

  @Test
  void pairsKeepAllSolutions() throws IOException {
    Random random = new Random(61);
    int merged = 0;
    int trials = Integer.getInteger("equalityPairs.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String on = run(model, true, "-a", "-debug");
      merged += on.contains("% equality pairs") ? 1 : 0;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(merged > trials / 2, "merged " + merged);
  }

  @Test
  void pairsKeepOptima() throws IOException {
    Random random = new Random(62);
    int trials = Integer.getInteger("equalityPairs.trials", 300) * 2 / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"));
      for (String[] options :
          List.of(
              new String[] {"--lcg", "off"}, new String[] {"--lcg", "on"}, new String[] {"-f"})) {
        assertEquals(
            expected,
            optimum(run(model, true, options)),
            "trial " + trial + " " + Arrays.toString(options) + "\n" + model);
      }
    }
  }

  /** 2x + 2y <= 3 rounds to x + y <= 1, which meets -x - y <= -1 in the equality 2x + 2y = 2. */
  @Test
  void roundedBoundsMeet() throws IOException {
    String model =
        """
        var 0..3: x:: output_var;
        var 0..3: y:: output_var;
        constraint int_lin_le([2,2],[x,y],3);
        constraint int_lin_le([-1,-1],[y,x],-1);
        solve satisfy;
        """;
    String out = run(model, true, "-a", "-debug");
    assertTrue(out.contains("% equality pairs: 1 equalities"), out);
    assertEquals(2, solutions(out), out);
  }

  private static int solutions(String out) {
    return out.split("----------", -1).length - 1;
  }

  private String run(String model, boolean pairs, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, String.valueOf(pairs));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
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
