/*
 * TranslationTilingFlatzincTest.java
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
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tilings of Z_n by translation written as an all different over the terms (x_j + a) mod n get the
 * redundant exact cover of {@code TranslationTilingDetector}: the solutions must stay the same,
 * with and without LCG.
 */
class TranslationTilingFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.translationTiling";

  @TempDir Path tmp;

  /**
   * The model of the XCSP3 tiling rhythmic canons, as MiniZinc flattens it: x_0 = 0 is fixed, so
   * its terms are constants; x_1 &lt; ... &lt; x_{m-1}; s = x + a and t = s mod n define the other
   * terms. The rhythm A is random, so many models have no tiling.
   */
  private static String model(Random random, int n, int[] a) {
    int m = n / a.length;
    StringBuilder fzn = new StringBuilder();
    List<String> terms = new ArrayList<>();
    List<String> constraints = new ArrayList<>();
    for (int j = 1; j < m; j++) {
      fzn.append("var 0..").append(n - 1).append(": x").append(j).append(";\n");
    }
    int next = 0;
    for (int ai : a) {
      terms.add(String.valueOf(ai % n));
      for (int j = 1; j < m; j++) {
        if (ai == 0) {
          terms.add("x" + j);
          continue;
        }
        String s = "s" + next;
        String t = "t" + next++;
        fzn.append("var ").append(ai).append("..").append(n - 1 + ai).append(": ").append(s);
        fzn.append(":: var_is_introduced :: is_defined_var;\n");
        fzn.append("var 0..").append(n - 1).append(": ").append(t);
        fzn.append(":: var_is_introduced :: is_defined_var;\n");
        // both orders of the sum occur in flattened models
        if (random.nextBoolean()) {
          constraints.add("int_lin_eq([1,-1],[x" + j + "," + s + "]," + -ai + ")");
        } else {
          constraints.add("int_lin_eq([-1,1],[x" + j + "," + s + "]," + ai + ")");
        }
        constraints.add("int_mod(" + s + "," + n + "," + t + ")");
        terms.add(t);
      }
    }
    fzn.append("array [1..").append(m - 1).append("] of var int: x:: output_array([1..");
    fzn.append(m - 1).append("]) = [");
    for (int j = 1; j < m; j++) {
      fzn.append(j > 1 ? "," : "").append("x").append(j);
    }
    fzn.append("];\n");
    for (int j = 1; j < m - 1; j++) {
      constraints.add("int_lt(x" + j + ",x" + (j + 1) + ")");
    }
    constraints.add("int_lt(0,x1)");
    constraints.add("jacop_alldiff(" + terms + ")");
    constraints.forEach(c -> fzn.append("constraint ").append(c.replace(" ", "")).append(";\n"));
    fzn.append("solve satisfy;\n");
    return fzn.toString();
  }

  // a random rhythm with 0, of a size that divides n
  private static int[] rhythm(Random random, int n) {
    List<Integer> sizes = new ArrayList<>();
    for (int k = 2; k < n; k++) {
      if (n % k == 0 && n / k >= 2) {
        sizes.add(k);
      }
    }
    int k = sizes.get(random.nextInt(sizes.size()));
    Set<Integer> a = new TreeSet<>();
    a.add(0);
    if (random.nextBoolean()) {
      // a tiling rhythm: a sum of k = p * q points spaced to tile (p * step, for q blocks)
      for (int i = 1; i < k; i++) {
        a.add(i * (n / k) % n);
      }
    }
    while (a.size() < k) {
      a.add(random.nextInt(n));
    }
    return a.stream().mapToInt(Integer::intValue).toArray();
  }

  @Test
  void exactCoverKeepsAllSolutions() throws IOException {
    Random random = new Random(41);
    int trials = Integer.getInteger("translationTiling.trials", 60);
    int found = 0;
    int solved = 0;
    for (int trial = 0; trial < trials; trial++) {
      int n = List.of(8, 9, 10, 12, 16, 18).get(random.nextInt(6));
      String fzn = model(random, n, rhythm(random, n));
      String on = run(fzn, null, "-a", "-debug");
      // a rhythm that cannot tile may fail at the root before the count is printed
      found += on.contains("CountValues") ? 1 : 0;
      Set<String> expected = solutions(run(fzn, "false", "-a"));
      solved += expected.isEmpty() ? 0 : 1;
      assertEquals(expected, solutions(on), "trial " + trial + "\n" + fzn);
      // the first solution under LCG and free search is a solution, or both say none
      String lcg = run(fzn, null, "-f", "--lcg", "on");
      assertEquals(expected.isEmpty(), solutions(lcg).isEmpty(), "trial " + trial + " lcg\n" + fzn);
      assertTrue(solutions(lcg).isEmpty() || expected.containsAll(solutions(lcg)), fzn);
    }
    assertTrue(found > trials * 9 / 10, "found " + found);
    assertTrue(solved > trials / 5, "solved " + solved);
  }

  @Test
  void rhythmicCanonOfPeriodTwelve() throws IOException {
    // A = {0, 1, 2}: B = {0, 3, 6, 9} is the only complement with 0
    String fzn = model(new Random(1), 12, new int[] {0, 1, 2});
    String out = run(fzn, null, "-a", "-debug");
    assertTrue(out.contains("translation tilings: 1"), out);
    assertEquals(Set.of("x = array1d(1..3, [3, 6, 9]);"), solutions(out));
  }

  private String run(String model, String property, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (property != null) {
      System.setProperty(PROPERTY, property);
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
}
