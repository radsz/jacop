/*
 * CostAlldifferentFlatzincTest.java
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the detection of all-different and global cardinality constraints with a sum of value
 * costs in the FlatZinc front end, which posts a redundant CostAlldifferent or CostGCC: all
 * solutions must match a brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class CostAlldifferentFlatzincTest {

  @TempDir Path tmp;

  /** The FlatZinc of a random model and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce) {}

  /**
   * A random model on n variables with values offset..offset+m-1: kind 0 is jacop_alldiff, 1
   * jacop_count_values (an open GCC over some of the values) and 2 jacop_gcc (closed).
   */
  private static Model randomModel(Random random, int kind) {
    int n = 2 + random.nextInt(4);
    int m = kind == 0 ? n + random.nextInt(3) : 1 + random.nextInt(4);
    // array_int_element indexes from 1; jacop_array_var_int_element_nonshifted from any value
    boolean shifted = random.nextBoolean();
    int offset = shifted ? 1 : random.nextInt(3) - 1;
    int[][] d = new int[n][m];
    for (int[] row : d) {
      for (int j = 0; j < m; j++) {
        row[j] = random.nextInt(30) - 5;
      }
    }
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] =
          java.util.stream.IntStream.range(0, m)
              .filter(j -> random.nextInt(4) != 0)
              .map(j -> j + offset)
              .toArray();
      if (domains[i].length == 0) {
        domains[i] = new int[] {offset + random.nextInt(m)};
      }
    }
    // the counted values and the bounds of their counters
    int[] counted = new int[0];
    int[][] counts = new int[m][];
    if (kind > 0) {
      List<Integer> values = new ArrayList<>();
      for (int j = 0; j < m; j++) {
        if (kind == 2 || random.nextBoolean()) {
          values.add(offset + j);
          int lo = random.nextInt(2);
          counts[j] = new int[] {lo, lo + random.nextInt(n)};
        }
      }
      counted = values.stream().mapToInt(Integer::intValue).toArray();
    }

    List<int[]> all = new ArrayList<>();
    enumerate(0, new int[n + 1], domains, offset, d, kind, counts, all);
    TreeSet<Integer> costs = new TreeSet<>();
    for (int[] s : all) {
      costs.add(s[n]);
    }
    int lo = costs.isEmpty() ? 0 : costs.first() - random.nextInt(3);
    int hi =
        costs.isEmpty()
            ? 10
            : random.nextBoolean() ? costs.first() + random.nextInt(10) : costs.last() + 2;

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(set(domains[i])).append(": x").append(i).append(";\n");
    }
    for (int i = 0; i < n; i++) {
      fzn.append("var -5..25: c").append(i).append(";\n");
    }
    for (int j = 0; j < counted.length; j++) {
      int[] b = counts[counted[j] - offset];
      fzn.append("var ").append(b[0]).append("..").append(b[1]).append(": k").append(j);
      fzn.append(";\n");
    }
    fzn.append("var ").append(lo).append("..").append(hi).append(": cost:: output_var;\n");
    fzn.append("array [1..").append(n).append("] of var int: x:: output_array([1..");
    fzn.append(n).append("]) = [").append(names("x", n)).append("];\n");
    for (int i = 0; i < n; i++) {
      // the row of costs as an element array indexed by the value
      String array = Arrays.toString(d[i]).replace(" ", "");
      if (shifted) {
        fzn.append("constraint array_int_element(x").append(i).append(',').append(array);
        fzn.append(",c").append(i).append(");\n");
      } else {
        fzn.append("constraint jacop_array_var_int_element_nonshifted(x").append(i).append(',');
        fzn.append(array).append(",c").append(i).append(',').append(offset).append(");\n");
      }
    }
    String counters = "[" + names("k", counted.length) + "]";
    switch (kind) {
      case 0 -> fzn.append("constraint jacop_alldiff(x);\n");
      case 1 ->
          fzn.append("constraint jacop_count_values(x,")
              .append(Arrays.toString(counted).replace(" ", ""))
              .append(',')
              .append(counters)
              .append(");\n");
      default ->
          fzn.append("constraint jacop_gcc(x,")
              .append(counters)
              .append(',')
              .append(offset)
              .append(");\n");
    }
    // the sum, with the cost first or last and either sign
    int sign = random.nextBoolean() ? 1 : -1;
    StringBuilder coefs = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    boolean costFirst = random.nextBoolean();
    if (costFirst) {
      coefs.append(-sign).append(',');
      vars.append("cost,");
    }
    for (int i = 0; i < n; i++) {
      coefs.append(i == 0 ? "" : ",").append(sign);
      vars.append(i == 0 ? "" : ",").append('c').append(i);
    }
    if (!costFirst) {
      coefs.append(',').append(-sign);
      vars.append(",cost");
    }
    fzn.append("constraint int_lin_eq([").append(coefs).append("],[").append(vars);
    fzn.append("],0);\n");
    fzn.append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    for (int[] s : all) {
      if (s[n] >= lo && s[n] <= hi) {
        expected.add(
            "cost = "
                + s[n]
                + "; x = array1d(1.."
                + n
                + ", "
                + Arrays.toString(Arrays.copyOf(s, n))
                + ");");
      }
    }
    return new Model(fzn.toString(), expected);
  }

  private static String names(String prefix, int k) {
    StringBuilder s = new StringBuilder();
    for (int i = 0; i < k; i++) {
      s.append(i == 0 ? "" : ",").append(prefix).append(i);
    }
    return s.toString();
  }

  private static String set(int[] values) {
    StringBuilder s = new StringBuilder("{");
    for (int k = 0; k < values.length; k++) {
      s.append(k == 0 ? "" : ",").append(values[k]);
    }
    return s.append('}').toString();
  }

  private static void enumerate(
      int i,
      int[] t,
      int[][] domains,
      int offset,
      int[][] d,
      int kind,
      int[][] counts,
      List<int[]> out) {
    int n = t.length - 1;
    if (i == n) {
      int m = d[0].length;
      int[] used = new int[m];
      long sum = 0;
      for (int k = 0; k < n; k++) {
        used[t[k] - offset]++;
        sum += d[k][t[k] - offset];
      }
      for (int j = 0; j < m; j++) {
        boolean ok =
            kind == 0
                ? used[j] <= 1
                : counts[j] == null
                    ? kind == 1 || used[j] == 0
                    : used[j] >= counts[j][0] && used[j] <= counts[j][1];
        if (!ok) {
          return;
        }
      }
      int[] s = t.clone();
      s[n] = (int) sum;
      out.add(s);
      return;
    }
    for (int v : domains[i]) {
      t[i] = v;
      enumerate(i + 1, t, domains, offset, d, kind, counts, out);
    }
  }

  private void check(int kind, long seed, String detection) throws IOException {
    Random random = new Random(seed);
    int detected = 0;
    for (int trial = 0; trial < 150; trial++) {
      Model model = randomModel(random, kind);
      String out = run(model.fzn(), "-a", "-debug");
      if (out.contains(detection)) {
        detected++;
      }
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
    // a model that fails before the detection runs is not detected, every other one is
    assertTrue(detected > 30, "detected " + detected);
  }

  @Test
  void detectedCostAlldifferentKeepsAllSolutions() throws IOException {
    check(0, 7, "% redundant CostAlldifferent");
  }

  @Test
  void detectedOpenCostGccKeepsAllSolutions() throws IOException {
    check(1, 11, "% redundant CostGCC");
  }

  @Test
  void detectedClosedCostGccKeepsAllSolutions() throws IOException {
    check(2, 13, "% redundant CostGCC");
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    Model model = randomModel(new Random(3), 0);
    String property = "org.jacop.fz.costAlldifferent";
    System.setProperty(property, "false");
    try {
      assertFalse(run(model.fzn(), "-a", "-debug").contains("% redundant CostAlldifferent"));
    } finally {
      System.clearProperty(property);
    }
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
