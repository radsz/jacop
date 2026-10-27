/*
 * SubcircuitCostFlatzincTest.java
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
 * Checks the detection of subcircuits with a sum of arc costs in the FlatZinc front end, which
 * posts a redundant SubcircuitCost: all solutions must match a brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class SubcircuitCostFlatzincTest {

  @TempDir Path tmp;

  /** The FlatZinc of a random subcircuit with costs and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce) {}

  /*
   * A subcircuit on x with element arrays d[i] (style 0 array_int_element, 1
   * jacop_array_var_int_element_nonshifted) and one linear constraint over the element values,
   * with coefficients a[i], and reified tests t[i] (x[i] = v or x[i] != v) with coefficients p[i]:
   * either an equation with the cost variable (either sign, first or last) or an inequality with a
   * bound, as a length budget.
   */
  private static Model randomModel(Random random) {
    int n = 1 + random.nextInt(6);
    int style = random.nextInt(2);
    int[][] d = new int[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        d[i][j] = i == j && random.nextBoolean() ? 0 : random.nextInt(30) - 5;
      }
    }
    int[] a = new int[n];
    for (int i = 0; i < n; i++) {
      a[i] = random.nextInt(3) == 0 ? random.nextInt(5) - 2 : 1;
    }
    // tests: -1 none, else the value tested, x[i] = value when equal[i]
    int[] tested = new int[n];
    boolean[] equal = new boolean[n];
    int[] p = new int[n];
    for (int i = 0; i < n; i++) {
      tested[i] =
          random.nextInt(3) == 0 ? -1 : random.nextInt(2) == 0 ? i + 1 : 1 + random.nextInt(n);
      equal[i] = random.nextBoolean();
      p[i] = random.nextInt(21) - 5;
    }
    int[][] domains = new int[n][];
    double self = random.nextDouble();
    for (int i = 0; i < n; i++) {
      final int node = i;
      domains[i] =
          java.util.stream.IntStream.range(0, n)
              .filter(j -> j == node ? random.nextDouble() < self : random.nextInt(4) != 0)
              .map(j -> j + 1)
              .toArray();
      if (domains[i].length == 0) {
        domains[i] = new int[] {i + 1};
      }
    }

    List<int[]> subcircuits = new ArrayList<>();
    enumerate(0, new int[n], new boolean[n], domains, subcircuits);
    TreeSet<Integer> sums = new TreeSet<>();
    for (int[] s : subcircuits) {
      int sum = 0;
      for (int i = 0; i < n; i++) {
        sum += a[i] * d[i][s[i]];
        if (tested[i] >= 0 && (s[i] + 1 == tested[i]) == equal[i]) {
          sum += p[i];
        }
      }
      s[n] = sum;
      sums.add(sum);
    }
    boolean budget = random.nextInt(3) == 0;
    int lo = sums.isEmpty() ? 0 : sums.first() - random.nextInt(3);
    int hi =
        sums.isEmpty()
            ? 10
            : random.nextBoolean()
                ? sums.first() + random.nextInt(10)
                : sums.last() + random.nextInt(3);

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(set(domains[i])).append(": x").append(i).append(";\n");
    }
    for (int i = 0; i < n; i++) {
      fzn.append("var -5..25: c").append(i).append(";\n");
      if (tested[i] >= 0) {
        fzn.append("var bool: b").append(i).append(";\n");
        fzn.append("var 0..1: t").append(i).append(";\n");
      }
    }
    if (!budget) {
      fzn.append("var ").append(lo).append("..").append(hi).append(": cost:: output_var;\n");
    }
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < n; i++) {
      xs.append(i == 0 ? "" : ",").append('x').append(i);
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");
    for (int i = 0; i < n; i++) {
      String array = Arrays.toString(d[i]).replace(" ", "");
      if (style == 0) {
        fzn.append("constraint array_int_element(x").append(i).append(',').append(array);
        fzn.append(",c").append(i).append(");\n");
      } else {
        fzn.append("constraint jacop_array_var_int_element_nonshifted(x").append(i);
        fzn.append(',').append(array).append(",c").append(i).append(",1);\n");
      }
      if (tested[i] >= 0) {
        fzn.append("constraint int_").append(equal[i] ? "eq" : "ne").append("_reif(x").append(i);
        fzn.append(',').append(tested[i]).append(",b").append(i).append(");\n");
        fzn.append("constraint bool2int(b").append(i).append(",t").append(i).append(");\n");
      }
    }
    fzn.append("constraint jacop_subcircuit(x);\n");

    List<String> coefs = new ArrayList<>();
    List<String> vars = new ArrayList<>();
    int sign = budget || random.nextBoolean() ? 1 : -1;
    for (int i = 0; i < n; i++) {
      coefs.add(String.valueOf(sign * a[i]));
      vars.add("c" + i);
      if (tested[i] >= 0) {
        coefs.add(String.valueOf(sign * p[i]));
        vars.add("t" + i);
      }
    }
    if (budget) {
      fzn.append("constraint int_lin_le([").append(String.join(",", coefs)).append("],[");
      fzn.append(String.join(",", vars)).append("],").append(hi).append(");\n");
    } else {
      int at = random.nextBoolean() ? 0 : coefs.size();
      coefs.add(at, String.valueOf(-sign));
      vars.add(at, "cost");
      fzn.append("constraint int_lin_eq([").append(String.join(",", coefs)).append("],[");
      fzn.append(String.join(",", vars)).append("],0);\n");
    }
    fzn.append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    for (int[] s : subcircuits) {
      if ((budget || s[n] >= lo) && s[n] <= hi) {
        int[] values = new int[n];
        for (int i = 0; i < n; i++) {
          values[i] = s[i] + 1;
        }
        String x = "x = array1d(1.." + n + ", " + Arrays.toString(values) + ");";
        expected.add(budget ? x : "cost = " + s[n] + "; " + x);
      }
    }
    return new Model(fzn.toString(), expected);
  }

  private static String set(int[] values) {
    StringBuilder s = new StringBuilder("{");
    for (int k = 0; k < values.length; k++) {
      s.append(k == 0 ? "" : ",").append(values[k]);
    }
    return s.append('}').toString();
  }

  // every subcircuit in the domains, as successors from 0 with a free last entry for the sum
  private static void enumerate(
      int i, int[] next, boolean[] used, int[][] domains, List<int[]> out) {
    int n = next.length;
    if (i == n) {
      int start = -1;
      int inCircuit = 0;
      for (int k = 0; k < n; k++) {
        if (next[k] != k) {
          start = k;
          inCircuit++;
        }
      }
      int steps = 0;
      if (start >= 0) {
        int node = start;
        do {
          node = next[node];
          steps++;
        } while (node != start && steps <= n);
      }
      if (steps == inCircuit) {
        out.add(Arrays.copyOf(next, n + 1));
      }
      return;
    }
    for (int v : domains[i]) {
      int j = v - 1;
      if (!used[j]) {
        used[j] = true;
        next[i] = j;
        enumerate(i + 1, next, used, domains, out);
        used[j] = false;
      }
    }
  }

  @Test
  void detectedSubcircuitCostKeepsAllSolutions() throws IOException {
    Random random = new Random(17);
    int detected = 0;
    for (int trial = 0; trial < 300; trial++) {
      Model model = randomModel(random);
      String out = run(model.fzn(), "-a", "-debug");
      if (out.contains("% redundant SubcircuitCost")) {
        detected++;
      }
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
    // models whose successors are fixed before the detection runs are not detected
    assertTrue(detected > 100, "detected " + detected);
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    Model model = randomModel(new Random(5));
    String property = "org.jacop.fz.circuitCost";
    System.setProperty(property, "false");
    try {
      assertFalse(run(model.fzn(), "-a", "-debug").contains("% redundant SubcircuitCost"));
    } finally {
      System.clearProperty(property);
    }
  }

  @Test
  void budgetWithOtherVariablesIsNotDetected() throws IOException {
    // c0 + c1 + c2 + y <= 7 does not bound the arc costs alone
    String fzn =
        """
        var 1..3: x0;
        var 1..3: x1;
        var 1..3: x2;
        var 0..9: c0;
        var 0..9: c1;
        var 0..9: c2;
        var 0..1: y:: output_var;
        array [1..3] of var int: x:: output_array([1..3]) = [x0,x1,x2];
        constraint array_int_element(x0,[0,1,2],c0);
        constraint array_int_element(x1,[3,0,4],c1);
        constraint array_int_element(x2,[5,6,0],c2);
        constraint jacop_subcircuit(x);
        constraint int_ne(x0,1);
        constraint int_lin_le([1,1,1,1],[c0,c1,c2,y],7);
        solve satisfy;
        """;
    String out = run(fzn, "-a", "-debug");
    assertFalse(out.contains("% redundant SubcircuitCost"));
    assertEquals(
        Set.of(
            "x = array1d(1..3, [2, 1, 3]); y = 0;",
            "x = array1d(1..3, [2, 1, 3]); y = 1;",
            "x = array1d(1..3, [3, 2, 1]); y = 0;"),
        solutions(out));
  }

  @Test
  void subcircuitCostPredicateKeepsAllSolutions() throws IOException {
    // jacop_subcircuit_cost from the mznlib predicate subcircuit_cost, d given row by row
    int[][] d = {{4, 3, 9, 2}, {5, 0, 1, 7}, {2, 6, 3, 8}, {1, 4, 6, 5}};
    String fzn =
        """
        var 1..4: x0;
        var 1..4: x1;
        var 1..4: x2;
        var 1..4: x3;
        var 0..13: cost:: output_var;
        array [1..4] of var int: x:: output_array([1..4]) = [x0,x1,x2,x3];
        constraint jacop_subcircuit_cost(x,[4,3,9,2,5,0,1,7,2,6,3,8,1,4,6,5],cost);
        solve satisfy;
        """;
    int[][] domains = new int[4][];
    Arrays.fill(domains, new int[] {1, 2, 3, 4});
    List<int[]> all = new ArrayList<>();
    enumerate(0, new int[4], new boolean[4], domains, all);
    Set<String> expected = new TreeSet<>();
    for (int[] s : all) {
      int sum = 0;
      int[] values = new int[4];
      for (int i = 0; i < 4; i++) {
        sum += d[i][s[i]];
        values[i] = s[i] + 1;
      }
      if (sum <= 13) {
        expected.add("cost = " + sum + "; x = array1d(1..4, " + Arrays.toString(values) + ");");
      }
    }
    assertEquals(expected, solutions(run(fzn, "-a")));
  }

  @Test
  void weightedSubcircuitsPredicateKeepsAllSolutions() throws IOException {
    // two tours over four nodes, node 0 in tour 1; every arc costs 1 and leaving a node out 0
    String fzn =
        """
        var 1..4: x0;
        var 1..4: x1;
        var 1..4: x2;
        var 1..4: x3;
        var 1..1: t0;
        var 0..2: t1;
        var 0..2: t2;
        var 0..2: t3;
        var 0..10: c1;
        var 0..10: c2;
        var 0..10: cost;
        array [1..4] of var int: x:: output_array([1..4]) = [x0,x1,x2,x3];
        array [1..4] of var int: t:: output_array([1..4]) = [t0,t1,t2,t3];
        constraint jacop_weighted_subcircuits(x,t,[0,1,1,1,1,0,1,1,1,1,0,1,1,1,1,0],[c1,c2],cost,1);
        solve satisfy;
        """;
    // brute force: permutations whose circuits get different tours, node 0 in tour 1
    int[][] domains = new int[4][];
    Arrays.fill(domains, new int[] {1, 2, 3, 4});
    List<int[]> perms = new ArrayList<>();
    enumerateAll(0, new int[4], new boolean[4], perms);
    Set<String> expected = new TreeSet<>();
    for (int[] p : perms) {
      int[] cycle = new int[4];
      Arrays.fill(cycle, -1);
      int cycles = 0;
      for (int s = 0; s < 4; s++) {
        if (p[s] != s && cycle[s] < 0) {
          int v = s;
          do {
            cycle[v] = cycles;
            v = p[v];
          } while (v != s);
          cycles++;
        }
      }
      for (int assign = 0; assign < 4; assign++) {
        // cycle c gets tour 1 + ((assign >> c) & 1)
        if (cycles > 2
            || (cycles == 2 && (assign & 1) == ((assign >> 1) & 1))
            || assign >= 1 << cycles) {
          continue;
        }
        int[] t = new int[4];
        for (int i = 0; i < 4; i++) {
          t[i] = cycle[i] < 0 ? 0 : 1 + ((assign >> cycle[i]) & 1);
        }
        if (t[0] != 1) {
          continue;
        }
        int[] values = new int[4];
        for (int i = 0; i < 4; i++) {
          values[i] = p[i] + 1;
        }
        expected.add(
            "t = array1d(1..4, "
                + Arrays.toString(t)
                + "); x = array1d(1..4, "
                + Arrays.toString(values)
                + ");");
      }
    }
    assertEquals(expected, solutions(run(fzn, "-a")));
  }

  // all permutations of 0..n-1
  private static void enumerateAll(int i, int[] next, boolean[] used, List<int[]> out) {
    if (i == next.length) {
      out.add(next.clone());
      return;
    }
    for (int j = 0; j < next.length; j++) {
      if (!used[j]) {
        used[j] = true;
        next[i] = j;
        enumerateAll(i + 1, next, used, out);
        used[j] = false;
      }
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
