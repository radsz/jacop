/*
 * PermutationElementSumsFlatzincTest.java
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
import java.util.Arrays;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the sums of element constraints indexed by the variables of an all_different constraint
 * ({@code org.jacop.fz.constraints.PermutationElementSums}): small permutation flow shops keep
 * their optimum (brute force over the permutations), and random models with permutations,
 * injections and indices without elements keep all their solutions.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class PermutationElementSumsFlatzincTest {

  @TempDir Path tmp;

  private static final String SUMS = "org.jacop.fz.permutationElementSums";

  // the permutation flow shop of pfsp.mzn (osolpro gap-sources/scheduling) as FlatZinc: perm,
  // d[i,k] = p[i, perm[k]], s[i,k] >= s[i,k-1] + d[i,k-1], s[i,k] >= s[i-1,k] + d[i-1,k]
  private static String flowShop(int[][] p) {
    int m = p.length;
    int n = p[0].length;
    int horizon = Arrays.stream(p).flatMapToInt(Arrays::stream).sum();
    StringBuilder fzn = new StringBuilder();
    StringBuilder perm = new StringBuilder();
    for (int k = 0; k < n; k++) {
      fzn.append("var 1..").append(n).append(": perm_").append(k).append(";\n");
      perm.append(k == 0 ? "" : ",").append("perm_").append(k);
    }
    for (int i = 0; i < m; i++) {
      for (int k = 0; k < n; k++) {
        fzn.append("var 0..").append(horizon).append(": s_").append(i).append('_').append(k);
        fzn.append(";\nvar 1..99: d_").append(i).append('_').append(k).append(";\n");
      }
    }
    fzn.append("var 0..").append(horizon).append(": makespan:: output_var;\n");
    fzn.append("array [1..").append(n).append("] of var int: perm:: output_array([1..");
    fzn.append(n).append("]) = [").append(perm).append("];\n");
    fzn.append("constraint jacop_alldiff([").append(perm).append("]);\n");
    for (int i = 0; i < m; i++) {
      String row = Arrays.toString(p[i]).replace(" ", "");
      for (int k = 0; k < n; k++) {
        fzn.append("constraint array_int_element(perm_").append(k).append(',').append(row);
        fzn.append(",d_").append(i).append('_').append(k).append(");\n");
        if (k > 0) {
          lessEqual(fzn, "s_" + i + "_" + (k - 1), "d_" + i + "_" + (k - 1), "s_" + i + "_" + k);
        }
        if (i > 0) {
          lessEqual(fzn, "s_" + (i - 1) + "_" + k, "d_" + (i - 1) + "_" + k, "s_" + i + "_" + k);
        }
      }
    }
    fzn.append("constraint int_eq(s_0_0,0);\n");
    String last = (m - 1) + "_" + (n - 1);
    fzn.append("constraint int_lin_eq([1,1,-1],[s_").append(last).append(",d_").append(last);
    fzn.append(",makespan],0);\n");
    return fzn.append("solve minimize makespan;\n").toString();
  }

  // a + b <= c
  private static void lessEqual(StringBuilder fzn, String a, String b, String c) {
    fzn.append("constraint int_lin_le([1,1,-1],[").append(a).append(',').append(b).append(',');
    fzn.append(c).append("],0);\n");
  }

  // the makespan of the best permutation
  private static int bestMakespan(int[][] p) {
    int n = p[0].length;
    int[] perm = new int[n];
    for (int j = 0; j < n; j++) {
      perm[j] = j;
    }
    return best(p, perm, 0);
  }

  private static int best(int[][] p, int[] perm, int k) {
    if (k == perm.length) {
      int[] c = new int[p.length];
      for (int j : perm) {
        for (int i = 0; i < p.length; i++) {
          c[i] = Math.max(c[i], i > 0 ? c[i - 1] : 0) + p[i][j];
        }
      }
      return c[p.length - 1];
    }
    int b = Integer.MAX_VALUE;
    for (int t = k; t < perm.length; t++) {
      swap(perm, k, t);
      b = Math.min(b, best(p, perm, k + 1));
      swap(perm, k, t);
    }
    return b;
  }

  private static void swap(int[] a, int i, int j) {
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
  }

  @Test
  void flowShopsKeepTheirOptimum() throws IOException {
    Random random = new Random(3);
    for (int trial = 0; trial < 8; trial++) {
      int m = 2 + random.nextInt(3);
      int n = 3 + random.nextInt(3);
      int[][] p = new int[m][n];
      for (int[] row : p) {
        for (int j = 0; j < n; j++) {
          row[j] = 1 + random.nextInt(30);
        }
      }
      int expected = bestMakespan(p);
      for (String mode : new String[] {"", "-f"}) {
        String out =
            mode.isEmpty()
                ? run(flowShop(p), "-s", "--search-statistics")
                : run(flowShop(p), "-s", "--search-statistics", mode);
        assertTrue(out.contains("=========="), "trial " + trial + " " + mode + "\n" + out);
        assertEquals(expected, makespan(out), "trial " + trial + " " + mode + "\n" + out);
        assertTrue(
            out.contains("%%%mzn-stat: permutationElementSums=" + m + "\n"),
            "trial " + trial + " " + mode + "\n" + out);
      }
    }
  }

  @Test
  void randomElementsKeepAllSolutions() throws IOException {
    Random random = new Random(11);
    int fired = 0;
    for (int trial = 0; trial < 100; trial++) {
      String fzn = randomModel(random);
      Set<String> off;
      System.setProperty(SUMS, "false");
      try {
        off = solutions(run(fzn, "-a"));
      } finally {
        System.clearProperty(SUMS);
      }
      String on = run(fzn, "-a", "--search-statistics");
      if (on.contains("permutationElementSums=")) {
        fired++;
      }
      assertEquals(off, solutions(on), "trial " + trial + "\n" + fzn);
    }
    assertTrue(fired > 30, "fired " + fired);
  }

  // n indices x_k all different over first..first+u-1 (u >= n, holes in some domains), values
  // y_k = c[x_k] for most k, some with a second array on the same index, and a linear constraint
  // on the values
  private static String randomModel(Random random) {
    int n = 3 + random.nextInt(3);
    int u = n + random.nextInt(2);
    int first = random.nextInt(2);
    int[] c = new int[u];
    int[] c2 = new int[u];
    for (int j = 0; j < u; j++) {
      c[j] = random.nextInt(9) - 2;
      c2[j] = random.nextInt(5);
    }
    StringBuilder fzn = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    StringBuilder ys = new StringBuilder();
    StringBuilder ones = new StringBuilder();
    for (int k = 0; k < n; k++) {
      fzn.append("var ").append(first).append("..").append(first + u - 1).append(": x_").append(k);
      fzn.append(";\nvar -2..6: y_").append(k).append(";\nvar 0..4: z_").append(k);
      fzn.append(";\n");
      xs.append(k == 0 ? "" : ",").append("x_").append(k);
      ys.append(k == 0 ? "" : ",").append("y_").append(k);
      ones.append(k == 0 ? "" : ",").append(1 + random.nextInt(2));
    }
    fzn.append("array [1..").append(n).append("] of var int: x:: output_array([1..").append(n);
    fzn.append("]) = [").append(xs).append("];\n");
    fzn.append("array [1..").append(n).append("] of var int: y:: output_array([1..").append(n);
    fzn.append("]) = [").append(ys).append("];\n");
    fzn.append("constraint jacop_alldiff([").append(xs).append("]);\n");
    String array = Arrays.toString(c).replace(" ", "");
    String array2 = Arrays.toString(c2).replace(" ", "");
    for (int k = 0; k < n; k++) {
      if (random.nextInt(6) == 0) {
        fzn.append("constraint int_ne(x_").append(k).append(',');
        fzn.append(first + random.nextInt(u)).append(");\n");
      }
      if (random.nextInt(8) == 0) {
        continue;
      }
      element(fzn, "x_" + k, array, "y_" + k, first);
      if (random.nextInt(3) == 0) {
        element(fzn, "x_" + k, array2, "z_" + k, first);
      }
    }
    int sum = random.nextInt(3 * n) + n;
    fzn.append("constraint int_lin_le([").append(ones).append("],[").append(ys).append("],");
    fzn.append(sum).append(");\n");
    return fzn.append("solve satisfy;\n").toString();
  }

  private static void element(StringBuilder fzn, String x, String array, String y, int first) {
    if (first == 1) {
      fzn.append("constraint array_int_element(").append(x).append(',').append(array);
      fzn.append(',').append(y).append(");\n");
    } else {
      fzn.append("constraint jacop_array_var_int_element_nonshifted(").append(x).append(',');
      fzn.append(array).append(',').append(y).append(",0);\n");
    }
  }

  private static int makespan(String out) {
    Matcher m = Pattern.compile("makespan = (\\d+);").matcher(out);
    int last = -1;
    while (m.find()) {
      last = Integer.parseInt(m.group(1));
    }
    return last;
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
