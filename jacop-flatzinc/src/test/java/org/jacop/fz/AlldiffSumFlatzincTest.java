/*
 * AlldiffSumFlatzincTest.java
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
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the AlldiffSum the FlatZinc front end posts next to a sum with unit coefficients over
 * variables that the all_different constraints make pairwise different: all solutions must match a
 * brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class AlldiffSumFlatzincTest {

  @TempDir Path tmp;

  /** The FlatZinc of a random model and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce, boolean detectable) {}

  // forms of the sum
  private static final int EQ_CONST = 0;
  private static final int LE_CONST = 1;
  private static final int EQ_VAR = 2;

  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(3);
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] = IntStream.rangeClosed(1, 6).filter(v -> random.nextInt(4) != 0).toArray();
      if (domains[i].length < 2) {
        domains[i] = new int[] {1 + random.nextInt(3), 4 + random.nextInt(3)};
      }
    }
    // all_different groups of at least three variables
    List<int[]> groups = new ArrayList<>();
    int groupCount = 1 + random.nextInt(3);
    for (int g = 0; g < groupCount; g++) {
      int[] group = IntStream.range(0, n).filter(i -> random.nextInt(3) != 0).toArray();
      if (group.length >= 3) {
        groups.add(group);
      }
    }
    // the summed variables, at least three
    int[] summed = IntStream.range(0, n).filter(i -> random.nextInt(4) != 0).toArray();
    if (summed.length < 3) {
      summed = new int[] {0, 1, 2};
    }
    int form = random.nextInt(3);
    int sign = random.nextBoolean() ? 1 : -1;
    int c = 6 + random.nextInt(4 * summed.length);
    int lo = 4 + random.nextInt(8);
    int hi = lo + random.nextInt(8);

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(set(domains[i])).append(": x").append(i).append(";\n");
    }
    if (form == EQ_VAR) {
      fzn.append("var ").append(lo).append("..").append(hi).append(": total:: output_var;\n");
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
    for (int[] group : groups) {
      List<String> names = new ArrayList<>();
      for (int i : group) {
        names.add("x" + i);
      }
      Collections.shuffle(names, random);
      fzn.append("constraint jacop_alldiff([").append(String.join(",", names)).append("]);\n");
    }
    List<String> terms = new ArrayList<>();
    for (int i : summed) {
      terms.add(sign + ":x" + i);
    }
    if (form == EQ_VAR) {
      terms.add(-sign + ":total");
    }
    Collections.shuffle(terms, random);
    StringBuilder coefs = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (String t : terms) {
      String[] p = t.split(":");
      coefs.append(coefs.isEmpty() ? "" : ",").append(p[0]);
      vars.append(vars.isEmpty() ? "" : ",").append(p[1]);
    }
    // sign * sum(x) - sign * total == 0, sign * sum(x) == sign * c or sign * sum(x) <= sign * c
    int rhs = form == EQ_VAR ? 0 : sign * c;
    fzn.append("constraint int_lin_")
        .append(form == LE_CONST ? "le" : "eq")
        .append("([")
        .append(coefs)
        .append("],[")
        .append(vars)
        .append("],")
        .append(rhs)
        .append(");\n");
    fzn.append("solve satisfy;\n");

    int[] sumIndex = summed;
    Set<String> expected = new TreeSet<>();
    enumerate(
        0,
        new int[n],
        domains,
        values -> {
          for (int[] group : groups) {
            if (Arrays.stream(group).map(i -> values[i]).distinct().count() != group.length) {
              return;
            }
          }
          int s = Arrays.stream(sumIndex).map(i -> values[i]).sum();
          String xOut = "x = array1d(1.." + n + ", " + Arrays.toString(values) + ");";
          if (form == EQ_VAR) {
            if (lo <= s && s <= hi) {
              expected.add("total = " + s + "; " + xOut);
            }
          } else if (form == LE_CONST ? sign * s <= rhs : sign * s == rhs) {
            expected.add(xOut);
          }
        });
    return new Model(fzn.toString(), expected, pairwiseCovered(summed, groups));
  }

  private static boolean pairwiseCovered(int[] summed, List<int[]> groups) {
    for (int a = 0; a < summed.length; a++) {
      for (int b = 0; b < a; b++) {
        int i = summed[a];
        int j = summed[b];
        boolean covered =
            groups.stream()
                .anyMatch(
                    g ->
                        Arrays.stream(g).anyMatch(v -> v == i)
                            && Arrays.stream(g).anyMatch(v -> v == j));
        if (!covered) {
          return false;
        }
      }
    }
    return true;
  }

  private interface Visitor {
    void visit(int[] values);
  }

  private static void enumerate(int i, int[] x, int[][] domains, Visitor visitor) {
    if (i == x.length) {
      visitor.visit(x.clone());
      return;
    }
    for (int v : domains[i]) {
      x[i] = v;
      enumerate(i + 1, x, domains, visitor);
    }
  }

  private static String set(int[] values) {
    StringBuilder s = new StringBuilder("{");
    for (int k = 0; k < values.length; k++) {
      s.append(k == 0 ? "" : ",").append(values[k]);
    }
    return s.append('}').toString();
  }

  @Test
  void alldiffSumKeepsAllSolutions() throws IOException {
    Random random = new Random(13);
    int detected = 0;
    for (int trial = 0; trial < 400; trial++) {
      Model model = randomModel(random);
      String out = run(model.fzn(), "-a", "-debug");
      boolean found = out.contains("AlldiffSum");
      if (found) {
        detected++;
      }
      // a model found infeasible while it is read never reaches the detection
      if (model.detectable() && !model.bruteForce().isEmpty()) {
        assertTrue(found, "not detected, trial " + trial + "\n" + model.fzn());
      } else if (!model.detectable()) {
        assertFalse(found, "detected, trial " + trial + "\n" + model.fzn());
      }
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
    assertTrue(detected > 80, "detected " + detected);
  }

  @Test
  void killerCageGetsAlldiffSumAndCanBeTurnedOff() throws IOException {
    // a cage x0, x1, x2 whose pairs are each in an all_different (a row, a column, a box), none
    // of which holds the whole cage
    String fzn =
        """
        var 1..4: x0;
        var 1..4: x1;
        var 1..4: x2;
        var 1..4: x3;
        var 1..4: x4;
        array [1..5] of var int: x:: output_array([1..5]) = [x0,x1,x2,x3,x4];
        constraint jacop_alldiff([x0,x1,x3]);
        constraint jacop_alldiff([x1,x2,x4]);
        constraint jacop_alldiff([x2,x0,x4]);
        constraint int_lin_eq([1,1,1],[x0,x1,x2],6);
        solve satisfy;
        """;
    String out = run(fzn, "-a", "-debug");
    assertTrue(out.contains("AlldiffSum"));
    String property = "org.jacop.fz.alldiffSum";
    System.setProperty(property, "false");
    try {
      String off = run(fzn, "-a", "-debug");
      assertFalse(off.contains("AlldiffSum"));
      assertEquals(solutions(off), solutions(out));
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
