/*
 * IncreasingSumFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the detection of sums over ordered variables in the FlatZinc front end, which posts a
 * redundant IncreasingSum: all solutions must match a brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class IncreasingSumFlatzincTest {

  @TempDir Path tmp;

  /** The FlatZinc of a random ordered sum and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce, boolean detectable) {}

  // forms of the sum
  private static final int EQ_VAR = 0;
  private static final int EQ_SHIFTED = 1;
  private static final int EQ_CONST = 2;
  private static final int LE_CONST = 3;
  private static final int GE_CONST = 4;

  private static Model randomModel(Random random) {
    int n = 2 + random.nextInt(4);
    boolean strict = random.nextInt(3) == 0;
    boolean decreasing = random.nextBoolean();
    int orderStyle = random.nextInt(3);
    int form = random.nextInt(5);
    int sign = random.nextBoolean() ? 1 : -1;
    // a chain with a missing link is not an order on all summed variables
    int broken = random.nextInt(6) == 0 ? random.nextInt(n - 1) : -1;

    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] =
          java.util.stream.IntStream.rangeClosed(-1, 5)
              .filter(v -> random.nextInt(4) != 0)
              .toArray();
      if (domains[i].length == 0) {
        domains[i] = new int[] {random.nextInt(5)};
      }
    }
    int lo = -2 + random.nextInt(8);
    int hi = lo + random.nextInt(4 * n);
    int c = random.nextInt(4 * n) - 2;
    int shift = random.nextInt(5) - 2;

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(set(domains[i])).append(": x").append(i).append(";\n");
    }
    boolean hasTotal = form == EQ_VAR || form == EQ_SHIFTED;
    if (hasTotal) {
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

    // the order x0 <= x1 <= ... (or >= when decreasing)
    if (orderStyle == 0 && broken < 0) {
      fzn.append("constraint jacop_")
          .append(strict ? "strictly_" : "")
          .append(decreasing ? "decreasing" : "increasing")
          .append("(x);\n");
    } else {
      for (int i = 0; i + 1 < n; i++) {
        if (i == broken) {
          continue;
        }
        String a = "x" + (decreasing ? i + 1 : i);
        String b = "x" + (decreasing ? i : i + 1);
        if (orderStyle == 1) {
          fzn.append("constraint int_")
              .append(strict ? "lt" : "le")
              .append('(')
              .append(a)
              .append(',')
              .append(b)
              .append(");\n");
        } else {
          // k * (a - b) <= -k for a < b, or a rhs in [0, k) for a <= b
          int k = 1 + random.nextInt(3);
          int rhs = strict ? -k : random.nextInt(k);
          boolean flip = random.nextBoolean();
          fzn.append("constraint int_lin_le([")
              .append(flip ? -k : k)
              .append(',')
              .append(flip ? k : -k)
              .append("],[")
              .append(flip ? b : a)
              .append(',')
              .append(flip ? a : b)
              .append("],")
              .append(rhs)
              .append(");\n");
        }
      }
    }

    // the sum, over the variables in random order
    List<String> terms = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      terms.add(sign + ":x" + i);
    }
    if (hasTotal) {
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
    int rhs =
        switch (form) {
          case EQ_VAR -> 0;
          case EQ_SHIFTED -> sign * shift;
          case EQ_CONST, LE_CONST -> sign * c;
          default -> -sign * c;
        };
    // sign * sum(x) <= rhs: for sign -1 a lower bound on the sum
    boolean le = form == LE_CONST || form == GE_CONST;
    fzn.append("constraint int_lin_")
        .append(le ? "le" : "eq")
        .append("([")
        .append(coefs)
        .append("],[")
        .append(vars)
        .append("],")
        .append(rhs)
        .append(");\n");
    fzn.append("solve satisfy;\n");

    // sign * sum(x) - sign * total = rhs, or sign * sum(x) <= rhs
    Set<String> expected = new TreeSet<>();
    int[] x = new int[n];
    enumerate(
        0,
        x,
        domains,
        values -> {
          for (int i = 0; i + 1 < n; i++) {
            if (i == broken) {
              continue;
            }
            int step = decreasing ? values[i] - values[i + 1] : values[i + 1] - values[i];
            if (strict ? step <= 0 : step < 0) {
              return;
            }
          }
          int s = Arrays.stream(values).sum();
          String xOut = "x = array1d(1.." + n + ", " + Arrays.toString(values) + ");";
          if (hasTotal) {
            for (int t = lo; t <= hi; t++) {
              if (sign * s - sign * t == rhs) {
                expected.add("total = " + t + "; " + xOut);
              }
            }
          } else if (le ? sign * s <= rhs : sign * s == rhs) {
            expected.add(xOut);
          }
        });
    return new Model(fzn.toString(), expected, broken < 0 && n >= (hasTotal ? 2 : 3));
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
  void detectedIncreasingSumKeepsAllSolutions() throws IOException {
    Random random = new Random(11);
    int detected = 0;
    for (int trial = 0; trial < 400; trial++) {
      Model model = randomModel(random);
      String out = run(model.fzn(), "-a", "-debug");
      boolean found = out.contains("IncreasingSum");
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
    assertTrue(detected > 150, "detected " + detected);
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    String fzn =
        """
        var 0..10: x0;
        var 0..10: x1;
        var 0..10: x2;
        array [1..3] of var int: x:: output_array([1..3]) = [x0,x1,x2];
        constraint int_le(x0,x1);
        constraint int_le(x1,x2);
        constraint int_lin_eq([1,1,1],[x0,x1,x2],6);
        solve satisfy;
        """;
    assertTrue(run(fzn, "-a", "-debug").contains("IncreasingSum"));
    String property = "org.jacop.fz.increasingSum";
    System.setProperty(property, "false");
    try {
      assertFalse(run(fzn, "-a", "-debug").contains("IncreasingSum"));
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
