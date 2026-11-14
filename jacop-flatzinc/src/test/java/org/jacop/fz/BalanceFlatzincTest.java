/*
 * BalanceFlatzincTest.java
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
 * Checks the detection of balancing sums (sums of |a * x[i] - b| or (a * x[i] - b)^2 over variables
 * with a fixed sum) in the FlatZinc front end, which posts a redundant Deviation or Spread, and the
 * jacop_deviation and jacop_spread constraints: all solutions must match a brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class BalanceFlatzincTest {

  @TempDir Path tmp;

  /** The FlatZinc of a random balancing sum and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce, boolean detectable) {}

  // forms of the sum of the terms
  private static final int EQ_VAR = 0;
  private static final int EQ_SHIFTED = 1;
  private static final int LE_CONST = 2;

  private static Model randomModel(Random random) {
    int n = 2 + random.nextInt(3);
    boolean squares = random.nextBoolean();
    boolean pow = random.nextBoolean();
    // terms over x itself (a = 1, b = 0) or over a defined a * x - b
    boolean direct = random.nextInt(4) == 0;
    int a = direct ? 1 : (random.nextBoolean() ? n : 1 + random.nextInt(3));
    int b = direct ? 0 : -3 + random.nextInt(14);
    int form = random.nextInt(3);
    // the sum of x is missing, or over a different set of variables
    int sumStyle = random.nextInt(6);
    boolean mixed = random.nextInt(8) == 0;

    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] = IntStream.rangeClosed(-1, 5).filter(v -> random.nextInt(4) != 0).toArray();
      if (domains[i].length == 0) {
        domains[i] = new int[] {random.nextInt(5)};
      }
    }
    int s = random.nextInt(4 * n);
    int lo = random.nextInt(squares ? 30 : 10);
    int hi = lo + random.nextInt(squares ? 150 : 30);
    int shift = random.nextInt(5) - 2;
    int bound = random.nextInt(squares ? 200 : 40);

    StringBuilder fzn = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(set(domains[i])).append(": x").append(i).append(";\n");
      xs.append(i == 0 ? "" : ",").append('x').append(i);
    }
    for (int i = 0; i < n; i++) {
      if (!direct) {
        fzn.append("var int: t").append(i).append(";\n");
      }
      fzn.append("var int: g").append(i).append(";\n");
    }
    boolean hasTotal = form != LE_CONST;
    if (hasTotal) {
      fzn.append("var ").append(lo).append("..").append(hi).append(": total:: output_var;\n");
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");

    for (int i = 0; i < n; i++) {
      String t = direct ? "x" + i : "t" + i;
      if (!direct) {
        // t = a * x - b, or t = b - a * x
        if (random.nextBoolean()) {
          fzn.append("constraint int_lin_eq([" + a + ",-1],[x" + i + ",t" + i + "]," + b + ");\n");
        } else {
          fzn.append("constraint int_lin_eq([1," + a + "],[t" + i + ",x" + i + "]," + b + ");\n");
        }
      }
      // one term of another kind is not a balancing sum
      boolean square = mixed && i == 0 ? !squares : squares;
      if (!square) {
        fzn.append("constraint int_abs(" + t + ",g" + i + ");\n");
      } else if (pow) {
        fzn.append("constraint int_pow(" + t + ",2,g" + i + ");\n");
      } else {
        fzn.append("constraint int_times(" + t + "," + t + ",g" + i + ");\n");
      }
    }

    // the sum of the terms, in random order
    List<String> terms = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      terms.add("1:g" + i);
    }
    if (hasTotal) {
      terms.add("-1:total");
    }
    Collections.shuffle(terms, random);
    StringBuilder coefs = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (String term : terms) {
      String[] p = term.split(":");
      coefs.append(coefs.isEmpty() ? "" : ",").append(p[0]);
      vars.append(vars.isEmpty() ? "" : ",").append(p[1]);
    }
    int rhs = form == EQ_VAR ? 0 : form == EQ_SHIFTED ? shift : bound;
    fzn.append("constraint int_lin_")
        .append(form == LE_CONST ? "le" : "eq")
        .append("([")
        .append(coefs)
        .append("],[")
        .append(vars)
        .append("],")
        .append(rhs)
        .append(");\n");

    // the sum of x: all of x (with coefficients 1 or -1), missing, or without x[n-1]
    int summed = sumStyle == 0 ? 0 : sumStyle == 1 ? n - 1 : n;
    int sign = random.nextBoolean() ? 1 : -1;
    int partial = 0;
    if (summed > 0) {
      StringBuilder ones = new StringBuilder();
      StringBuilder over = new StringBuilder();
      for (int i = 0; i < summed; i++) {
        ones.append(i == 0 ? "" : ",").append(sign);
        over.append(i == 0 ? "" : ",").append('x').append(i);
      }
      partial = summed == n ? s : random.nextInt(4 * n);
      fzn.append("constraint int_lin_eq([" + ones + "],[" + over + "]," + sign * partial + ");\n");
    }
    fzn.append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] x = new int[n];
    int count = summed;
    int target = partial;
    enumerate(
        0,
        x,
        domains,
        values -> {
          if (count > 0 && IntStream.of(values).limit(count).sum() != target) {
            return;
          }
          long cost = 0;
          for (int i = 0; i < n; i++) {
            long e = (long) a * values[i] - b;
            boolean square = mixed && i == 0 ? !squares : squares;
            cost += square ? e * e : Math.abs(e);
          }
          String xOut = "x = array1d(1.." + n + ", " + Arrays.toString(values) + ");";
          if (hasTotal) {
            long total = cost - rhs;
            if (total >= lo && total <= hi) {
              expected.add("total = " + total + "; " + xOut);
            }
          } else if (cost <= rhs) {
            expected.add(xOut);
          }
        });
    return new Model(fzn.toString(), expected, summed == n && !mixed);
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
  void detectedBalanceKeepsAllSolutions() throws IOException {
    Random random = new Random(13);
    int detected = 0;
    for (int trial = 0; trial < 400; trial++) {
      Model model = randomModel(random);
      String out = run(model.fzn(), "-a", "-debug");
      boolean found = out.contains("redundant Deviation") || out.contains("redundant Spread");
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
    assertTrue(detected > 100, "detected " + detected);
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    String fzn =
        """
        var 0..10: x0;
        var 0..10: x1;
        var 0..10: x2;
        var int: t0;
        var int: t1;
        var int: t2;
        var int: g0;
        var int: g1;
        var int: g2;
        var 0..100: d:: output_var;
        array [1..3] of var int: x:: output_array([1..3]) = [x0,x1,x2];
        constraint int_lin_eq([3,-1],[x0,t0],10);
        constraint int_lin_eq([3,-1],[x1,t1],10);
        constraint int_lin_eq([3,-1],[x2,t2],10);
        constraint int_abs(t0,g0);
        constraint int_abs(t1,g1);
        constraint int_abs(t2,g2);
        constraint int_lin_eq([1,1,1,-1],[g0,g1,g2,d],0);
        constraint int_lin_eq([1,1,1],[x0,x1,x2],10);
        solve minimize d;
        """;
    String out = run(fzn, "-debug");
    assertTrue(out.contains("redundant Deviation"));
    // 3, 3, 4: |9 - 10| + |9 - 10| + |12 - 10| = 4, proved optimal
    assertTrue(out.contains("d = 4;"), out);
    String property = "org.jacop.fz.balance";
    System.setProperty(property, "false");
    try {
      assertFalse(run(fzn, "-debug").contains("redundant Deviation"));
    } finally {
      System.clearProperty(property);
    }
  }

  @Test
  void jacopDeviationAndSpreadMatchBruteForce() throws IOException {
    Random random = new Random(14);
    for (int trial = 0; trial < 200; trial++) {
      int n = 1 + random.nextInt(4);
      boolean squares = random.nextBoolean();
      int a = 1 + random.nextInt(n + 1);
      int b = -2 + random.nextInt(12);
      int s = random.nextInt(4 * n);
      int[][] domains = new int[n][];
      StringBuilder fzn = new StringBuilder();
      StringBuilder xs = new StringBuilder();
      for (int i = 0; i < n; i++) {
        domains[i] = IntStream.rangeClosed(-1, 5).filter(v -> random.nextInt(4) != 0).toArray();
        if (domains[i].length == 0) {
          domains[i] = new int[] {random.nextInt(5)};
        }
        fzn.append("var ").append(set(domains[i])).append(": x").append(i).append(";\n");
        xs.append(i == 0 ? "" : ",").append('x').append(i);
      }
      int lo = random.nextInt(squares ? 40 : 10);
      int hi = lo + random.nextInt(squares ? 200 : 30);
      fzn.append("var ").append(lo).append("..").append(hi).append(": d:: output_var;\n");
      fzn.append("array [1..")
          .append(n)
          .append("] of var int: x:: output_array([1..")
          .append(n)
          .append("]) = [")
          .append(xs)
          .append("];\n");
      fzn.append("constraint jacop_")
          .append(squares ? "spread" : "deviation")
          .append("(x,")
          .append(a)
          .append(',')
          .append(b)
          .append(',')
          .append(s)
          .append(",d);\n");
      fzn.append("solve satisfy;\n");

      Set<String> expected = new TreeSet<>();
      enumerate(
          0,
          new int[n],
          domains,
          values -> {
            if (IntStream.of(values).sum() != s) {
              return;
            }
            long cost = 0;
            for (int v : values) {
              long e = (long) a * v - b;
              cost += squares ? e * e : Math.abs(e);
            }
            if (cost >= lo && cost <= hi) {
              expected.add(
                  "d = " + cost + "; x = array1d(1.." + n + ", " + Arrays.toString(values) + ");");
            }
          });
      assertEquals(expected, solutions(run(fzn.toString(), "-a")), "trial " + trial + "\n" + fzn);
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
