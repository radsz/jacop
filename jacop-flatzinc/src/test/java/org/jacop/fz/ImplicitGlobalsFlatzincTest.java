/*
 * ImplicitGlobalsFlatzincTest.java
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
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Predicate;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the detection of hand-written globals in the FlatZinc front end: counts written as sums of
 * reified equalities, which get a redundant GCC, and cliques of disequalities, possibly with
 * offsets, which are replaced by an all-different. On random models all solutions must match a
 * brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class ImplicitGlobalsFlatzincTest {

  @TempDir Path tmp;

  /** The FlatZinc of a random model and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce) {}

  // values: x0..x(n-1), then the counters y0..y(m-1)
  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(4);
    int maxValue = 1 + random.nextInt(n == 6 ? 2 : 3);
    int m = random.nextInt(3);
    int maxCounter = 1 + random.nextInt(2);
    StringBuilder fzn = new StringBuilder();
    StringBuilder constraints = new StringBuilder();
    List<Predicate<int[]>> checks = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..").append(maxValue).append(": x").append(i).append(";\n");
    }
    for (int k = 0; k < m; k++) {
      fzn.append("var 0..").append(maxCounter).append(": y").append(k).append(":: output_var;\n");
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(names("x", n))
        .append("];\n");

    // one literal b <-> x = v for each pair used, with its 0/1 integer
    Map<String, String> literals = new LinkedHashMap<>();
    int counts = random.nextInt(6);
    for (int c = 0; c < counts; c++) {
      int v = random.nextInt(maxValue + 1);
      // counts over all variables, which can share a GCC, or over some of them
      boolean all = random.nextBoolean();
      List<Integer> xs = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        if (all || random.nextInt(4) != 0) {
          xs.add(i);
        }
      }
      if (xs.size() < 2) {
        continue;
      }
      int a = random.nextBoolean() ? 1 : random.nextBoolean() ? -1 : 2;
      StringBuilder coefs = new StringBuilder();
      StringBuilder vars = new StringBuilder();
      for (int i : xs) {
        String key = i + "_" + v;
        String lit = literals.computeIfAbsent(key, k -> literal(fzn, constraints, "x" + i, v, k));
        coefs.append(coefs.isEmpty() ? "" : ",").append(a);
        vars.append(vars.isEmpty() ? "" : ",").append(lit);
      }
      // a * count(xs, v) + w * y rel rhs, or a * count(xs, v) rel rhs
      int y = m > 0 && random.nextInt(3) != 0 ? random.nextInt(m) : -1;
      int w = y < 0 ? 0 : random.nextBoolean() ? -a : random.nextInt(5) - 2;
      if (y >= 0 && w != 0) {
        coefs.append(',').append(w);
        vars.append(",y").append(y);
      }
      boolean equation = random.nextBoolean();
      int rhs =
          random.nextInt(3) * (random.nextBoolean() ? 1 : a) - (random.nextInt(3) == 0 ? 1 : 0);
      constraints
          .append("constraint int_lin_")
          .append(equation ? "eq" : "le")
          .append("([")
          .append(coefs)
          .append("],[")
          .append(vars)
          .append("],")
          .append(rhs)
          .append(");\n");
      int yy = y;
      int ww = w;
      checks.add(
          s -> {
            int count = 0;
            for (int i : xs) {
              if (s[i] == v) {
                count++;
              }
            }
            int lhs = a * count + (yy >= 0 ? ww * s[n + yy] : 0);
            return equation ? lhs == rhs : lhs <= rhs;
          });
    }

    // disequalities: random ones and cliques with offsets, x[i] + o[i] all different
    int cliques = random.nextInt(3);
    for (int c = 0; c < cliques; c++) {
      List<Integer> xs = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        if (random.nextInt(5) != 0) {
          xs.add(i);
        }
      }
      boolean shifted = random.nextBoolean();
      int[] o = new int[n];
      for (int i : xs) {
        o[i] = shifted ? random.nextInt(3) - 1 : 0;
      }
      for (int p = 0; p < xs.size(); p++) {
        for (int q = p + 1; q < xs.size(); q++) {
          if (random.nextInt(20) == 0) {
            continue;
          }
          int i = xs.get(p);
          int j = xs.get(q);
          constraints.append(disequality(random, i, j, o[j] - o[i]));
          int d = o[j] - o[i];
          checks.add(s -> s[i] - s[j] != d);
        }
      }
    }
    int extra = random.nextInt(3);
    for (int k = 0; k < extra; k++) {
      int i = random.nextInt(n);
      int j = random.nextInt(n);
      if (i != j) {
        int d = random.nextInt(3) - 1;
        constraints.append(disequality(random, i, j, d));
        checks.add(s -> s[i] - s[j] != d);
      }
    }

    fzn.append(constraints);
    fzn.append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] s = new int[n + m];
    enumerate(0, s, n, maxValue, maxCounter, checks, expected);
    return new Model(fzn.toString(), expected);
  }

  // b <-> x = v and its 0/1 integer i, named by the key; returns the integer's name
  private static String literal(
      StringBuilder decls, StringBuilder constraints, String x, int v, String key) {
    decls.append("var bool: b").append(key).append(";\nvar 0..1: i").append(key).append(";\n");
    constraints
        .append("constraint int_eq_reif(")
        .append(x)
        .append(',')
        .append(v)
        .append(",b")
        .append(key)
        .append(");\nconstraint bool2int(b")
        .append(key)
        .append(",i")
        .append(key)
        .append(");\n");
    return "i" + key;
  }

  // x[i] - x[j] != d
  private static String disequality(Random random, int i, int j, int d) {
    if (d == 0 && random.nextBoolean()) {
      return "constraint int_ne(x" + i + ",x" + j + ");\n";
    }
    int k = 1 + random.nextInt(2);
    if (random.nextBoolean()) {
      return "constraint int_lin_ne(["
          + k
          + ","
          + -k
          + "],[x"
          + i
          + ",x"
          + j
          + "],"
          + k * d
          + ");\n";
    }
    return "constraint int_lin_ne([" + -k + "," + k + "],[x" + j + ",x" + i + "]," + k * d + ");\n";
  }

  private static String names(String prefix, int n) {
    StringBuilder s = new StringBuilder();
    for (int i = 0; i < n; i++) {
      s.append(i == 0 ? "" : ",").append(prefix).append(i);
    }
    return s.toString();
  }

  private static void enumerate(
      int pos,
      int[] s,
      int n,
      int maxValue,
      int maxCounter,
      List<Predicate<int[]>> checks,
      Set<String> out) {
    if (pos == s.length) {
      for (Predicate<int[]> c : checks) {
        if (!c.test(s)) {
          return;
        }
      }
      TreeSet<String> lines = new TreeSet<>();
      lines.add("x = array1d(1.." + n + ", " + Arrays.toString(Arrays.copyOf(s, n)) + ");");
      for (int k = n; k < s.length; k++) {
        lines.add("y" + (k - n) + " = " + s[k] + ";");
      }
      out.add(String.join(" ", lines));
      return;
    }
    int hi = pos < n ? maxValue : maxCounter;
    for (int v = 0; v <= hi; v++) {
      s[pos] = v;
      enumerate(pos + 1, s, n, maxValue, maxCounter, checks, out);
    }
  }

  @Test
  void detectedGlobalsKeepAllSolutions() throws IOException {
    Random random = new Random(7);
    int gcc = 0;
    int alldifferent = 0;
    int trials = Integer.getInteger("implicitGlobals.trials", 600);
    for (int trial = 0; trial < trials; trial++) {
      Model model = randomModel(random);
      String out = run(model.fzn(), "-a", "-debug");
      if (out.contains("% redundant GCC")) {
        gcc++;
      }
      if (out.contains("% alldifferent on")) {
        alldifferent++;
      }
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
    assertTrue(gcc > trials / 20, "GCCs " + gcc);
    assertTrue(alldifferent > trials / 20, "alldifferents " + alldifferent);
  }

  // magic sequence of length n written by hand: s[v] = sum(i)(bool2int(s[i] = v))
  private static String magicSequence(int n) {
    StringBuilder fzn = new StringBuilder();
    StringBuilder constraints = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..").append(n - 1).append(": s").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: s:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(names("s", n))
        .append("];\n");
    for (int v = 0; v < n; v++) {
      StringBuilder coefs = new StringBuilder("1");
      StringBuilder vars = new StringBuilder("s" + v);
      for (int i = 0; i < n; i++) {
        String k = i + "_" + v;
        literal(fzn, constraints, "s" + i, v, k);
        coefs.append(",-1");
        vars.append(",i").append(k);
      }
      constraints
          .append("constraint int_lin_eq([")
          .append(coefs)
          .append("],[")
          .append(vars)
          .append("],0);\n");
    }
    fzn.append(constraints);
    fzn.append("solve :: int_search(s,input_order,indomain_min,complete) satisfy;\n");
    return fzn.toString();
  }

  @Test
  void magicSequenceGetsOneGcc() throws IOException {
    String out = run(magicSequence(12), "-a", "-debug", "-s");
    assertTrue(out.contains("% redundant GCC on 12 variables, 12 counted values"), out);
    assertEquals(
        Set.of("s = array1d(1..12, [8, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]);"), solutions(out));
  }

  // n-queens with the rows and both diagonals written as pairwise disequalities
  private static String queens(int n) {
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var 1..").append(n).append(": q").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: q:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(names("q", n))
        .append("];\n");
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        fzn.append("constraint int_ne(q").append(i).append(",q").append(j).append(");\n");
        fzn.append("constraint int_lin_ne([1,-1],[q")
            .append(i)
            .append(",q")
            .append(j)
            .append("],")
            .append(j - i)
            .append(");\n");
        fzn.append("constraint int_lin_ne([1,-1],[q")
            .append(i)
            .append(",q")
            .append(j)
            .append("],")
            .append(i - j)
            .append(");\n");
      }
    }
    fzn.append("solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void queensGetRowAndDiagonalAlldifferents() throws IOException {
    String out = run(queens(8), "-a", "-debug");
    assertEquals(3, out.split("% alldifferent on 8 variables", -1).length - 1, "three cliques");
    assertTrue(out.contains(" 84 disequalities replaced"), out);
    assertEquals(92, solutions(out).size());
  }

  private static String nodes(String out) {
    return out.lines().filter(l -> l.startsWith("%%%mzn-stat: nodes=")).findFirst().orElse(out);
  }

  // the all-different counts as the disequalities it replaces in the static degree, so the
  // most_constrained search of eyedrop_optimize2 is the one with them kept (without the degrees it
  // took 795,270 nodes instead of 4,373)
  @Test
  void replacedDisequalitiesKeepTheSearchThatCountsConstraints() throws IOException {
    String model =
        Files.readString(
            Path.of("../jacop-benchmarks/src/test/fz/upTo5sec/eyedrop_optimize2")
                .resolve("eyedrop_optimize2.fzn"));
    String out = run(model, "-s", "-debug");
    assertTrue(out.contains(" 15 disequalities replaced"), out);
    System.setProperty("org.jacop.fz.alldifferent", "redundant");
    String kept;
    try {
      kept = run(model, "-s", "-debug");
    } finally {
      System.clearProperty("org.jacop.fz.alldifferent");
    }
    assertTrue(kept.contains(" 0 disequalities replaced"), kept);
    assertEquals(solutions(kept), solutions(out));
    assertEquals(nodes(kept), nodes(out));
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    System.setProperty("org.jacop.fz.cardinality", "false");
    System.setProperty("org.jacop.fz.alldifferent", "false");
    try {
      String out = run(magicSequence(8), "-debug");
      assertFalse(out.contains("% redundant GCC"));
      out = run(queens(6), "-a", "-debug");
      assertFalse(out.contains("% alldifferent on"));
      assertEquals(4, solutions(out).size());
    } finally {
      System.clearProperty("org.jacop.fz.cardinality");
      System.clearProperty("org.jacop.fz.alldifferent");
    }
  }

  private String run(String model, String... options) throws IOException {
    return FlatzincTestRunner.run(tmp, model, options);
  }

  private static Set<String> solutions(String out) {
    return FlatzincTestRunner.solutions(out);
  }
}
