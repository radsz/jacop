/*
 * DisjunctiveCliqueFlatzincTest.java
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
import java.util.function.Predicate;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the detection of disjunctive cliques in the FlatZinc front end, which posts redundant
 * unary resources: on random models with cumulatives, disjunctions in the encodings MiniZinc
 * produces and precedences, all solutions must match a brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class DisjunctiveCliqueFlatzincTest {

  @TempDir Path tmp;

  /** The FlatZinc of a random scheduling model and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce) {}

  // values: the starts s0..s(n-1), then the variable durations in the order of varDur
  private static Model randomModel(Random random) {
    int n = 4 + random.nextInt(3);
    int horizon = 4 + random.nextInt(4);
    int[] dur = new int[n];
    List<Integer> varDur = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      dur[i] = 1 + random.nextInt(3);
      if (random.nextInt(6) == 0) {
        varDur.add(i);
      }
    }
    int width = n + varDur.size();
    StringBuilder fzn = new StringBuilder();
    List<Predicate<int[]>> checks = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..").append(horizon).append(": s").append(i).append(";\n");
    }
    for (int i : varDur) {
      fzn.append("var 1..2: d").append(i).append(":: output_var;\n");
    }
    StringBuilder ss = new StringBuilder();
    for (int i = 0; i < n; i++) {
      ss.append(i == 0 ? "" : ",").append('s').append(i);
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: s:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(ss)
        .append("];\n");
    StringBuilder constraints = new StringBuilder();
    int[] bools = {0};

    // cumulatives
    int cumulatives = random.nextInt(3);
    for (int c = 0; c < cumulatives; c++) {
      List<Integer> tasks = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        if (random.nextInt(3) != 0) {
          tasks.add(i);
        }
      }
      if (tasks.size() < 2) {
        continue;
      }
      int capacity = 2 + random.nextInt(3);
      int[] use = new int[tasks.size()];
      StringBuilder s = new StringBuilder();
      StringBuilder d = new StringBuilder();
      StringBuilder r = new StringBuilder();
      for (int k = 0; k < tasks.size(); k++) {
        int i = tasks.get(k);
        use[k] = 1 + random.nextInt(capacity);
        String sep = k == 0 ? "" : ",";
        s.append(sep).append('s').append(i);
        d.append(sep).append(varDur.contains(i) ? "d" + i : String.valueOf(dur[i]));
        r.append(sep).append(use[k]);
      }
      constraints
          .append("constraint jacop_cumulative([")
          .append(s)
          .append("],[")
          .append(d)
          .append("],[")
          .append(r)
          .append("],")
          .append(capacity)
          .append(");\n");
      int[] vdIndex = varDurIndex(n, varDur);
      checks.add(
          v -> {
            for (int t = 0; t <= horizon + 3; t++) {
              int load = 0;
              for (int k = 0; k < tasks.size(); k++) {
                int i = tasks.get(k);
                int di = vdIndex[i] >= 0 ? v[vdIndex[i]] : dur[i];
                if (v[i] <= t && t < v[i] + di) {
                  load += use[k];
                }
              }
              if (load > capacity) {
                return false;
              }
            }
            return true;
          });
    }

    // disjunctions s[j] >= s[i] + a1 \/ s[i] >= s[j] + a2 in several encodings
    int disjunctions = random.nextInt(6);
    for (int k = 0; k < disjunctions; k++) {
      int i = random.nextInt(n);
      int j = random.nextInt(n);
      if (i == j) {
        continue;
      }
      int a1 = Math.max(0, dur[i] + random.nextInt(3) - 1);
      int a2 = Math.max(0, dur[j] + random.nextInt(3) - 1);
      int style = random.nextInt(5);
      String b1 = "b" + bools[0]++;
      String b2 = "b" + bools[0]++;
      fzn.append("var bool: ").append(b1).append(";\nvar bool: ").append(b2).append(";\n");
      boolean reif1 = style == 1 || style == 3;
      boolean reif2 = style == 1 || style == 3 || random.nextBoolean() && style != 2;
      constraints.append(literal(random, i, j, a1, b1, reif1));
      constraints.append(literal(random, j, i, a2, b2, reif2));
      switch (style) {
        case 2, 3 ->
            constraints
                .append("constraint bool_not(")
                .append(b1)
                .append(',')
                .append(b2)
                .append(");\n");
        case 4 ->
            constraints
                .append("constraint array_bool_or([")
                .append(b1)
                .append(',')
                .append(b2)
                .append("],true);\n");
        default ->
            constraints
                .append("constraint bool_clause([")
                .append(b1)
                .append(',')
                .append(b2)
                .append("],[]);\n");
      }
      if (style == 3) {
        // both literals are reified and complementary: exactly one order holds
        checks.add(v -> (v[j] >= v[i] + a1) != (v[i] >= v[j] + a2));
      } else {
        checks.add(v -> v[j] >= v[i] + a1 || v[i] >= v[j] + a2);
      }
    }

    // precedences
    int precedences = random.nextInt(4);
    for (int k = 0; k < precedences; k++) {
      int i = random.nextInt(n);
      int j = random.nextInt(n);
      if (i == j) {
        continue;
      }
      int a = random.nextInt(6) - 2;
      switch (random.nextInt(3)) {
        case 0 -> {
          constraints
              .append("constraint int_lin_le([1,-1],[s")
              .append(i)
              .append(",s")
              .append(j)
              .append("],")
              .append(-a)
              .append(");\n");
          checks.add(v -> v[j] >= v[i] + a);
        }
        case 1 -> {
          constraints.append("constraint int_lt(s").append(i).append(",s").append(j).append(");\n");
          checks.add(v -> v[j] >= v[i] + 1);
        }
        default -> {
          constraints
              .append("constraint int_lin_eq([-1,1],[s")
              .append(i)
              .append(",s")
              .append(j)
              .append("],")
              .append(a)
              .append(");\n");
          checks.add(v -> v[j] == v[i] + a);
        }
      }
    }
    fzn.append(constraints);
    fzn.append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] v = new int[width];
    enumerate(0, v, n, horizon, checks, varDur, expected);
    return new Model(fzn.toString(), expected);
  }

  // the literal b -> s[to] >= s[from] + lag (or b <-> ... when reified)
  private static String literal(Random random, int from, int to, int lag, String b, boolean reif) {
    String suffix = reif ? "_reif(" : "_imp(";
    if (lag == 0 && random.nextBoolean()) {
      return "constraint int_le" + suffix + "s" + from + ",s" + to + "," + b + ");\n";
    }
    if (lag == 1 && random.nextBoolean()) {
      return "constraint int_lt" + suffix + "s" + from + ",s" + to + "," + b + ");\n";
    }
    int k = 1 + random.nextInt(2);
    if (random.nextBoolean()) {
      // k*s[from] - k*s[to] <= -k*lag
      return "constraint int_lin_le"
          + suffix
          + "["
          + k
          + ","
          + -k
          + "],[s"
          + from
          + ",s"
          + to
          + "],"
          + -k * lag
          + ","
          + b
          + ");\n";
    }
    // -k*s[to] + k*s[from] <= -k*lag + k - 1, the same constraint with a remainder
    return "constraint int_lin_le"
        + suffix
        + "["
        + -k
        + ","
        + k
        + "],[s"
        + to
        + ",s"
        + from
        + "],"
        + (-k * lag + k - 1)
        + ","
        + b
        + ");\n";
  }

  private static int[] varDurIndex(int n, List<Integer> varDur) {
    int[] index = new int[n];
    Arrays.fill(index, -1);
    for (int k = 0; k < varDur.size(); k++) {
      index[varDur.get(k)] = n + k;
    }
    return index;
  }

  private static void enumerate(
      int pos,
      int[] v,
      int n,
      int horizon,
      List<Predicate<int[]>> checks,
      List<Integer> varDur,
      Set<String> out) {
    if (pos == v.length) {
      for (Predicate<int[]> c : checks) {
        if (!c.test(v)) {
          return;
        }
      }
      TreeSet<String> lines = new TreeSet<>();
      lines.add("s = array1d(1.." + n + ", " + Arrays.toString(Arrays.copyOf(v, n)) + ");");
      for (int k = 0; k < varDur.size(); k++) {
        lines.add("d" + varDur.get(k) + " = " + v[n + k] + ";");
      }
      out.add(String.join(" ", lines));
      return;
    }
    int lo = pos < n ? 0 : 1;
    int hi = pos < n ? horizon : 2;
    for (int x = lo; x <= hi; x++) {
      v[pos] = x;
      enumerate(pos + 1, v, n, horizon, checks, varDur, out);
    }
  }

  @Test
  void detectedUnaryResourcesKeepAllSolutions() throws IOException {
    Random random = new Random(11);
    int detected = 0;
    int trials = Integer.getInteger("disjunctiveCliques.trials", 400);
    for (int trial = 0; trial < trials; trial++) {
      Model model = randomModel(random);
      String out = run(model.fzn(), "-a", "-debug");
      if (out.contains("% redundant unary resource")) {
        detected++;
      }
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
    assertTrue(detected > trials / 10, "detected " + detected);
  }

  // the 3n problem of Sidorov et al. (CP 2025): every pair of the 3n tasks conflicts on one of
  // three cumulatives, so the clique of all tasks fails at once although each cumulative alone
  // is satisfiable
  private static String threeN(int n) {
    int horizon = 3 * n - 1;
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < 3 * n; i++) {
      fzn.append("var 0..").append(horizon - 1).append(": s").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(3 * n)
        .append("] of var int: s:: output_array([1..")
        .append(3 * n)
        .append("]) = [");
    for (int i = 0; i < 3 * n; i++) {
      fzn.append(i == 0 ? "" : ",").append('s').append(i);
    }
    fzn.append("];\n");
    for (int g = 0; g < 3; g++) {
      int h = (g + 1) % 3;
      StringBuilder s = new StringBuilder();
      StringBuilder d = new StringBuilder();
      StringBuilder r = new StringBuilder();
      for (int k = 0; k < 2 * n; k++) {
        int task = k < n ? g * n + k : h * n + k - n;
        String sep = k == 0 ? "" : ",";
        s.append(sep).append('s').append(task);
        d.append(sep).append(1);
        r.append(sep).append(k < n ? 4 : 2);
      }
      fzn.append("constraint jacop_cumulative([")
          .append(s)
          .append("],[")
          .append(d)
          .append("],[")
          .append(r)
          .append("],5);\n");
    }
    fzn.append("solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void threeNProblemFailsWithoutSearch() throws IOException {
    String out = run(threeN(8), "-s");
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    // the model fails while it is posted, before any search node
    assertFalse(out.contains("%%%mzn-stat: nodes="), out);
  }

  @Test
  void detectionCanBeTurnedOff() throws IOException {
    String property = "org.jacop.fz.disjunctiveCliques";
    System.setProperty(property, "false");
    try {
      String out = run(threeN(3), "-debug", "-s");
      assertFalse(out.contains("% redundant unary resource"));
      assertTrue(out.contains("=====UNSATISFIABLE====="), out);
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
