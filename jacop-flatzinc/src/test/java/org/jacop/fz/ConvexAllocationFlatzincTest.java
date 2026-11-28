/*
 * ConvexAllocationFlatzincTest.java
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
import java.util.function.IntUnaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of {@link org.jacop.fz.constraints.ConvexAllocationDetector} on random FlatZinc balancing
 * models: weighted absolute values, squares (int_times, int_pow), dead zones (int_max) and squared
 * dead zones of affine functions of the variables, summed by an int_lin_eq (the objective's
 * definition) or bounded by an int_lin_le, over variables whose sum is fixed, equal to a variable,
 * or the loads of a bin packing. The solution sets must equal a brute-force enumeration, and the
 * ConvexAllocation must be posted exactly when the model has the pattern. Larger random models are
 * minimized with and without the detection, in both search modes, and the optima must agree.
 */
class ConvexAllocationFlatzincTest {

  @TempDir Path tmp;

  /** Checked satisfaction models; the optimization test runs 2/5 as many models. */
  private static final int TRIALS = Integer.getInteger("convex.fz.trials", 300);

  /** A random model, its solutions by enumeration, and whether the detection should fire. */
  private record Model(String fzn, Set<String> bruteForce, boolean detectable) {}

  /** One cost term over x[i]: weight * shape, with its FlatZinc. */
  private record Term(int i, int weight, IntUnaryOperator value) {}

  private static final int FIXED = 0;
  private static final int TOTAL = 1;
  private static final int BINS = 2;
  private static final int MISSING = 3;

  private static Model randomModel(Random random, int n, int lo, int hi, boolean small) {
    int groupStyle = random.nextInt(small ? 5 : 3);
    if (groupStyle == 4) {
      groupStyle = MISSING;
    }
    boolean le = random.nextInt(4) == 0;
    StringBuilder fzn = new StringBuilder();
    StringBuilder body = new StringBuilder();
    int[][] domains = new int[n][];

    // bin packing: items with weights in bins 0..n-1, the loads are x
    int items = 2 + random.nextInt(small ? 2 : 4);
    int[] w = new int[items];
    for (int k = 0; k < items; k++) {
      w[k] = 1 + random.nextInt(small ? 2 : 3);
    }
    int weights = IntStream.of(w).sum();
    for (int i = 0; i < n; i++) {
      if (groupStyle == BINS) {
        domains[i] = IntStream.rangeClosed(0, weights).toArray();
      } else {
        domains[i] = IntStream.rangeClosed(lo, hi).filter(v -> random.nextInt(4) != 0).toArray();
        if (domains[i].length == 0) {
          domains[i] = new int[] {lo};
        }
      }
      fzn.append("var ").append(set(domains[i])).append(": x").append(i).append(";\n");
    }

    List<Term> terms = new ArrayList<>();
    int defined = 0;
    for (int i = 0; i < n; i++) {
      int count = 1 + (random.nextInt(4) == 0 ? 1 : 0);
      for (int c = 0; c < count; c++) {
        int weight = 1 + random.nextInt(3);
        int g = terms.size();
        String gv = "g" + g;
        fzn.append("var int: ").append(gv).append(";\n");
        int kind = random.nextInt(5);
        int p = random.nextBoolean() ? 1 : 1 + random.nextInt(2);
        int q = lo + random.nextInt(hi - lo + 1);
        String t = affine(fzn, body, "x" + i, p, -q, defined++, random);
        switch (kind) {
          case 0 -> {
            body.append("constraint int_abs(" + t + "," + gv + ");\n");
            terms.add(new Term(i, weight, v -> Math.abs(p * v - q)));
          }
          case 1 -> {
            if (random.nextBoolean()) {
              body.append("constraint int_pow(" + t + ",2," + gv + ");\n");
            } else {
              body.append("constraint int_times(" + t + "," + t + "," + gv + ");\n");
            }
            terms.add(new Term(i, weight, v -> (p * v - q) * (p * v - q)));
          }
          case 2 -> {
            // max(x - q, 0)
            String z = "z" + g;
            fzn.append("var 0..0: ").append(z).append(";\n");
            String u = affine(fzn, body, "x" + i, 1, -q, defined++, random);
            body.append("constraint int_max(" + u + "," + z + "," + gv + ");\n");
            terms.add(new Term(i, weight, v -> Math.max(v - q, 0)));
          }
          default -> {
            // max(x - ceil, floor - x), squared or not, floor in {ceil - 1, ceil}
            int floor = q - random.nextInt(2);
            String u = affine(fzn, body, "x" + i, 1, -q, defined++, random);
            String r = affine(fzn, body, "x" + i, -1, floor, defined++, random);
            boolean squared = kind == 4;
            String m = squared ? "m" + g : gv;
            if (squared) {
              fzn.append("var int: ").append(m).append(";\n");
            }
            body.append("constraint int_max(" + u + "," + r + "," + m + ");\n");
            if (squared) {
              body.append("constraint int_times(" + m + "," + m + "," + gv + ");\n");
            }
            terms.add(
                new Term(
                    i,
                    weight,
                    v -> {
                      int d = Math.max(v - q, floor - v);
                      return squared ? d * d : d;
                    }));
          }
        }
      }
    }
    // the cost: obj = sum of weight * g (equation) or sum of weight * g <= bound
    int bound = random.nextInt(small ? 40 : 200);
    StringBuilder coefs = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (int g = 0; g < terms.size(); g++) {
      coefs.append(g == 0 ? "" : ",").append(terms.get(g).weight());
      vars.append(g == 0 ? "" : ",").append("g").append(g);
    }
    if (le) {
      body.append("constraint int_lin_le([" + coefs + "],[" + vars + "]," + bound + ");\n");
    } else {
      fzn.append("var int: obj:: output_var;\n");
      body.append(
          "constraint int_lin_eq([" + coefs + ",-1],[" + vars + ",obj],0):: defines_var(obj);\n");
    }

    // the group
    int s = lo * n + random.nextInt((hi - lo) * n + 1);
    StringBuilder xs = new StringBuilder();
    StringBuilder ones = new StringBuilder();
    for (int i = 0; i < n; i++) {
      xs.append(i == 0 ? "" : ",").append('x').append(i);
      ones.append(i == 0 ? "" : ",").append(1);
    }
    int tlo = s - random.nextInt(3);
    int thi = s + random.nextInt(3);
    switch (groupStyle) {
      case FIXED -> body.append("constraint int_lin_eq([" + ones + "],[" + xs + "]," + s + ");\n");
      case TOTAL -> {
        fzn.append("var ").append(tlo).append("..").append(thi).append(": total:: output_var;\n");
        body.append("constraint int_lin_eq([" + ones + ",-1],[" + xs + ",total],0);\n");
      }
      case BINS -> {
        StringBuilder bins = new StringBuilder();
        for (int k = 0; k < items; k++) {
          fzn.append("var 0..").append(n - 1).append(": b").append(k).append(":: output_var;\n");
          bins.append(k == 0 ? "" : ",").append("b").append(k);
        }
        body.append(
            "constraint jacop_bin_packing(["
                + bins
                + "],["
                + xs
                + "],"
                + Arrays.toString(w).replace(" ", "")
                + ",0);\n");
      }
      default -> {
        // no sum: nothing to detect
      }
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");
    fzn.append(body);
    fzn.append(le ? "solve satisfy;\n" : "solve minimize obj;\n");

    Set<String> expected = new TreeSet<>();
    if (small && le) {
      int style = groupStyle;
      enumerate(
          0,
          new int[n],
          domains,
          x -> {
            int sum = IntStream.of(x).sum();
            if (style == FIXED && sum != s) {
              return;
            }
            if (style == TOTAL && (sum < tlo || sum > thi)) {
              return;
            }
            long cost = 0;
            for (Term term : terms) {
              cost += (long) term.weight() * term.value().applyAsInt(x[term.i()]);
            }
            if (cost > bound) {
              return;
            }
            String out = "x = array1d(1.." + n + ", " + Arrays.toString(x) + ");";
            if (style == TOTAL) {
              out = "total = " + sum + "; " + out;
            }
            if (style == BINS) {
              // every assignment of the items to bins with these loads
              int[] b = new int[items];
              for (String bins : packings(b, 0, w, x.clone())) {
                expected.add(bins + out);
              }
            } else {
              expected.add(out);
            }
          });
    }
    // a fixed sum of two variables is taken for a definition, not a group
    boolean detectable = groupStyle != MISSING && (groupStyle != FIXED || n >= 3);
    return new Model(fzn.toString(), expected, detectable);
  }

  // t = p * x + q, as x itself when p = 1 and q = 0, else defined by a random int_lin_eq
  private static String affine(
      StringBuilder fzn, StringBuilder body, String x, int p, int q, int id, Random random) {
    if (p == 1 && q == 0 && random.nextBoolean()) {
      return x;
    }
    String t = "t" + id;
    fzn.append("var int: ").append(t).append(";\n");
    if (random.nextBoolean()) {
      // p * x - t = -q
      body.append("constraint int_lin_eq([" + p + ",-1],[" + x + "," + t + "]," + (-q) + ");\n");
    } else {
      // -t + p * x = -q, written with t first
      body.append("constraint int_lin_eq([-1," + p + "],[" + t + "," + x + "]," + (-q) + ");\n");
    }
    return t;
  }

  private static List<String> packings(int[] b, int k, int[] w, int[] rest) {
    List<String> result = new ArrayList<>();
    if (k == b.length) {
      for (int r : rest) {
        if (r != 0) {
          return result;
        }
      }
      StringBuilder s = new StringBuilder();
      for (int j = 0; j < b.length; j++) {
        s.append("b").append(j).append(" = ").append(b[j]).append("; ");
      }
      result.add(s.toString());
      return result;
    }
    for (int bin = 0; bin < rest.length; bin++) {
      if (rest[bin] >= w[k]) {
        rest[bin] -= w[k];
        b[k] = bin;
        result.addAll(packings(b, k + 1, w, rest));
        rest[bin] += w[k];
      }
    }
    return result;
  }

  // the number of x[i] that take two values or more in the solutions
  private static int unfixed(Set<String> solutions) {
    List<Set<String>> values = new ArrayList<>();
    for (String solution : solutions) {
      String x = solution.substring(solution.indexOf('[') + 1, solution.indexOf(']'));
      String[] v = x.split(", ");
      for (int i = 0; i < v.length; i++) {
        if (values.size() <= i) {
          values.add(new TreeSet<>());
        }
        values.get(i).add(v[i]);
      }
    }
    return (int) values.stream().filter(set -> set.size() >= 2).count();
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
  void detectedAllocationKeepsAllSolutions() throws IOException {
    Random random = new Random(21);
    int detected = 0;
    int checked = 0;
    for (int trial = 0; checked < TRIALS; trial++) {
      Model model = randomModel(random, 2 + random.nextInt(2), -1, 4, true);
      if (!model.fzn().contains("solve satisfy")) {
        continue;
      }
      checked++;
      String out = run(model.fzn(), "-a", "-debug");
      boolean found = out.contains("redundant ConvexAllocation");
      if (found) {
        detected++;
      }
      // variables fixed while the model is read become shared constants, which the detection
      // may leave alone; it must fire when two variables of the group are not fixed
      if (model.detectable() && unfixed(model.bruteForce()) >= 2) {
        assertTrue(found, "not detected, trial " + trial + "\n" + model.fzn());
      } else if (!model.detectable()) {
        assertFalse(found, "detected, trial " + trial + "\n" + model.fzn());
      }
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
    assertTrue(detected > TRIALS / 4, "detected " + detected);
  }

  /** Random balancing models minimized with and without the detection, in both search modes. */
  @Test
  void optimaAgreeWithAndWithoutDetection() throws IOException {
    Random random = new Random(22);
    int detected = 0;
    int solved = 0;
    for (int trial = 0; trial < TRIALS * 2 / 5; trial++) {
      Model model = randomModel(random, 3 + random.nextInt(4), 0, 6, false);
      if (!model.fzn().contains("minimize")) {
        continue;
      }
      String[] mode =
          switch (trial % 4) {
            case 0 -> new String[] {"-debug", "--lcg", "on"};
            case 1 -> new String[] {"-debug", "--lcg", "on", "-f"};
            case 2 -> new String[] {"-debug", "--lcg", "off"};
            default -> new String[] {"-debug", "--lcg", "off", "-f"};
          };
      String on = run(model.fzn(), mode);
      String off;
      String property = "org.jacop.fz.convexAllocation";
      System.setProperty(property, "false");
      try {
        off = run(model.fzn(), mode);
      } finally {
        System.clearProperty(property);
      }
      if (on.contains("redundant ConvexAllocation")) {
        detected++;
      }
      assertFalse(off.contains("redundant ConvexAllocation"));
      assertEquals(optimum(off), optimum(on), "trial " + trial + "\n" + model.fzn());
      if (optimum(on) != null) {
        solved++;
      }
    }
    assertTrue(detected > TRIALS / 15, "detected " + detected);
    assertTrue(solved > TRIALS / 15, "solved " + solved);
  }

  @Test
  void balancedCurriculumLoadsAreDetected() throws IOException {
    // gbac: delta = max(load - ceil, floor - load), sum of delta^2, loads from a bin packing
    String fzn =
        """
        var 0..4: b0;
        var 0..4: b1;
        var 0..4: b2;
        var 0..4: b3;
        var 0..4: b4;
        var 0..20: l0;
        var 0..20: l1;
        var 0..20: l2;
        var -20..20: u0;
        var -20..20: u1;
        var -20..20: u2;
        var -20..20: v0;
        var -20..20: v1;
        var -20..20: v2;
        var 0..20: d0;
        var 0..20: d1;
        var 0..20: d2;
        var 0..400: s0;
        var 0..400: s1;
        var 0..400: s2;
        var 0..1200: objective:: output_var;
        constraint jacop_bin_packing([b0,b1,b2,b3,b4],[l0,l1,l2],[3,4,2,5,1],0);
        constraint int_lin_eq([1,-1],[l0,u0],5);
        constraint int_lin_eq([1,-1],[l1,u1],5);
        constraint int_lin_eq([1,-1],[l2,u2],5);
        constraint int_lin_eq([-1,-1],[l0,v0],-5);
        constraint int_lin_eq([-1,-1],[l1,v1],-5);
        constraint int_lin_eq([-1,-1],[l2,v2],-5);
        constraint int_max(u0,v0,d0);
        constraint int_max(u1,v1,d1);
        constraint int_max(u2,v2,d2);
        constraint int_times(d0,d0,s0);
        constraint int_times(d1,d1,s1);
        constraint int_times(d2,d2,s2);
        constraint int_lin_eq([1,-1,-1,-1],[objective,s0,s1,s2],0):: defines_var(objective);
        solve minimize objective;
        """;
    String out = run(fzn, "-debug");
    assertTrue(out.contains("redundant ConvexAllocation"), out);
    // by default the detection runs without LCG only
    assertTrue(runAsIs(fzn, "-debug", "--lcg", "off").contains("redundant ConvexAllocation"));
    assertFalse(runAsIs(fzn, "-debug", "--lcg", "on").contains("redundant ConvexAllocation"));
    // 15 units over three periods with ideal load 5: perfect balance 5, 5, 5 with 3+2, 4+1, 5
    assertTrue(out.contains("objective = 0;"), out);
  }

  private static final Pattern OBJ = Pattern.compile("obj = (-?\\d+);");

  private static String optimum(String out) {
    if (out.contains("=====UNSATISFIABLE=====")) {
      return "unsat";
    }
    if (!out.contains("==========")) {
      return null;
    }
    String last = null;
    Matcher m = OBJ.matcher(out);
    while (m.find()) {
      last = m.group(1);
    }
    return last;
  }

  private String run(String model, String... options) throws IOException {
    // the detection is off by default under LCG; the tests turn it on unless they turn it off
    String property = "org.jacop.fz.convexAllocation";
    boolean set = System.getProperty(property) == null;
    if (set) {
      System.setProperty(property, "true");
    }
    try {
      return runAsIs(model, options);
    } finally {
      if (set) {
        System.clearProperty(property);
      }
    }
  }

  private String runAsIs(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 3);
    args[options.length] = "-t";
    args[options.length + 1] = "20000";
    args[options.length + 2] = fzn.toString();
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
