/*
 * FunctionalTabuFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.constraints.Count;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the tabu search of functional models in the FlatZinc front end ({@code
 * Solve.functionalHint}): on low autocorrelation binary sequences and on random models whose
 * constraints all define a variable (products and linear equalities, some with domains that exclude
 * values of their definition), the tabu search must run under -f, the last cost must be the optimum
 * of an enumeration, and every printed solution must have the cost of its decision values.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class FunctionalTabuFlatzincTest {

  @TempDir Path tmp;

  // a definition: kind 0 product, 1 linear a * x + b * y + c; its domain lo..hi
  private record Definition(int kind, int x, int y, int a, int b, int c, int lo, int hi) {}

  private record Model(String fzn, int[][] domains, List<Definition> defs, int[] costTerms) {}

  private static Model randomModel(Random random) {
    int nd = 3 + random.nextInt(4);
    int[][] domains = new int[nd][];
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < nd; i++) {
      domains[i] =
          random.nextBoolean()
              ? new int[] {-1, 1}
              : new int[] {random.nextInt(2), 2 + random.nextInt(2), 5};
      fzn.append("var {")
          .append(Arrays.toString(domains[i]).replaceAll("[\\[\\] ]", ""))
          .append("}: x_")
          .append(i)
          .append(":: output_var;\n");
    }
    List<Definition> defs = new ArrayList<>();
    int count = 3 + random.nextInt(5);
    for (int k = 0; k < count; k++) {
      int pool = nd + k;
      int x = random.nextInt(pool);
      int y = random.nextInt(pool);
      boolean tight = random.nextInt(4) == 0;
      int lo = tight ? -5 + random.nextInt(5) : -1000;
      int hi = tight ? 3 + random.nextInt(10) : 1000;
      Definition d =
          random.nextBoolean()
              ? new Definition(0, x, y, 0, 0, 0, lo, hi)
              : new Definition(
                  1,
                  x,
                  y,
                  1 + random.nextInt(3),
                  -2 + random.nextInt(5),
                  random.nextInt(3),
                  lo,
                  hi);
      defs.add(d);
      String v = name(nd, pool);
      fzn.append("var ").append(lo).append("..").append(hi).append(": ").append(v);
      fzn.append(":: is_defined_var;\n");
    }
    fzn.append("var -100000..100000: z:: output_var:: is_defined_var;\n");
    for (int k = 0; k < count; k++) {
      Definition d = defs.get(k);
      String v = name(nd, nd + k);
      String x = name(nd, d.x());
      String y = name(nd, d.y());
      if (d.kind() == 0) {
        fzn.append("constraint int_times(").append(x).append(',').append(y).append(',');
        fzn.append(v).append(')');
      } else if (x.equals(y)) {
        fzn.append("constraint int_lin_eq([1,").append(-(d.a() + d.b())).append("],[");
        fzn.append(v).append(',').append(x).append("],").append(d.c()).append(')');
      } else {
        fzn.append("constraint int_lin_eq([1,").append(-d.a()).append(',').append(-d.b());
        fzn.append("],[").append(v).append(',').append(x).append(',').append(y);
        fzn.append("],").append(d.c()).append(')');
      }
      fzn.append(":: defines_var(").append(v).append(");\n");
    }
    // the cost: the last three definitions with signs
    int[] terms = new int[count];
    StringBuilder cs = new StringBuilder("[-1");
    StringBuilder vs = new StringBuilder("[z");
    for (int k = Math.max(0, count - 3); k < count; k++) {
      terms[k] = random.nextBoolean() ? 1 : -1;
      cs.append(',').append(terms[k]);
      vs.append(',').append(name(nd, nd + k));
    }
    fzn.append("constraint int_lin_eq(").append(cs).append("],").append(vs);
    fzn.append("],0):: defines_var(z);\n");
    fzn.append("solve minimize z;\n");
    return new Model(fzn.toString(), domains, defs, terms);
  }

  private static String name(int nd, int v) {
    return v < nd ? "x_" + v : "d_" + (v - nd);
  }

  // the cost of decision values, or null when a defined value is outside its domain
  private static Long cost(Model m, int[] xs) {
    int nd = xs.length;
    long[] vs = new long[nd + m.defs().size()];
    for (int i = 0; i < nd; i++) {
      vs[i] = xs[i];
    }
    for (int k = 0; k < m.defs().size(); k++) {
      Definition d = m.defs().get(k);
      long v =
          d.kind() == 0 ? vs[d.x()] * vs[d.y()] : d.a() * vs[d.x()] + d.b() * vs[d.y()] + d.c();
      if (v < d.lo() || v > d.hi()) {
        return null;
      }
      vs[nd + k] = v;
    }
    long z = 0;
    for (int k = 0; k < m.costTerms().length; k++) {
      z += m.costTerms()[k] * vs[nd + k];
    }
    return z;
  }

  private static Long optimum(Model m) {
    int nd = m.domains().length;
    int[] at = new int[nd];
    Long best = null;
    while (true) {
      int[] xs = new int[nd];
      for (int i = 0; i < nd; i++) {
        xs[i] = m.domains()[i][at[i]];
      }
      Long c = cost(m, xs);
      if (c != null && (best == null || c < best)) {
        best = c;
      }
      int i = 0;
      while (i < nd && ++at[i] == m.domains()[i].length) {
        at[i] = 0;
        i++;
      }
      if (i == nd) {
        return best;
      }
    }
  }

  @Test
  void tabuSearchKeepsTheOptimumOfRandomModels() throws IOException {
    Random random = new Random(23);
    int fired = 0;
    int trials = 16;
    for (int trial = 0; trial < trials; trial++) {
      Model model = randomModel(random);
      Long opt = optimum(model);
      String out =
          run(
              model.fzn(),
              20000,
              "--lcg",
              "on",
              "-f",
              "--search-statistics",
              "--free-config",
              "tabu-max=200");
      String tag = "trial " + trial + "\n" + model.fzn() + out;
      if (opt == null) {
        assertTrue(out.contains("=====UNSATISFIABLE====="), tag);
        continue;
      }
      if (out.contains("tabuVariables=")) {
        fired++;
      }
      assertTrue(out.contains("=========="), tag);
      assertEquals(opt.longValue(), lastCost(out), tag);
      for (String solution : out.split("----------")) {
        if (!solution.contains("z = ")) {
          continue;
        }
        int[] xs = new int[model.domains().length];
        Matcher m = Pattern.compile("(?m)^x_(\\d+) = (-?\\d+);").matcher(solution);
        while (m.find()) {
          xs[Integer.parseInt(m.group(1))] = Integer.parseInt(m.group(2));
        }
        Long c = cost(model, xs);
        assertTrue(c != null && c == lastCost(solution), tag + "\nwrong solution: " + solution);
      }
    }
    assertTrue(fired >= trials / 2, "the tabu search runs on the functional models: " + fired);
  }

  // low autocorrelation binary sequence of length n, minimising z
  private static String sequenceModel(int n) {
    StringBuilder fzn = new StringBuilder();
    StringBuilder cons = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var {-1,1}: x_").append(i).append(":: output_var;\n");
    }
    StringBuilder squares = new StringBuilder();
    for (int k = 1; k < n; k++) {
      StringBuilder ys = new StringBuilder();
      for (int i = 0; i + k < n; i++) {
        fzn.append("var {-1,1}: y_").append(k).append('_').append(i).append(":: is_defined_var;\n");
        ys.append(i == 0 ? "" : ",").append("y_").append(k).append('_').append(i);
        cons.append("constraint int_times(x_").append(i).append(",x_").append(i + k);
        cons.append(",y_").append(k).append('_').append(i).append(");\n");
      }
      fzn.append("var ").append(-(n - k)).append("..").append(n - k).append(": c_").append(k);
      fzn.append(":: is_defined_var;\n");
      fzn.append("var 0..").append((n - k) * (n - k)).append(": s_").append(k);
      fzn.append(":: is_defined_var;\n");
      squares.append(k == 1 ? "" : ",").append("s_").append(k);
      cons.append("constraint int_lin_eq([").append("1,".repeat(n - k)).append("-1],[");
      cons.append(ys).append(",c_").append(k).append("],0);\n");
      cons.append("constraint int_times(c_").append(k).append(",c_").append(k).append(",s_");
      cons.append(k).append(");\n");
    }
    fzn.append("var 0..100000: z:: output_var:: is_defined_var;\n");
    fzn.append(cons);
    fzn.append("constraint int_lin_eq([").append("1,".repeat(n - 1)).append("-1],[");
    fzn.append(squares).append(",z],0):: defines_var(z);\n");
    fzn.append("solve minimize z;\n");
    return fzn.toString();
  }

  /**
   * A function over many variables is evaluated whole after every trial move: with the cost a count
   * over 3,000 variables the walk took 54 s of a 60 s run (128 steps), and at 20 s there was no
   * answer; the solver alone takes 2 s. Such a model is left to the solver; a short count still
   * makes a functional model.
   */
  @Test
  void functionsOfManyVariablesAreLeftToTheSolver() {
    for (int n : new int[] {50, 3000}) {
      Store store = new Store();
      IntVar[] y = new IntVar[n];
      for (int i = 0; i < n; i++) {
        y[i] = new IntVar(store, "y" + i, 0, 9);
      }
      IntVar z = new IntVar(store, "z", 0, n);
      store.impose(new Count(y, z, 3));
      List<String> why = new ArrayList<>();
      FunctionalModel model = FunctionalModel.detect(store, List.of(), z, List.of(), why::add);
      if (n <= FunctionalModel.FUNCTION_INPUTS) {
        assertNotNull(model, why.toString());
      } else {
        assertNull(model);
        assertTrue(why.get(0).startsWith("a function of " + n + " variables"), why.toString());
      }
    }
  }

  @Test
  void tabuSearchFindsTheOptimalSequence() throws IOException {
    // low autocorrelation binary sequence of length 13: the Barker sequence, energy 6; the tabu
    // search runs instead of free search first, which a sum of squares otherwise starts
    String fzn = sequenceModel(13);
    String out =
        run(
            fzn,
            20000,
            "--lcg",
            "on",
            "-f",
            "--search-statistics",
            "--free-config",
            // free search first (#810) proves this optimum before LCG and its tabu search start
            "tabu-max=2000,free-first=0");
    String tag = fzn + out;
    assertTrue(out.contains("tabuVariables=13"), tag);
    assertTrue(out.contains("tabuBest=6"), tag);
    assertTrue(out.contains("=========="), tag);
    assertEquals(6, lastCost(out), tag);
  }

  @Test
  void solutionsAfterFreeSearchFirstImprove() throws IOException {
    // without the tabu search, free search first runs on the sum of squares and prints its
    // solutions; the LP probe after it printed worse ones (labs 22: 3311 after 39), so the last
    // solution was not the best. The build turns the probe off (org.jacop.fz.lpProbe=0).
    String fzn = sequenceModel(22);
    String probe = System.getProperty("org.jacop.fz.lpProbe");
    System.setProperty("org.jacop.fz.lpProbe", "200");
    String out;
    try {
      out = run(fzn, 8000, "--lcg", "on", "-f", "--free-config", "tabu=0");
    } finally {
      if (probe == null) {
        System.clearProperty("org.jacop.fz.lpProbe");
      } else {
        System.setProperty("org.jacop.fz.lpProbe", probe);
      }
    }
    Matcher m = Pattern.compile("(?m)^z = (-?\\d+);").matcher(out);
    int previous = Integer.MAX_VALUE;
    int count = 0;
    while (m.find()) {
      int cost = Integer.parseInt(m.group(1));
      assertTrue(cost < previous, "printed " + cost + " after " + previous + "\n" + out);
      previous = cost;
      count++;
    }
    assertTrue(count > 0, out);
  }

  private static int lastCost(String out) {
    Matcher m = Pattern.compile("(?m)^z = (-?\\d+);").matcher(out);
    int cost = Integer.MIN_VALUE;
    while (m.find()) {
      cost = Integer.parseInt(m.group(1));
    }
    return cost;
  }

  private String run(String model, int millis, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 4);
    args[options.length] = "-a";
    args[options.length + 1] = "-t";
    args[options.length + 2] = Integer.toString(millis);
    args[options.length + 3] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
