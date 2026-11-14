/*
 * CostNetworkFlatzincTest.java
 * <p>
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The cost network bound ({@code -Dorg.jacop.fz.costNetwork=true}) on small weighted frequency
 * assignment models flattened as MiniZinc flattens celar: every optimum must stay, with and without
 * LCG, and match a brute-force optimum.
 */
class CostNetworkFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.costNetwork";

  private static final int TRIALS = Integer.getInteger("costnetwork.fz.trials", 40);

  @TempDir Path tmp;

  /** A random instance: frequencies, soft distance constraints with weights, hard distances. */
  private record Instance(int n, int[] lo, int[] hi, int[][] soft, int[][] hard) {

    // soft: i, j, k, w: cost w when |f_i - f_j| <= k; hard: i, j, k: |f_i - f_j| = k
    long optimum() {
      int[] f = new int[n];
      return search(f, 0);
    }

    private long search(int[] f, int at) {
      if (at == n) {
        for (int[] h : hard) {
          if (Math.abs(f[h[0]] - f[h[1]]) != h[2]) {
            return Long.MAX_VALUE;
          }
        }
        long c = 0;
        for (int[] s : soft) {
          if (Math.abs(f[s[0]] - f[s[1]]) <= s[2]) {
            c += s[3];
          }
        }
        return c;
      }
      long best = Long.MAX_VALUE;
      for (int v = lo[at]; v <= hi[at]; v++) {
        f[at] = v;
        best = Math.min(best, search(f, at + 1));
      }
      return best;
    }

    String fzn() {
      StringBuilder m = new StringBuilder();
      StringBuilder body = new StringBuilder();
      StringBuilder coefs = new StringBuilder("1");
      StringBuilder terms = new StringBuilder("obj");
      for (int i = 0; i < n; i++) {
        m.append("var ")
            .append(lo[i])
            .append("..")
            .append(hi[i])
            .append(": f")
            .append(i)
            .append(";\n");
      }
      m.append("array [1..").append(n).append("] of var int: f :: output_array([1..").append(n);
      m.append("]) = [")
          .append(
              String.join(
                  ",", java.util.stream.IntStream.range(0, n).mapToObj(i -> "f" + i).toList()));
      m.append("];\n");
      int t = 0;
      for (int[] s : soft) {
        // d = f_i - f_j, a = |d|, b = (a <= k), c = bool2int(b), cost w * c
        m.append("var -20..20: d").append(t).append(" :: var_is_introduced :: is_defined_var;\n");
        m.append("var 0..20: a").append(t).append(" :: var_is_introduced :: is_defined_var;\n");
        m.append("var bool: b").append(t).append(" :: var_is_introduced :: is_defined_var;\n");
        m.append("var 0..1: c").append(t).append(" :: var_is_introduced :: is_defined_var;\n");
        body.append("constraint int_lin_eq([1,-1,1],[d")
            .append(t)
            .append(",f")
            .append(s[0])
            .append(",f");
        body.append(s[1]).append("],0) :: defines_var(d").append(t).append(");\n");
        body.append("constraint int_abs(d")
            .append(t)
            .append(",a")
            .append(t)
            .append(") :: defines_var(a");
        body.append(t).append(");\n");
        body.append("constraint int_le_reif(a")
            .append(t)
            .append(",")
            .append(s[2])
            .append(",b")
            .append(t);
        body.append(") :: defines_var(b").append(t).append(");\n");
        body.append("constraint bool2int(b")
            .append(t)
            .append(",c")
            .append(t)
            .append(") :: defines_var(c");
        body.append(t).append(");\n");
        coefs.append(",").append(-s[3]);
        terms.append(",c").append(t);
        t++;
      }
      int h = 0;
      for (int[] hd : hard) {
        m.append("var -20..20: e").append(h).append(" :: var_is_introduced :: is_defined_var;\n");
        body.append("constraint int_lin_eq([1,-1,1],[e")
            .append(h)
            .append(",f")
            .append(hd[0])
            .append(",f");
        body.append(hd[1]).append("],0) :: defines_var(e").append(h).append(");\n");
        body.append("constraint int_abs(e").append(h).append(",").append(hd[2]).append(");\n");
        h++;
      }
      m.append("var 0..1000: obj :: output_var :: is_defined_var;\n");
      body.append("constraint int_lin_eq([")
          .append(coefs)
          .append("],[")
          .append(terms)
          .append("],0) :: defines_var(obj);\n");
      return m.toString() + body + "solve minimize obj;\n";
    }
  }

  private static Instance random(Random rnd) {
    int n = 3 + rnd.nextInt(4);
    int[] lo = new int[n];
    int[] hi = new int[n];
    for (int i = 0; i < n; i++) {
      lo[i] = rnd.nextInt(3);
      hi[i] = lo[i] + 2 + rnd.nextInt(4);
    }
    int ns = 2 + rnd.nextInt(2 * n);
    int[][] soft = new int[ns][];
    for (int s = 0; s < ns; s++) {
      int i = rnd.nextInt(n);
      int j = (i + 1 + rnd.nextInt(n - 1)) % n;
      soft[s] = new int[] {i, j, rnd.nextInt(3), 1 + rnd.nextInt(9)};
    }
    int nh = rnd.nextInt(2);
    int[][] hard = new int[nh][];
    for (int s = 0; s < nh; s++) {
      int i = rnd.nextInt(n);
      int j = (i + 1 + rnd.nextInt(n - 1)) % n;
      hard[s] = new int[] {i, j, rnd.nextInt(3)};
    }
    return new Instance(n, lo, hi, soft, hard);
  }

  @Test
  void optimaStayWithTheBound() throws IOException {
    Random rnd = new Random(41);
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance inst = random(rnd);
      long opt = inst.optimum();
      String expected = opt == Long.MAX_VALUE ? "UNSATISFIABLE" : Long.toString(opt);
      for (String lcg : new String[] {"off", "on"}) {
        String out = run(inst.fzn(), "--lcg", lcg);
        assertEquals(
            expected, optimum(out), "trial " + trial + " lcg " + lcg + "\n" + inst.fzn() + out);
      }
    }
  }

  @Test
  void boundIsPosted() throws IOException {
    // three frequencies in 0..2, every pair within distance 0 costs: no assignment escapes cost 0
    // only when all differ; with two values two of them meet
    Instance inst =
        new Instance(
            3,
            new int[] {0, 0, 0},
            new int[] {1, 1, 1},
            new int[][] {{0, 1, 0, 5}, {1, 2, 0, 5}, {0, 2, 0, 5}},
            new int[0][]);
    assertEquals(5, inst.optimum());
    String out = run(inst.fzn(), "--search-statistics");
    assertEquals("5", optimum(out), out);
    assertTrue(out.contains("cfnTerms=3"), out);
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 2);
    args[options.length] = "-a";
    args[options.length + 1] = fzn.toString();
    System.setProperty(PROPERTY, "true");
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  // the value of obj in the last solution, or the status when there is none
  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out);
    return last;
  }
}
