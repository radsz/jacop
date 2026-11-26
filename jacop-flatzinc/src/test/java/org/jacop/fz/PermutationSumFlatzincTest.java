/*
 * PermutationSumFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the all-different constraints implied by element channels and by equalities x - y = d, and
 * the permutation sums they give the lattice of the equalities: Langford's problem written with
 * elements (as the XCSP LangfordBin instances) is proved infeasible before search for n ≡ 1, 2 (mod
 * 4), and random channelled models keep all their solutions.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class PermutationSumFlatzincTest {

  @TempDir Path tmp;

  private static final String IMPLIED = "org.jacop.fz.alldifferentImplied";
  private static final String SUMS = "org.jacop.fz.permutationSums";

  /**
   * Langford's problem L(2, n) as LangfordBin states it: cells v[0..2n-1], and for each value i the
   * positions p[2i] and p[2i+1] with v[p] = i and p[2i] = p[2i+1] + i + 1.
   */
  private static String langford(int n) {
    int cells = 2 * n;
    StringBuilder fzn = new StringBuilder();
    StringBuilder vs = new StringBuilder();
    StringBuilder ps = new StringBuilder();
    for (int k = 0; k < cells; k++) {
      fzn.append("var 1..").append(n).append(": v_").append(k).append(";\n");
      vs.append(k == 0 ? "" : ",").append("v_").append(k);
    }
    for (int k = 0; k < cells; k++) {
      fzn.append("var 0..").append(cells - 1).append(": p_").append(k).append(";\n");
      ps.append(k == 0 ? "" : ",").append("p_").append(k);
    }
    fzn.append("array [1..")
        .append(cells)
        .append("] of var int: v:: output_array([0..")
        .append(cells - 1)
        .append("]) = [")
        .append(vs)
        .append("];\n");
    fzn.append("array [1..")
        .append(cells)
        .append("] of var int: p:: output_array([0..")
        .append(cells - 1)
        .append("]) = [")
        .append(ps)
        .append("];\n");
    for (int i = 0; i < n; i++) {
      for (int k = 2 * i; k <= 2 * i + 1; k++) {
        fzn.append("constraint jacop_array_var_int_element_nonshifted(p_")
            .append(k)
            .append(",v,")
            .append(i + 1)
            .append(",0);\n");
      }
      fzn.append("constraint int_lin_eq([1,-1],[p_")
          .append(2 * i)
          .append(",p_")
          .append(2 * i + 1)
          .append("],")
          .append(i + 2)
          .append(");\n");
    }
    return fzn.append("solve satisfy;\n").toString();
  }

  @Test
  void langfordParityIsProvedBeforeSearch() throws IOException {
    for (int n : new int[] {5, 6, 9, 10, 13, 14}) {
      String out = run(langford(n), "-s");
      assertTrue(out.contains("=====UNSATISFIABLE====="), "n = " + n + "\n" + out);
      // found infeasible while the model is read: no search statistics
      assertTrue(!out.contains("%%%mzn-stat: nodes="), "n = " + n + " searched\n" + out);
    }
  }

  @Test
  void langfordSolutionsAreKept() throws IOException {
    // L(2, 7) has 26 pairings up to reversal, 52 position assignments
    for (int n : new int[] {3, 4, 7}) {
      Set<String> on = solutions(run(langford(n), "-a"));
      Set<String> off = withProperties(() -> solutions(run(langford(n), "-a")));
      assertEquals(off, on, "n = " + n);
      assertEquals(n == 3 ? 2 : n == 4 ? 2 : 52, on.size(), "n = " + n);
    }
  }

  @Test
  void randomChannelsKeepAllSolutions() throws IOException {
    Random random = new Random(7);
    int fired = 0;
    for (int trial = 0; trial < 150; trial++) {
      String fzn = randomModel(random);
      Set<String> off = withProperties(() -> solutions(run(fzn, "-a")));
      // the default: implied cliques only give permutation sums
      assertEquals(off, solutions(run(fzn, "-a")), "trial " + trial + "\n" + fzn);
      // the implied cliques posted as all-different constraints too
      System.setProperty(IMPLIED, "post");
      try {
        String post = run(fzn, "-a", "-debug");
        if (post.contains("alldifferent on")) {
          fired++;
        }
        assertEquals(off, solutions(post), "post, trial " + trial + "\n" + fzn);
      } finally {
        System.clearProperty(IMPLIED);
      }
    }
    assertTrue(fired > 20, "fired " + fired);
  }

  // m cells over values 1..k; positions p_j with v[p_j] = c_j (some through a fixed variable),
  // some pairs linked by p_a = p_b + d
  private static String randomModel(Random random) {
    int m = 5 + random.nextInt(2);
    int k = 2 + random.nextInt(3);
    int base = random.nextInt(2);
    StringBuilder fzn = new StringBuilder();
    StringBuilder vs = new StringBuilder();
    StringBuilder ps = new StringBuilder();
    for (int i = 0; i < m; i++) {
      fzn.append("var 1..").append(k).append(": v_").append(i).append(";\n");
      vs.append(i == 0 ? "" : ",").append("v_").append(i);
    }
    int[] c = new int[m];
    for (int j = 0; j < m; j++) {
      int lo = base + random.nextInt(2);
      int hi = base + m - 1 - random.nextInt(2);
      fzn.append("var ").append(lo).append("..").append(hi).append(": p_").append(j).append(";\n");
      ps.append(j == 0 ? "" : ",").append("p_").append(j);
      c[j] = 1 + random.nextInt(k);
    }
    fzn.append("var 1..").append(k).append(": y;\n");
    fzn.append("array [1..")
        .append(m)
        .append("] of var int: v:: output_array([1..")
        .append(m)
        .append("]) = [")
        .append(vs)
        .append("];\n");
    fzn.append("array [1..")
        .append(m)
        .append("] of var int: p:: output_array([1..")
        .append(m)
        .append("]) = [")
        .append(ps)
        .append("];\n");
    for (int j = 0; j < m; j++) {
      String target = j == 0 ? "y" : String.valueOf(c[j]);
      if (base == 1 && random.nextBoolean()) {
        fzn.append("constraint array_var_int_element(p_")
            .append(j)
            .append(",v,")
            .append(target)
            .append(");\n");
      } else {
        fzn.append("constraint jacop_array_var_int_element_nonshifted(p_")
            .append(j)
            .append(",v,")
            .append(target)
            .append(',')
            .append(base)
            .append(");\n");
      }
    }
    fzn.append("constraint int_eq(y,").append(c[0]).append(");\n");
    for (int a = 0; a < m; a++) {
      for (int b = a + 1; b < m; b++) {
        if (c[a] == c[b] && random.nextInt(3) != 0) {
          int d = 1 + random.nextInt(3);
          fzn.append("constraint int_lin_eq([1,-1],[p_")
              .append(a)
              .append(",p_")
              .append(b)
              .append("],")
              .append(random.nextBoolean() ? d : -d)
              .append(");\n");
        }
      }
    }
    return fzn.append("solve satisfy;\n").toString();
  }

  private interface Run<T> {
    T get() throws IOException;
  }

  private static <T> T withProperties(Run<T> run) throws IOException {
    System.setProperty(IMPLIED, "off");
    System.setProperty(SUMS, "false");
    try {
      return run.get();
    } finally {
      System.clearProperty(IMPLIED);
      System.clearProperty(SUMS);
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

  /**
   * A binary de Bruijn sequence of order 5 as gcc_de_bruijn writes it: digits d_0..d_31 (cyclic),
   * x_i = 16 d_i + 8 d_(i+1) + 4 d_(i+2) + 2 d_(i+3) + d_(i+4) :: defines_var(x_i) and
   * all_different(x).
   */
  private static String deBruijn() {
    int n = 32;
    StringBuilder fzn = new StringBuilder();
    StringBuilder ds = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..1: d_").append(i).append(";\n");
      ds.append(i == 0 ? "" : ",").append("d_").append(i);
      xs.append(i == 0 ? "" : ",").append("x_").append(i);
    }
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..").append(n - 1).append(": x_").append(i).append(" :: is_defined_var;\n");
    }
    fzn.append("array [1..32] of var int: d :: output_array([1..32]) = [")
        .append(ds)
        .append("];\n");
    fzn.append("array [1..32] of var int: x = [").append(xs).append("];\n");
    for (int i = 0; i < n; i++) {
      fzn.append("constraint int_lin_eq([1,-16,-8,-4,-2,-1],[x_").append(i);
      for (int k = 0; k < 5; k++) {
        fzn.append(",d_").append((i + k) % n);
      }
      fzn.append("],0) :: defines_var(x_").append(i).append(");\n");
    }
    fzn.append("constraint jacop_alldiff(x);\n");
    return fzn.append("solve :: int_search(d,input_order,indomain_min,complete) satisfy;\n")
        .toString();
  }

  private static String stat(String out, String name) {
    for (String line : out.split("\\R")) {
      if (line.startsWith("%%%mzn-stat: " + name + "=")) {
        return line.substring(line.indexOf('=') + 1);
      }
    }
    return null;
  }

  @Test
  void definitionsHeldTogetherByAPermutationSumAreNotReformulated() throws IOException {
    // the 32 definitions x_i are joined only by the permutation sum of all_different(x), which kept
    // them from being set aside as definitions: the component looked like a market split problem,
    // was reformulated over lattice variables and the search branched on those before the
    // annotation (gcc_de_bruijn: 80,000 failures and no solution in 60 s at the defaults)
    String model = deBruijn();
    String off = run(model, "--lcg", "off");
    String on = run(model, "--lcg", "on", "--lp", "on", "-s", "-v");
    assertEquals(solutions(off), solutions(on), on);
    assertEquals(1, solutions(on).size(), on);
    assertEquals("0", stat(on, "latticeVars"), on);
    assertEquals("0", stat(on, "failures"), on);
  }

  @Test
  void aCryptarithmWithItsPermutationSumIsStillReformulated() throws IOException {
    // the equality of general_store with the permutation sum of its ten digits: its own equality
    // is no definition, so the component is still reformulated
    String model =
        """
        var 0..9: S :: output_var;
        var 0..9: E :: output_var;
        var 0..9: H :: output_var;
        var 0..9: L :: output_var;
        var 0..9: O :: output_var;
        var 0..9: P :: output_var;
        var 0..9: A :: output_var;
        var 0..9: W :: output_var;
        var 0..9: B :: output_var;
        var 0..9: C :: output_var;
        array [1..10] of var int: x = [S,E,H,L,O,P,A,W,B,C];
        constraint int_lin_eq([12049,2342,25001,-89790,10610,1011032,-698690,111,101000,223000],\
        [S,E,H,L,O,P,A,W,B,C],0);
        constraint jacop_alldiff(x);
        solve satisfy;
        """;
    String on = run(model, "-a", "--lcg", "on", "--lp", "on", "-s", "-v");
    assertTrue(Integer.parseInt(stat(on, "latticeVars")) > 0, on);
    assertEquals(1, solutions(on).size(), on);
    assertEquals(solutions(run(model, "-a", "--lcg", "off", "--lp", "off")), solutions(on), on);
  }
}
