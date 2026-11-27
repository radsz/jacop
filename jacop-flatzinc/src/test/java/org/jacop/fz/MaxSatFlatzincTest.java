/*
 * MaxSatFlatzincTest.java
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks MaxSAT local search in the FlatZinc front end ({@code Solve.maxSatHint}) on random
 * weighted partial MaxSAT models in the encoding of the MaxSAT Evaluation converters: a {@code var
 * bool} per variable, the hard clauses as {@code bool_clause}, each soft clause with a relaxation
 * variable (some through {@code bool_not}) and the cost as a weighted sum of their {@code
 * bool2int}. Under -f and under model search without an annotation, the local search must run, the
 * last cost must be the optimum of an enumeration, and every printed solution must satisfy the hard
 * clauses with a cost no less than the weight of the soft clauses it falsifies.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class MaxSatFlatzincTest {

  @TempDir Path tmp;

  private record Model(String fzn, int n, List<int[]> hard, List<int[]> soft, int[] w, int opt) {}

  // literals 2 * v (x_v true) and 2 * v + 1 (x_v false)
  private static boolean satisfied(int[] clause, int a) {
    for (int lit : clause) {
      if (((a >> (lit >> 1)) & 1) == ((lit & 1) == 0 ? 1 : 0)) {
        return true;
      }
    }
    return false;
  }

  private static int[] clause(Random random, int n, int max) {
    int[] c = new int[2 + random.nextInt(max - 1)];
    for (int j = 0; j < c.length; j++) {
      c[j] = random.nextInt(2 * n);
    }
    return c;
  }

  private static String lits(int[] c, int sign, String extra) {
    StringBuilder b = new StringBuilder();
    for (int lit : c) {
      if ((lit & 1) == sign) {
        b.append(b.isEmpty() ? "" : ",").append("x_").append(lit >> 1);
      }
    }
    if (extra != null) {
      b.append(b.isEmpty() ? "" : ",").append(extra);
    }
    return b.toString();
  }

  private static Model randomModel(Random random) {
    int n = 8 + random.nextInt(7);
    List<int[]> hard = new ArrayList<>();
    List<int[]> soft = new ArrayList<>();
    int hards = random.nextInt(n);
    int softs = 10 + random.nextInt(16);
    int[] w = new int[softs];
    StringBuilder fzn = new StringBuilder();
    for (int v = 0; v < n; v++) {
      fzn.append("var bool: x_").append(v).append(":: output_var;\n");
    }
    for (int k = 0; k < softs; k++) {
      fzn.append("var bool: r_").append(k).append(";\n");
      fzn.append("var bool: s_").append(k).append(";\n");
      fzn.append("var 0..1: i_").append(k).append(";\n");
    }
    fzn.append("var 0..1000: z:: output_var;\n");
    for (int i = 0; i < hards; i++) {
      int[] c = clause(random, n, 3);
      hard.add(c);
      fzn.append("constraint bool_clause([").append(lits(c, 0, null)).append("],[");
      fzn.append(lits(c, 1, null)).append("]);\n");
    }
    StringBuilder ws = new StringBuilder();
    StringBuilder is = new StringBuilder();
    for (int k = 0; k < softs; k++) {
      int[] c = clause(random, n, 3);
      soft.add(c);
      w[k] = 1 + random.nextInt(9);
      if (random.nextBoolean()) {
        // relaxation r_k in the clause
        fzn.append("constraint bool_clause([").append(lits(c, 0, "r_" + k)).append("],[");
        fzn.append(lits(c, 1, null)).append("]);\n");
      } else {
        // its negation s_k, with not s_k in the clause
        fzn.append("constraint bool_not(r_").append(k).append(",s_").append(k).append(");\n");
        fzn.append("constraint bool_clause([").append(lits(c, 0, null)).append("],[");
        fzn.append(lits(c, 1, "s_" + k)).append("]);\n");
      }
      fzn.append("constraint bool2int(r_").append(k).append(",i_").append(k).append(");\n");
      ws.append(",").append(w[k]);
      is.append(",i_").append(k);
    }
    fzn.append("constraint int_lin_eq([-1").append(ws).append("],[z").append(is);
    fzn.append("],0):: defines_var(z);\n");
    fzn.append("solve minimize z;\n");
    int opt = Integer.MAX_VALUE;
    for (int a = 0; a < (1 << n); a++) {
      boolean ok = true;
      for (int[] c : hard) {
        ok &= satisfied(c, a);
      }
      if (ok) {
        opt = Math.min(opt, cost(soft, w, a));
      }
    }
    return new Model(fzn.toString(), n, hard, soft, w, opt);
  }

  private static int cost(List<int[]> soft, int[] w, int a) {
    int cost = 0;
    for (int k = 0; k < soft.size(); k++) {
      cost += satisfied(soft.get(k), a) ? 0 : w[k];
    }
    return cost;
  }

  @Test
  void localSearchKeepsTheOptimum() throws IOException {
    Random random = new Random(17);
    int fired = 0;
    int unsat = 0;
    for (int trial = 0; trial < 30; trial++) {
      Model model = randomModel(random);
      String[][] modes = {
        {"--lcg", "on", "-f", "--search-statistics"},
        {"--lcg", "on", "--search-statistics"},
        {"--lcg", "on", "-f", "--free-config", "maxsat=0"}
      };
      for (String[] mode : modes) {
        String out = run(model.fzn(), mode);
        String tag = "trial " + trial + " " + Arrays.toString(mode) + "\n" + model.fzn() + out;
        if (model.opt() == Integer.MAX_VALUE) {
          assertTrue(out.contains("=====UNSATISFIABLE====="), tag);
          unsat++;
          continue;
        }
        if (mode.length < 5 && out.contains("maxsatVariables=")) {
          fired++;
        }
        assertTrue(out.contains("=========="), tag);
        assertEquals(model.opt(), lastCost(out), tag);
        checkSolutions(model, out, tag);
      }
    }
    assertTrue(
        fired > 20, "the local search runs on the MaxSAT models: " + fired + ", unsat " + unsat);
  }

  // a model whose cost is the number of true x_v, with x_a + x_b <= 1 on disjoint pairs of cost
  // terms and random hard clauses that mostly ask for true literals, as hanoi5 of the PB
  // competition 2016; the local search must take the pairs as hard clauses
  private static Model pairModel(Random random) {
    int n = 8 + 2 * random.nextInt(4);
    List<int[]> hard = new ArrayList<>();
    StringBuilder fzn = new StringBuilder();
    StringBuilder is = new StringBuilder();
    StringBuilder ws = new StringBuilder();
    for (int v = 0; v < n; v++) {
      fzn.append("var bool: x_").append(v).append(":: output_var;\n");
      fzn.append("var 0..1: i_").append(v).append(";\n");
    }
    fzn.append("var 0..1000: z:: output_var;\n");
    for (int v = 0; v < n; v++) {
      fzn.append("constraint bool2int(x_").append(v).append(",i_").append(v).append(");\n");
      is.append(",i_").append(v);
      ws.append(",1");
    }
    for (int v = 0; v + 1 < n; v += 2) {
      hard.add(new int[] {2 * v + 1, 2 * (v + 1) + 1});
      fzn.append("constraint int_lin_le([1,1],[i_").append(v).append(",i_").append(v + 1);
      fzn.append("],1);\n");
    }
    int clauses = n / 2 + random.nextInt(n);
    for (int i = 0; i < clauses; i++) {
      int[] c = clause(random, n, 3);
      for (int j = 0; j < c.length; j++) {
        c[j] &= random.nextInt(4) == 0 ? ~0 : ~1;
      }
      hard.add(c);
      fzn.append("constraint bool_clause([").append(lits(c, 0, null)).append("],[");
      fzn.append(lits(c, 1, null)).append("]);\n");
    }
    fzn.append("constraint int_lin_eq([-1").append(ws).append("],[z").append(is);
    fzn.append("],0):: defines_var(z);\n");
    fzn.append("solve minimize z;\n");
    List<int[]> soft = new ArrayList<>();
    int[] w = new int[n];
    for (int v = 0; v < n; v++) {
      soft.add(new int[] {2 * v + 1});
      w[v] = 1;
    }
    int opt = Integer.MAX_VALUE;
    for (int a = 0; a < (1 << n); a++) {
      boolean ok = true;
      for (int[] c : hard) {
        ok &= satisfied(c, a);
      }
      if (ok) {
        opt = Math.min(opt, Integer.bitCount(a));
      }
    }
    return new Model(fzn.toString(), n, hard, soft, w, opt);
  }

  @Test
  void localSearchTakesClauseShapedRowsAsHard() throws IOException {
    Random random = new Random(23);
    int fired = 0;
    for (int trial = 0; trial < 24; trial++) {
      Model model = pairModel(random);
      if (model.opt() == Integer.MAX_VALUE) {
        continue;
      }
      // with no patience, an assignment the local search did not reach at once comes from JaSAT
      String[][] modes = {
        {"--lcg", "on", "-f", "--search-statistics"},
        {"--lcg", "on", "-f", "--search-statistics", "--free-config", "maxsat-patience=0"}
      };
      for (String[] mode : modes) {
        String out = run(model.fzn(), mode);
        String tag = "trial " + trial + " " + Arrays.toString(mode) + "\n" + model.fzn() + out;
        assertTrue(out.contains("=========="), tag);
        assertEquals(model.opt(), lastCost(out), tag);
        checkSolutions(model, out, tag);
        Matcher best = Pattern.compile("maxsatBest=(\\d+)").matcher(out);
        if (best.find()) {
          // blind to the pairs, the search reported costs below the optimum
          assertTrue(Integer.parseInt(best.group(1)) >= model.opt(), tag);
          fired++;
        }
      }
    }
    assertTrue(fired > 20, "the local search found assignments: " + fired);
  }

  private static int lastCost(String out) {
    Matcher m = Pattern.compile("(?m)^z = (\\d+);").matcher(out);
    int cost = -1;
    while (m.find()) {
      cost = Integer.parseInt(m.group(1));
    }
    return cost;
  }

  private static void checkSolutions(Model model, String out, String tag) {
    for (String solution : out.split("----------")) {
      if (!solution.contains("z = ")) {
        continue;
      }
      int a = 0;
      Matcher m = Pattern.compile("(?m)^x_(\\d+) = (true|false);").matcher(solution);
      while (m.find()) {
        a |= "true".equals(m.group(2)) ? 1 << Integer.parseInt(m.group(1)) : 0;
      }
      for (int[] c : model.hard()) {
        assertTrue(satisfied(c, a), tag + "\nbreaks a hard clause: " + solution);
      }
      assertTrue(cost(model.soft(), model.w(), a) <= lastCost(solution), tag + solution);
    }
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 4);
    args[options.length] = "-a";
    args[options.length + 1] = "-t";
    args[options.length + 2] = "20000";
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
