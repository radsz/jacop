/*
 * PureClauseFlatzincTest.java
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
import java.util.List;
import java.util.Random;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.jasat.cdcl.CdclSolver;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of models of clauses alone solved by JaSAT without lazy clause generation ({@link
 * PureClauseModel}): random small CNFs against a brute-force check, in the default mode and with
 * -f, and models that must stay with lazy clause generation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class PureClauseFlatzincTest {

  @TempDir Path tmp;

  private static final int VARS = 50;

  private static final Pattern MODEL =
      Pattern.compile("xs = array1d\\(1\\.\\.\\d+, \\[(.*?)\\]\\);");

  // a random 3-CNF over VARS variables near the threshold, about half of them satisfiable, with
  // literals as +-(1..VARS)
  private static List<int[]> cnf(long seed) {
    Random random = new Random(seed);
    int clauses = 205 + random.nextInt(15);
    List<int[]> cnf = new ArrayList<>();
    for (int c = 0; c < clauses; c++) {
      int[] clause = new int[3];
      for (int i = 0; i < clause.length; i++) {
        clause[i] = (1 + random.nextInt(VARS)) * (random.nextBoolean() ? 1 : -1);
      }
      cnf.add(clause);
    }
    return cnf;
  }

  private static boolean satisfies(List<int[]> cnf, boolean[] value) {
    for (int[] clause : cnf) {
      boolean sat = false;
      for (int l : clause) {
        sat |= value[Math.abs(l)] == l > 0;
      }
      if (!sat) {
        return false;
      }
    }
    return true;
  }

  // the reference: JaSAT on the CNF itself, as CdclMain solves it
  private static boolean satisfiable(List<int[]> cnf) {
    CdclSolver solver = new CdclSolver();
    solver.ensureVars(VARS);
    for (int[] clause : cnf) {
      solver.addClause(clause);
    }
    int result = solver.solve();
    assertTrue(result != CdclSolver.UNKNOWN);
    return result == CdclSolver.SAT;
  }

  // the CNF as bool_clause constraints, with an output array xs and the given extra lines
  private static String model(List<int[]> cnf, String extra, String solve) {
    StringBuilder s = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    for (int v = 1; v <= VARS; v++) {
      s.append("var bool: x").append(v).append(";\n");
      xs.append(v == 1 ? "" : ",").append('x').append(v);
    }
    s.append("array [1..").append(VARS).append("] of var bool: xs:: output_array([1..");
    s.append(VARS).append("]) = [").append(xs).append("];\n");
    for (int[] clause : cnf) {
      StringBuilder pos = new StringBuilder();
      StringBuilder neg = new StringBuilder();
      for (int l : clause) {
        StringBuilder side = l > 0 ? pos : neg;
        side.append(side.isEmpty() ? "" : ",").append('x').append(Math.abs(l));
      }
      s.append("constraint bool_clause([").append(pos).append("],[").append(neg).append("]);\n");
    }
    s.append(extra).append(solve).append('\n');
    return s.toString();
  }

  private static boolean[] printed(String out) {
    Matcher m = MODEL.matcher(out);
    assertTrue(m.find(), out);
    String[] values = m.group(1).split(",");
    boolean[] value = new boolean[VARS + 1];
    for (int v = 1; v <= VARS; v++) {
      value[v] = "true".equals(values[v - 1].trim());
    }
    return value;
  }

  private void check(List<int[]> cnf, String out) {
    if (satisfiable(cnf)) {
      assertTrue(satisfies(cnf, printed(out)), out);
      assertFalse(out.contains("=====UNSATISFIABLE====="), out);
    } else {
      assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    }
  }

  @Test
  void randomCnfsGoToJaSat() throws IOException {
    int routed = 0;
    int runs = 0;
    int unsat = 0;
    for (long seed = 1; seed <= 16; seed++) {
      List<int[]> cnf = cnf(seed);
      String fzn = model(cnf, "", "solve satisfy;");
      unsat += satisfiable(cnf) ? 0 : 1;
      for (boolean free : new boolean[] {false, true}) {
        String out = run(fzn, free);
        // root probing can decide a model before the search
        routed += out.contains("%%%mzn-stat: pureClauseModel=true") ? 1 : 0;
        if (seed == 1) {}
        runs++;
        check(cnf, out);
      }
    }
    assertTrue(routed >= runs / 2, routed + " of " + runs + " runs given to JaSAT");
    assertTrue(unsat > 0 && unsat < 16, unsat + " unsatisfiable");
  }

  @Test
  void fixedVariablesAreLeftOutOfTheClauses() throws IOException {
    // x1 is true and x2 false at the root: clauses with x1 are satisfied, x2 drops out of others
    for (long seed = 1; seed <= 6; seed++) {
      List<int[]> cnf = new ArrayList<>(cnf(seed));
      cnf.add(new int[] {1});
      cnf.add(new int[] {-2});
      cnf.add(new int[] {1, 3, -4});
      cnf.add(new int[] {2, 5, 6});
      String out = run(model(cnf, "", "solve satisfy;"), true);
      check(cnf, out);
    }
  }

  @Test
  void fixedSearchStaysWithLcg() throws IOException {
    for (long seed = 1; seed <= 4; seed++) {
      List<int[]> cnf = cnf(seed);
      String fzn =
          model(cnf, "", "solve :: bool_search(xs, input_order, indomain_min, complete) satisfy;");
      String out = run(fzn, false);
      assertFalse(out.contains("pureClauseModel"), out);
      check(cnf, out);
    }
  }

  @Test
  void otherConstraintsStayWithLcg() throws IOException {
    // at most 4 of the variables are true: a sum, not a clause
    List<int[]> cnf = List.of(new int[] {1, 2, 3}, new int[] {-1, 4});
    StringBuilder ones = new StringBuilder();
    for (int v = 1; v <= VARS; v++) {
      ones.append(v == 1 ? "" : ",").append('1');
    }
    String sum = "constraint bool_lin_le([" + ones + "],xs,4);\n";
    String out = run(model(cnf, sum, "solve satisfy;"), true);
    assertFalse(out.contains("pureClauseModel"), out);
    boolean[] value = printed(out);
    int count = 0;
    for (int v = 1; v <= VARS; v++) {
      count += value[v] ? 1 : 0;
    }
    assertTrue(count <= 4 && satisfies(cnf, value), out);
    assertEquals(1, out.split("----------", -1).length - 1, out);
  }

  private String run(String model, boolean free) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    // the tests of the build run with LCG off by default (jacop.lcg)
    List<String> args = new ArrayList<>(List.of("--lcg", "-s", "-t", "10000"));
    if (free) {
      args.add("-f");
    }
    args.add(fzn.toString());
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
