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
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
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
    // a weighted sum of the variables at most 4, x1 at weight 2: neither a clause nor a
    // cardinality row
    List<int[]> cnf = List.of(new int[] {1, 2, 3}, new int[] {-1, 4});
    StringBuilder ones = new StringBuilder();
    for (int v = 1; v <= VARS; v++) {
      ones.append(v == 1 ? "2" : ",1");
    }
    String sum = "constraint bool_lin_le([" + ones + "],xs,4);\n";
    String out = run(model(cnf, sum, "solve satisfy;"), true);
    assertFalse(out.contains("pureClauseModel"), out);
    boolean[] value = printed(out);
    int count = value[1] ? 1 : 0;
    for (int v = 1; v <= VARS; v++) {
      count += value[v] ? 1 : 0;
    }
    assertTrue(count <= 4 && satisfies(cnf, value), out);
    assertEquals(1, out.split("----------", -1).length - 1, out);
  }

  private static final int SMALL = 16;

  private static final Pattern SMALL_MODEL =
      Pattern.compile("ys = array1d\\(1\\.\\.\\d+, \\[(.*?)\\]\\);");

  // a random model of linear rows over SMALL 0/1 variables that are each a few clauses: clauses
  // over literals (a negated literal 1 - x moves 1 to the right-hand side), x + y <= 1, exactly one
  // of three and x -> y and z (2 x - y - z <= 0); with windows, also y[i] + y[i+1] + y[i+2] <= 1
  // over the first eight variables, which the sequence detector posts as one sequence too, and with
  // wide, at most 4 of 9 variables, 126 clauses, which JaSAT gets as a counter instead. Each row
  // holds its relation (-1 for le, 0 for eq, 1 for ge), its right-hand side and its weights
  private static List<long[]> rows(long seed, boolean windows, boolean wide) {
    Random random = new Random(seed);
    List<long[]> rows = new ArrayList<>();
    int count = 22 + random.nextInt(10);
    for (int r = 0; r < count; r++) {
      long[] row = new long[2 + SMALL];
      int[] v = new int[3];
      for (int k = 0; k < 3; k++) {
        do {
          v[k] = random.nextInt(SMALL);
        } while (k > 0 && (v[k] == v[0] || k > 1 && v[k] == v[1]));
      }
      switch (random.nextInt(6)) {
        case 0, 1, 2 -> {
          row[0] = 1;
          row[1] = 1;
          for (int k = 0; k < 3; k++) {
            boolean negated = random.nextBoolean();
            row[2 + v[k]] = negated ? -1 : 1;
            row[1] -= negated ? 1 : 0;
          }
        }
        case 3 -> {
          row[0] = -1;
          row[1] = 1;
          row[2 + v[0]] = 1;
          row[2 + v[1]] = 1;
        }
        case 4 -> {
          row[0] = 0;
          row[1] = 1;
          for (int k = 0; k < 3; k++) {
            row[2 + v[k]] = 1;
          }
        }
        default -> {
          row[0] = -1;
          row[1] = 0;
          row[2 + v[0]] = 2;
          row[2 + v[1]] = -1;
          row[2 + v[2]] = -1;
        }
      }
      rows.add(row);
    }
    if (windows) {
      for (int i = 0; i + 3 <= 8; i++) {
        long[] row = new long[2 + SMALL];
        row[0] = -1;
        row[1] = 1;
        for (int k = i; k < i + 3; k++) {
          row[2 + k] = 1;
        }
        rows.add(row);
      }
    }
    if (wide) {
      long[] row = new long[2 + SMALL];
      row[0] = -1;
      row[1] = 4;
      for (int k = 0; k < 9; k++) {
        row[2 + k] = 1;
      }
      rows.add(row);
    }
    return rows;
  }

  private static boolean holds(List<long[]> rows, int assignment) {
    for (long[] row : rows) {
      long sum = 0;
      for (int i = 0; i < SMALL; i++) {
        sum += row[2 + i] * (assignment >> i & 1);
      }
      boolean ok = row[0] < 0 ? sum <= row[1] : row[0] == 0 ? sum == row[1] : sum >= row[1];
      if (!ok) {
        return false;
      }
    }
    return true;
  }

  private static String linearModel(List<long[]> rows) {
    StringBuilder s = new StringBuilder();
    StringBuilder ys = new StringBuilder();
    for (int v = 1; v <= SMALL; v++) {
      s.append("var 0..1: y").append(v).append(";\n");
      ys.append(v == 1 ? "" : ",").append('y').append(v);
    }
    s.append("array [1..").append(SMALL).append("] of var int: ys:: output_array([1..");
    s.append(SMALL).append("]) = [").append(ys).append("];\n");
    for (long[] row : rows) {
      StringBuilder w = new StringBuilder();
      StringBuilder x = new StringBuilder();
      for (int i = 0; i < SMALL; i++) {
        if (row[2 + i] != 0) {
          w.append(w.isEmpty() ? "" : ",").append(row[2 + i]);
          x.append(x.isEmpty() ? "" : ",").append('y').append(i + 1);
        }
      }
      if (w.isEmpty()) {
        continue;
      }
      // ge as -sum <= -rhs
      if (row[0] > 0) {
        w = new StringBuilder();
        for (int i = 0; i < SMALL; i++) {
          if (row[2 + i] != 0) {
            w.append(w.isEmpty() ? "" : ",").append(-row[2 + i]);
          }
        }
      }
      String op = row[0] == 0 ? "int_lin_eq" : "int_lin_le";
      long rhs = row[0] > 0 ? -row[1] : row[1];
      s.append("constraint ").append(op).append("([").append(w).append("],[").append(x);
      s.append("],").append(rhs).append(");\n");
    }
    s.append("solve satisfy;\n");
    return s.toString();
  }

  @Test
  void clauseShapedRowsGoToJaSat() throws IOException {
    int routed = 0;
    int unsat = 0;
    int runs = 0;
    for (long seed = 1; seed <= 24; seed++) {
      boolean windows = seed % 3 == 0;
      boolean wide = seed % 4 == 0;
      List<long[]> rows = rows(seed, windows, wide);
      int solutions = 0;
      for (int a = 0; a < 1 << SMALL; a++) {
        solutions += holds(rows, a) ? 1 : 0;
      }
      unsat += solutions == 0 ? 1 : 0;
      for (boolean free : new boolean[] {false, true}) {
        String out = run(linearModel(rows), free);
        runs++;
        boolean pure = out.contains("%%%mzn-stat: pureClauseModel=true");
        routed += pure ? 1 : 0;
        if (wide && pure) {
          // at most 4 of 9 is a cardinality row, written as the clauses of its counter
          assertFalse(out.contains("%%%mzn-stat: pureClauseCardinalities=0"), out);
        }
        if (solutions == 0) {
          assertTrue(out.contains("=====UNSATISFIABLE====="), out);
          continue;
        }
        Matcher m = SMALL_MODEL.matcher(out);
        assertTrue(m.find(), out);
        String[] values = m.group(1).split(",");
        int a = 0;
        for (int i = 0; i < SMALL; i++) {
          a |= Integer.parseInt(values[i].trim()) << i;
        }
        assertTrue(holds(rows, a), out);
      }
    }
    assertTrue(routed >= runs / 2, routed + " of " + runs + " runs given to JaSAT");
    assertTrue(unsat > 0 && unsat < 24, unsat + " unsatisfiable");
  }

  // a random model over SMALL 0/1 variables of a few clauses and cardinality rows: sums of 6 to 16
  // literals (x or 1 - x) at most, at least or equal to a bound, as the rows of rows(...)
  private static List<long[]> cardinalityRows(long seed) {
    Random random = new Random(seed);
    List<long[]> rows = new ArrayList<>();
    for (int r = 0; r < 6; r++) {
      long[] row = new long[2 + SMALL];
      row[0] = 1;
      row[1] = 1;
      for (int k = 0; k < 3; k++) {
        int v = random.nextInt(SMALL);
        if (row[2 + v] == 0) {
          boolean negated = random.nextBoolean();
          row[2 + v] = negated ? -1 : 1;
          row[1] -= negated ? 1 : 0;
        }
      }
      rows.add(row);
    }
    int count = 1 + random.nextInt(3);
    for (int r = 0; r < count; r++) {
      long[] row = new long[2 + SMALL];
      int n = 6 + random.nextInt(SMALL - 5);
      int k = random.nextInt(n + 1);
      row[0] = random.nextInt(3) - 1;
      row[1] = k;
      int placed = 0;
      while (placed < n) {
        int v = random.nextInt(SMALL);
        if (row[2 + v] == 0) {
          boolean negated = random.nextInt(4) == 0;
          row[2 + v] = negated ? -1 : 1;
          row[1] -= negated ? 1 : 0;
          placed++;
        }
      }
      rows.add(row);
    }
    return rows;
  }

  @Test
  void cardinalityRowsGoToJaSatAsCounters() throws IOException {
    int routed = 0;
    int runs = 0;
    int unsat = 0;
    for (long seed = 1; seed <= 20; seed++) {
      List<long[]> rows = cardinalityRows(seed);
      int solutions = 0;
      for (int a = 0; a < 1 << SMALL; a++) {
        solutions += holds(rows, a) ? 1 : 0;
      }
      unsat += solutions == 0 ? 1 : 0;
      // split for lazy clause generation into blocks of at most 4 terms, which are read back
      String[] split =
          seed % 2 == 0 ? new String[] {"--free-config", "lcg-split=4"} : new String[0];
      for (boolean free : new boolean[] {false, true}) {
        String out = run(linearModel(rows), free, split);
        runs++;
        if (out.contains("%%%mzn-stat: pureClauseModel=true")
            && !out.contains("%%%mzn-stat: pureClauseCardinalities=0")) {
          routed++;
        }
        if (solutions == 0) {
          assertTrue(out.contains("=====UNSATISFIABLE====="), out);
          continue;
        }
        Matcher m = SMALL_MODEL.matcher(out);
        assertTrue(m.find(), out);
        String[] values = m.group(1).split(",");
        int a = 0;
        for (int i = 0; i < SMALL; i++) {
          a |= Integer.parseInt(values[i].trim()) << i;
        }
        assertTrue(holds(rows, a), out);
      }
    }
    assertTrue(routed >= runs / 3, routed + " of " + runs + " runs given to JaSAT with counters");
    assertTrue(unsat > 0 && unsat < 20, unsat + " unsatisfiable");
  }

  @Test
  void theDomainOfASumLeftOutIsKept() {
    // ten 5-cycles of x + y <= 1 over 50 0/1 variables (at most 2 of each cycle, 20 in all) and a
    // sum s = y1 + ... + y50 whose domain 21..50 is the only row that asks for more: the sum is
    // left out of the clauses, and its domain must stay as two rows over the y (dbsg_50_25_4_15
    // of the Pseudo-Boolean Competition 2016 kept a split row's right-hand side as the domain of
    // its block sum, and JaSAT found a model of the clauses without it)
    Store store = new Store();
    IntVar[] y = new IntVar[50];
    for (int i = 0; i < y.length; i++) {
      y[i] = new IntVar(store, "y" + i, 0, 1);
    }
    for (int c = 0; c < 10; c++) {
      for (int i = 0; i < 5; i++) {
        IntVar[] pair = {y[5 * c + i], y[5 * c + (i + 1) % 5]};
        store.impose(new LinearInt(pair, new int[] {1, 1}, "<=", 1));
      }
    }
    IntVar sum = new IntVar(store, "s", 21, 50);
    IntVar[] all = new IntVar[51];
    int[] weights = new int[51];
    System.arraycopy(y, 0, all, 0, 50);
    Arrays.fill(weights, 1);
    all[50] = sum;
    weights[50] = -1;
    store.impose(new LinearInt(all, weights, "==", 0));
    assertTrue(store.consistency());
    PureClauseModel cnf =
        PureClauseModel.of(
            store,
            new ArrayList<>(),
            Collections.newSetFromMap(new IdentityHashMap<>()),
            Map.of(),
            () -> y);
    assertTrue(cnf != null && cnf.cardinalityRows > 0);
    assertEquals(CdclSolver.UNSAT, cnf.solver.solve());
  }

  // the pigeonhole formula of p pigeons and h holes: each pigeon in a hole, no two in one hole;
  // its pigeons and its holes are interchangeable, so symmetry breaking posts lex-leader
  // constraints, which JaSAT gets as clauses
  private static String pigeons(int p, int h) {
    StringBuilder s = new StringBuilder();
    StringBuilder all = new StringBuilder();
    for (int i = 0; i < p; i++) {
      for (int j = 0; j < h; j++) {
        s.append("var bool: q").append(i).append('_').append(j).append(";\n");
        all.append(all.isEmpty() ? "" : ",").append('q').append(i).append('_').append(j);
      }
    }
    s.append("array [1..").append(p * h).append("] of var bool: qs:: output_array([1..");
    s.append(p * h).append("]) = [").append(all).append("];\n");
    for (int i = 0; i < p; i++) {
      StringBuilder some = new StringBuilder();
      for (int j = 0; j < h; j++) {
        some.append(some.isEmpty() ? "" : ",").append('q').append(i).append('_').append(j);
      }
      s.append("constraint bool_clause([").append(some).append("],[]);\n");
    }
    for (int j = 0; j < h; j++) {
      for (int i = 0; i < p; i++) {
        for (int k = i + 1; k < p; k++) {
          s.append("constraint bool_clause([],[q").append(i).append('_').append(j);
          s.append(",q").append(k).append('_').append(j).append("]);\n");
        }
      }
    }
    s.append("solve satisfy;\n");
    return s.toString();
  }

  @Test
  void symmetryBreakingOfClausesGoesToJaSatAsClauses() throws IOException {
    Pattern qs = Pattern.compile("qs = array1d\\(1\\.\\.\\d+, \\[(.*?)\\]\\);");
    for (int h = 3; h <= 6; h++) {
      // the root refutation of the linear relaxation decides the unsatisfiable ones
      String out = run(pigeons(h + 1, h), true, "--symmetry", "on");
      assertTrue(out.contains("=====UNSATISFIABLE====="), out);
      out = run(pigeons(h, h), false, "--symmetry", "on");
      assertTrue(out.contains("%%%mzn-stat: pureClauseModel=true"), out);
      assertFalse(out.contains("%%%mzn-stat: pureClauseLexPairs=0"), out);
      Matcher m = qs.matcher(out);
      assertTrue(m.find(), out);
      String[] values = m.group(1).split(",");
      // a permutation: one hole per pigeon, one pigeon per hole
      for (int i = 0; i < h; i++) {
        int row = 0;
        int column = 0;
        for (int j = 0; j < h; j++) {
          row += "true".equals(values[i * h + j].trim()) ? 1 : 0;
          column += "true".equals(values[j * h + i].trim()) ? 1 : 0;
        }
        assertEquals(1, row, out);
        assertEquals(1, column, out);
      }
    }
  }

  @Test
  void symmetricCnfsKeepTheirAnswer() throws IOException {
    // a random CNF closed under swapping variable i with i + VARS / 2: symmetry breaking orders the
    // two halves, and JaSAT gets the lex-leader constraints as clauses
    int routed = 0;
    int lexed = 0;
    int unsat = 0;
    for (long seed = 1; seed <= 16; seed++) {
      List<int[]> half = cnf(seed).subList(0, 108);
      List<int[]> cnf = new ArrayList<>(half);
      for (int[] clause : half) {
        int[] image = new int[clause.length];
        for (int i = 0; i < clause.length; i++) {
          int v = Math.abs(clause[i]);
          int w = v <= VARS / 2 ? v + VARS / 2 : v - VARS / 2;
          image[i] = clause[i] > 0 ? w : -w;
        }
        cnf.add(image);
      }
      unsat += satisfiable(cnf) ? 0 : 1;
      for (boolean free : new boolean[] {false, true}) {
        String out = run(model(cnf, "", "solve satisfy;"), free, "--symmetry", "on");
        routed += out.contains("%%%mzn-stat: pureClauseModel=true") ? 1 : 0;
        lexed += out.contains("%%%mzn-stat: pureClauseLexPairs=0") ? 0 : 1;
        check(cnf, out);
      }
    }
    assertTrue(routed >= 16, routed + " of 32 runs given to JaSAT");
    assertTrue(lexed >= 8, lexed + " runs with lex-leader clauses");
    assertTrue(unsat > 0 && unsat < 16, unsat + " unsatisfiable");
  }

  private String run(String model, boolean free, String... extra) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    // the tests of the build run with LCG off by default (jacop.lcg)
    List<String> args = new ArrayList<>(List.of("--lcg", "-s", "-t", "10000"));
    if (free) {
      args.add("-f");
    }
    args.addAll(List.of(extra));
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
