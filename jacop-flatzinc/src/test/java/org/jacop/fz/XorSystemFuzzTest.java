/*
 * XorSystemFuzzTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random small FlatZinc models of parity constraints (array_bool_xor, bool_xor, bool_not,
 * bool_eq_reif) with a few clauses, minimising the number of true variables, compared with
 * enumeration. The parity constraints form one system, so the front end posts an {@link
 * org.jacop.constraints.XorSystem} for them. Each model is solved with LCG and the explanation
 * checker on, which derives every reason of the system again, with LCG and the system turned off,
 * and with plain search.
 *
 * <pre>
 * mvn -Pmin -pl jacop-flatzinc test -Dtest=XorSystemFuzzTest -Dxorfuzz.trials=3000
 * </pre>
 */
class XorSystemFuzzTest {

  private static final int TRIALS = Integer.getInteger("xorfuzz.trials", 150);
  private static final long SEED = Long.getLong("xorfuzz.seed", 20261106L);

  @TempDir Path tmp;

  // xor(rows[i]) = parities[i] over variables 0..n-1, and clauses as positive variables
  private record Model(int n, int[][] rows, int[] parities, int[][] clauses) {}

  private static Model randomModel(Random r) {
    int n = 4 + r.nextInt(9);
    int m = 2 + r.nextInt(n);
    int[][] rows = new int[m][];
    int[] parities = new int[m];
    for (int i = 0; i < m; i++) {
      int k = 2 + r.nextInt(Math.min(n - 1, 5));
      rows[i] = new int[k];
      for (int j = 0; j < k; j++) {
        rows[i][j] = r.nextInt(n);
      }
      parities[i] = r.nextInt(2);
    }
    int[][] clauses = new int[r.nextInt(3)][];
    for (int i = 0; i < clauses.length; i++) {
      clauses[i] = new int[] {r.nextInt(n), r.nextInt(n)};
    }
    return new Model(n, rows, parities, clauses);
  }

  // the least number of true variables, or -1 when there is no solution
  private static int bruteForce(Model m) {
    int best = -1;
    for (int s = 0; s < 1 << m.n; s++) {
      boolean ok = true;
      for (int i = 0; i < m.rows.length && ok; i++) {
        int sum = m.parities[i];
        for (int c : m.rows[i]) {
          sum ^= (s >> c) & 1;
        }
        ok = sum == 0;
      }
      for (int[] cl : m.clauses) {
        ok &= ((s >> cl[0]) & 1) == 1 || ((s >> cl[1]) & 1) == 1;
      }
      if (ok && (best < 0 || Integer.bitCount(s) < best)) {
        best = Integer.bitCount(s);
      }
    }
    return best;
  }

  private static String name(int c) {
    return "x" + c;
  }

  private static String fzn(Model m) {
    StringBuilder sb = new StringBuilder();
    for (int c = 0; c < m.n; c++) {
      sb.append("var bool: ").append(name(c)).append(" :: output_var;\n");
      sb.append("var 0..1: y").append(c).append(";\n");
    }
    sb.append("var 0..").append(m.n).append(": obj :: output_var;\n");
    // the sums of the rows posted as linear equations take values of the row's parity only
    for (int i = 3; i < m.rows.length; i += 5) {
      StringBuilder values = new StringBuilder();
      for (int v = m.parities[i]; v <= 3 * m.rows[i].length + 2; v += 2) {
        values.append(values.length() > 0 ? "," : "").append(v);
      }
      sb.append("var {").append(values).append("}: s").append(i).append(";\n");
    }
    for (int i = 0; i < m.rows.length; i++) {
      int[] row = m.rows[i];
      String[] names = Arrays.stream(row).mapToObj(XorSystemFuzzTest::name).toArray(String[]::new);
      int p = m.parities[i];
      if (i % 5 == 4) {
        sb.append(table(row, p, i % 2 == 0 ? -1 : (i * 7) % m.n));
      } else if (i % 5 == 3) {
        sb.append(linear(row, i, (i * 3) % m.n));
      } else if (row.length == 2 && i % 3 == 0) {
        // a xor b = p
        sb.append(p == 1 ? "constraint bool_not(" : "constraint bool_eq(")
            .append(names[0])
            .append(", ")
            .append(names[1])
            .append(");\n");
      } else if (row.length == 3 && i % 2 == 0) {
        // c = a xor b, or c = (a == b)
        sb.append(p == 0 ? "constraint bool_xor(" : "constraint bool_eq_reif(")
            .append(String.join(", ", names))
            .append(");\n");
      } else if (p == 1) {
        sb.append("constraint array_bool_xor([").append(String.join(", ", names)).append("]);\n");
      } else {
        // xor(names) = 0: names[0] = xor(rest), as array_bool_xor over the row and true
        sb.append("constraint array_bool_xor([")
            .append(String.join(", ", names))
            .append(", true]);\n");
      }
    }
    for (int[] cl : m.clauses) {
      sb.append("constraint bool_clause([")
          .append(name(cl[0]))
          .append(", ")
          .append(name(cl[1]))
          .append("], []);\n");
    }
    StringBuilder ys = new StringBuilder();
    StringBuilder ones = new StringBuilder();
    for (int c = 0; c < m.n; c++) {
      sb.append("constraint bool2int(").append(name(c)).append(", y").append(c).append(");\n");
      ys.append(c > 0 ? ", " : "").append("y").append(c);
      ones.append(c > 0 ? ", " : "").append("1");
    }
    sb.append("constraint int_lin_eq([")
        .append(ones)
        .append(", -1], [")
        .append(ys)
        .append(", obj], 0);\n");
    sb.append("solve minimize obj;\n");
    return sb.toString();
  }

  // xor(row) = p as y_row_1 + ... + y_row_k + 2 y_even - s = 0 with s taking the values of parity
  // p only; every third such row has the coefficient 3 on its first variable
  private static String linear(int[] row, int i, int even) {
    int k = row.length;
    StringBuilder coefficients = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (int j = 0; j < k; j++) {
      coefficients.append(j == 0 && i % 3 == 0 ? "3" : "1").append(", ");
      vars.append("y").append(row[j]).append(", ");
    }
    return "constraint int_lin_eq(["
        + coefficients
        + "2, -1], ["
        + vars
        + "y"
        + even
        + ", s"
        + i
        + "], 0);\n";
  }

  // xor(row) = p as a table over the 0/1 integers y, all tuples of that parity; with a star
  // column over y[extra] when extra >= 0 (a short table)
  private static String table(int[] row, int p, int extra) {
    StringBuilder vars = new StringBuilder();
    for (int j = 0; j < row.length; j++) {
      vars.append(j > 0 ? ", " : "").append("y").append(row[j]);
    }
    if (extra >= 0) {
      vars.append(", y").append(extra);
    }
    StringBuilder tuples = new StringBuilder();
    for (int s = 0; s < 1 << row.length; s++) {
      if ((Integer.bitCount(s) & 1) != p) {
        continue;
      }
      for (int j = 0; j < row.length; j++) {
        tuples.append(tuples.length() > 0 ? ", " : "").append((s >> j) & 1);
      }
      if (extra >= 0) {
        tuples.append(", 9");
      }
    }
    if (extra >= 0) {
      return "constraint jacop_short_table_int([" + vars + "], [" + tuples + "], 9);\n";
    }
    return "constraint jacop_table_int([" + vars + "], [" + tuples + "]);\n";
  }

  // the objective of the last solution, -1 for UNSAT, null when the run did not finish
  private Integer solve(String model, String... options) throws IOException {
    String out = run(model, options);
    if (out.contains("=====UNSATISFIABLE=====")) {
      return -1;
    }
    if (!out.contains("==========")) {
      return null;
    }
    Integer last = null;
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = Integer.parseInt(line.substring(6, line.length() - 1).trim());
      }
    }
    return last;
  }

  // the output of the solver on the model
  private String run(String model, String... options) throws IOException {
    Path file = tmp.resolve("case.fzn");
    Files.writeString(file, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      List<String> args = new ArrayList<>(Arrays.asList(options));
      args.add(file.toString());
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  // a table that is an XOR, also with an integer column and as a short table, gives its row; a
  // table whose tuples span every 0/1 point (a + b + c != 1, the truncated XOR of the AES models)
  // gives none
  @Test
  void tablesGiveTheParitiesTheyImply() throws IOException {
    String vars =
        "var 0..1: a :: output_var;\nvar 0..1: b;\nvar 0..1: c;\nvar 0..1: d;\nvar 0..5: e;\n";
    String xors =
        vars
            + "constraint jacop_table_int([a, b, c, e], [0,0,0,3, 0,1,1,4, 1,0,1,5, 1,1,0,3]);\n"
            + "constraint jacop_short_table_int([b, c, d, e], [0,0,1,9, 1,1,1,9, 0,1,0,9, 1,0,0,9], 9);\n"
            + "solve satisfy;\n";
    assertTrue(run(xors, "-debug").contains("% XorSystem: 1 systems, 2 rows, 2 rows from tables"));
    String truncated =
        vars
            + "constraint jacop_table_int([a, b, c], [0,0,0, 0,1,1, 1,0,1, 1,1,0, 1,1,1]);\n"
            + "constraint jacop_table_int([b, c, d], [0,0,1, 1,1,1, 0,1,0, 1,0,0]);\n"
            + "solve satisfy;\n";
    assertTrue(!run(truncated, "-debug").contains("% XorSystem:"));
  }

  // a sum of 0/1 variables equal to a variable with odd values only (the lit-neighbour counts of
  // Lights Out) gives its row, and so does an odd coefficient; an even coefficient or a variable
  // with values of both parities gives none
  @Test
  void linearEquationsGiveTheParitiesTheyImply() throws IOException {
    String vars =
        "var 0..1: a :: output_var;\nvar 0..1: b;\nvar 0..1: c;\nvar 0..1: d;\n"
            + "var {1,3}: s;\nvar {0,2,4,6}: t;\nvar 0..5: u;\n";
    String parities =
        vars
            + "constraint int_lin_eq([1, 1, 1, -1], [a, b, c, s], 0);\n"
            + "constraint int_lin_eq([3, 1, 2, -1], [b, c, d, t], 1);\n"
            + "solve satisfy;\n";
    assertTrue(
        run(parities, "-debug")
            .contains("% XorSystem: 1 systems, 2 rows, 0 rows from tables, 2 rows from linear"));
    String mixed =
        vars
            + "constraint int_lin_eq([1, 1, 1, -1], [a, b, c, u], 0);\n"
            + "constraint int_lin_eq([1, 1, 1, 1], [b, c, d, a], 2);\n"
            + "solve satisfy;\n";
    assertTrue(!run(mixed, "-debug").contains("% XorSystem:"));
  }

  @Test
  void rootConflictOfAProbeIsKeptWithoutXorSystem() throws IOException {
    // trial 123 of seed rotation 6: a probe of the core-guided search had its level undone by a
    // clause of the LCG propagator, the root conflict that followed was taken for a failure of the
    // probed literal, and variable elimination then met an empty clause (internal error)
    String model =
        String.join(
                "\n",
                "var bool: x0 :: output_var;",
                "var 0..1: y0;",
                "var bool: x1 :: output_var;",
                "var 0..1: y1;",
                "var bool: x2 :: output_var;",
                "var 0..1: y2;",
                "var bool: x3 :: output_var;",
                "var 0..1: y3;",
                "var bool: x4 :: output_var;",
                "var 0..1: y4;",
                "var bool: x5 :: output_var;",
                "var 0..1: y5;",
                "var bool: x6 :: output_var;",
                "var 0..1: y6;",
                "var bool: x7 :: output_var;",
                "var 0..1: y7;",
                "var bool: x8 :: output_var;",
                "var 0..1: y8;",
                "var bool: x9 :: output_var;",
                "var 0..1: y9;",
                "var 0..10: obj :: output_var;",
                "constraint array_bool_xor([x2, x5, x2, x2]);",
                "constraint array_bool_xor([x3, x4]);",
                "constraint array_bool_xor([x1, x5, x5, x2, x1]);",
                "constraint bool_not(x7, x9);",
                "constraint jacop_table_int([y2, y3], [0, 0, 1, 1]);",
                "constraint array_bool_xor([x6, x1, x9, x6, x1, x2]);",
                "constraint array_bool_xor([x3, x1, x1, x5, true]);",
                "constraint array_bool_xor([x3, x0, x3, x6, x0, true]);",
                "constraint array_bool_xor([x8, x0, x7, x2, x6, true]);",
                "constraint jacop_short_table_int([y0, y7, y7, y3], [0, 0, 0, 9, 1, 1, 0, 9, 1, 0, 1, 9, 0, 1, 1, 9], 9);",
                "constraint bool_clause([x8, x4], []);",
                "constraint bool_clause([x5, x9], []);",
                "constraint bool2int(x0, y0);",
                "constraint bool2int(x1, y1);",
                "constraint bool2int(x2, y2);",
                "constraint bool2int(x3, y3);",
                "constraint bool2int(x4, y4);",
                "constraint bool2int(x5, y5);",
                "constraint bool2int(x6, y6);",
                "constraint bool2int(x7, y7);",
                "constraint bool2int(x8, y8);",
                "constraint bool2int(x9, y9);",
                "constraint int_lin_eq([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1], [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, obj], 0);",
                "solve minimize obj;")
            + "\n";
    // the model has no solution: plain depth-first search, without LCG, agrees with enumeration
    assertEquals(Integer.valueOf(-1), solve(model, "--lcg", "off"));
    System.setProperty("org.jacop.fz.xorSystem", "false");
    try {
      assertEquals(Integer.valueOf(-1), solve(model, "--lcg"));
    } finally {
      System.clearProperty("org.jacop.fz.xorSystem");
    }
  }

  @Test
  void parityModelsHaveTheOptimumOfEnumeration() throws IOException {
    Random r = new Random(SEED);
    List<String> failures = new ArrayList<>();
    System.setProperty("jacop.lcg.check", "true");
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < 5; trial++) {
        Model m = randomModel(r);
        int expected = bruteForce(m);
        String model = fzn(m);
        String[][] runs = {{"--lcg"}, {"--lcg", "-f"}, {"--lcg", "off"}};
        for (String[] options : runs) {
          Integer got = solve(model, options);
          if (got == null || got != expected) {
            failures.add(
                "trial "
                    + trial
                    + " "
                    + String.join(" ", options)
                    + ": expected "
                    + expected
                    + ", got "
                    + got
                    + "\n"
                    + model);
          }
        }
        System.setProperty("org.jacop.fz.xorSystem", "false");
        try {
          Integer got = solve(model, "--lcg");
          if (got == null || got != expected) {
            failures.add(
                "trial "
                    + trial
                    + " without XorSystem: expected "
                    + expected
                    + ", got "
                    + got
                    + "\n"
                    + model);
          }
        } finally {
          System.clearProperty("org.jacop.fz.xorSystem");
        }
      }
    } catch (IllegalStateException e) {
      failures.add(e.getMessage());
    } finally {
      System.clearProperty("jacop.lcg.check");
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
  }

  // clauses as literals: v + 1 for variable v, -(v + 1) for its negation
  private record CnfModel(int n, List<int[]> clauses) {}

  // the clauses of xor(t_1, ..., t_k) = p where each term t_i is the disjunction of its variables
  // (one variable: a plain XOR; two: an XOR lifted by substitution, as or_randxor)
  private static void liftedXor(int[][] terms, int p, List<int[]> out, Random r) {
    int k = terms.length;
    for (int s = 0; s < 1 << k; s++) {
      if ((Integer.bitCount(s) & 1) == p) {
        continue;
      }
      // the clause excludes the terms at s: t_i if t_i = 0 at s, not t_i otherwise, and not t_i
      // (all variables of t_i false) is distributed over the variables of t_i
      List<List<Integer>> partial = new ArrayList<>();
      partial.add(new ArrayList<>());
      for (int i = 0; i < k; i++) {
        List<List<Integer>> next = new ArrayList<>();
        for (List<Integer> c : partial) {
          if ((s >> i & 1) == 0) {
            List<Integer> d = new ArrayList<>(c);
            for (int v : terms[i]) {
              d.add(v + 1);
            }
            next.add(d);
          } else {
            for (int v : terms[i]) {
              List<Integer> d = new ArrayList<>(c);
              d.add(-(v + 1));
              next.add(d);
            }
          }
        }
        partial = next;
      }
      for (List<Integer> c : partial) {
        // sometimes a clause is shortened (unless r is null): a stronger clause subsuming it
        if (r != null && c.size() > 2 && r.nextInt(6) == 0) {
          c.remove(r.nextInt(c.size()));
        }
        out.add(c.stream().mapToInt(Integer::intValue).toArray());
      }
    }
  }

  private static CnfModel randomCnf(Random r) {
    int n = 5 + r.nextInt(8);
    List<int[]> clauses = new ArrayList<>();
    int xors = 1 + r.nextInt(5);
    for (int x = 0; x < xors; x++) {
      int k = 2 + r.nextInt(3);
      int[][] terms = new int[k][];
      for (int i = 0; i < k; i++) {
        terms[i] =
            r.nextInt(3) == 0 ? new int[] {r.nextInt(n), r.nextInt(n)} : new int[] {r.nextInt(n)};
      }
      liftedXor(terms, r.nextInt(2), clauses, r);
    }
    // an AND gate now and then, and a few other clauses
    if (r.nextBoolean()) {
      int g = r.nextInt(n);
      int a = r.nextInt(n);
      int b = r.nextInt(n);
      clauses.add(new int[] {-(g + 1), a + 1});
      clauses.add(new int[] {-(g + 1), b + 1});
      clauses.add(new int[] {g + 1, -(a + 1), -(b + 1)});
    }
    for (int i = r.nextInt(3); i > 0; i--) {
      clauses.add(
          new int[] {
            (r.nextInt(n) + 1) * (r.nextBoolean() ? 1 : -1),
            (r.nextInt(n) + 1) * (r.nextBoolean() ? 1 : -1),
            (r.nextInt(n) + 1) * (r.nextBoolean() ? 1 : -1)
          });
    }
    return new CnfModel(n, clauses);
  }

  // the least number of true variables, or -1 when there is no solution
  private static int bruteForce(CnfModel m) {
    int best = -1;
    for (int s = 0; s < 1 << m.n; s++) {
      boolean ok = true;
      for (int[] c : m.clauses) {
        boolean sat = false;
        for (int l : c) {
          sat |= ((s >> (Math.abs(l) - 1) & 1) == 1) == (l > 0);
        }
        if (!sat) {
          ok = false;
          break;
        }
      }
      if (ok && (best < 0 || Integer.bitCount(s) < best)) {
        best = Integer.bitCount(s);
      }
    }
    return best;
  }

  private static String fzn(CnfModel m, boolean minimize) {
    StringBuilder sb = new StringBuilder();
    for (int c = 0; c < m.n; c++) {
      sb.append("var bool: ").append(name(c)).append(" :: output_var;\n");
      sb.append("var 0..1: y").append(c).append(";\n");
    }
    sb.append("var 0..").append(m.n).append(": obj :: output_var;\n");
    for (int[] c : m.clauses) {
      List<String> pos = new ArrayList<>();
      List<String> neg = new ArrayList<>();
      for (int l : c) {
        (l > 0 ? pos : neg).add(name(Math.abs(l) - 1));
      }
      sb.append("constraint bool_clause([")
          .append(String.join(", ", pos))
          .append("], [")
          .append(String.join(", ", neg))
          .append("]);\n");
    }
    StringBuilder ys = new StringBuilder();
    StringBuilder ones = new StringBuilder();
    for (int c = 0; c < m.n; c++) {
      sb.append("constraint bool2int(").append(name(c)).append(", y").append(c).append(");\n");
      ys.append(c > 0 ? ", " : "").append("y").append(c);
      ones.append(c > 0 ? ", " : "").append("1");
    }
    sb.append("constraint int_lin_eq([")
        .append(ones)
        .append(", -1], [")
        .append(ys)
        .append(", obj], 0);\n");
    sb.append(minimize ? "solve minimize obj;\n" : "solve satisfy;\n");
    return sb.toString();
  }

  // the XORs written as clauses, plain (some clauses subsumed by shorter ones) or lifted by
  // substitution, give rows; an AND gate gives none; a system of plain rows without a cycle is
  // left out
  @Test
  void clausesGiveTheParitiesTheyEncode() throws IOException {
    List<int[]> plain = new ArrayList<>();
    liftedXor(new int[][] {{0}, {1}, {2}}, 1, plain, null);
    liftedXor(new int[][] {{2}, {3}, {4}, {5}}, 0, plain, null);
    // x6 = x0 x1, and the clause x0 or x1 subsuming two of the clauses of the first XOR; with
    // that clause the gate allows only 100, 010 and 111 of x0 x1 x6, so x0 + x1 + x6 = 1 is a
    // third row
    plain.add(new int[] {-7, 1});
    plain.add(new int[] {-7, 2});
    plain.add(new int[] {7, -1, -2});
    plain.add(new int[] {1, 2});
    String out = run(fzn(new CnfModel(7, plain), false), "-debug");
    assertTrue(out.contains("% XorSystem: 1 systems, 3 rows"), out);
    assertTrue(out.contains("3 rows from clauses"), out);
    // without that clause the gate gives no row, and the two XORs, which share only x2, form no
    // cycle: unit propagation on their clauses does what Gauss-Jordan elimination would
    plain.removeLast();
    String gate = run(fzn(new CnfModel(7, plain), false), "-s", "-v");
    assertTrue(gate.contains("%%%mzn-stat: xorSystems=0"), gate);
    assertTrue(gate.contains("%%%mzn-stat: xorAcyclicSystems=1"), gate);
    List<int[]> lifted = new ArrayList<>();
    liftedXor(new int[][] {{0, 1}, {2, 3}, {4, 5}}, 1, lifted, null);
    liftedXor(new int[][] {{0, 1}, {2, 3}, {6}}, 0, lifted, null);
    liftedXor(new int[][] {{0, 1}, {4, 5}, {7}}, 0, lifted, null);
    String quadratic = run(fzn(new CnfModel(8, lifted), false), "-debug", "-s", "-v");
    assertTrue(quadratic.contains("%%%mzn-stat: xorQuadraticRows=3"), quadratic);
    assertTrue(quadratic.contains("%%%mzn-stat: xorProducts=3"), quadratic);
  }

  @Test
  void clauseParityModelsHaveTheOptimumOfEnumeration() throws IOException {
    Random r = new Random(SEED + 1);
    List<String> failures = new ArrayList<>();
    System.setProperty("jacop.lcg.check", "true");
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < 5; trial++) {
        CnfModel m = randomCnf(r);
        int expected = bruteForce(m);
        String model = fzn(m, true);
        String[][] runs = {{"--lcg"}, {"--lcg", "-f"}, {"--lcg", "off"}};
        for (String[] options : runs) {
          Integer got = solve(model, options);
          if (got == null || got != expected) {
            failures.add(
                "trial "
                    + trial
                    + " "
                    + String.join(" ", options)
                    + ": expected "
                    + expected
                    + ", got "
                    + got
                    + "\n"
                    + model);
          }
        }
      }
    } catch (IllegalStateException e) {
      failures.add(e.getMessage());
    } finally {
      System.clearProperty("jacop.lcg.check");
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
  }
}
