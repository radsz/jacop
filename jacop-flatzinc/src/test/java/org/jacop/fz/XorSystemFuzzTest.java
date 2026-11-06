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
    for (int i = 0; i < m.rows.length; i++) {
      int[] row = m.rows[i];
      String[] names = Arrays.stream(row).mapToObj(XorSystemFuzzTest::name).toArray(String[]::new);
      int p = m.parities[i];
      if (row.length == 2 && i % 3 == 0) {
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

  // the objective of the last solution, -1 for UNSAT, null when the run did not finish
  private Integer solve(String model, String... options) throws IOException {
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
    String out = buffer.toString(StandardCharsets.UTF_8);
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
}
