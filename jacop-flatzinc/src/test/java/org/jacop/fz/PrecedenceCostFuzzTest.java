/*
 * PrecedenceCostFuzzTest.java
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
 * Random small FlatZinc models of earliness and tardiness costs under precedences, written as
 * MiniZinc writes rcpsp-wet (int_max(0, a, y) over a = s - due or due - s, an int_lin_eq for the
 * objective, int_lin_le precedences, and pairs of tasks that must not overlap as two int_lin_le_imp
 * and a bool_clause), so that the front end posts a {@link org.jacop.constraints.PrecedenceCost}.
 * Each model is solved with the detection on (default search, LCG with the explanation checker, LCG
 * with free search) and compared with the optimum of the decomposition alone (detection off,
 * depth-first search).
 *
 * <pre>
 * mvn -Pmin -pl jacop-flatzinc test -Dtest=PrecedenceCostFuzzTest -Dprecedencefuzz.trials=1500
 * </pre>
 */
class PrecedenceCostFuzzTest {

  private static final int TRIALS = Integer.getInteger("precedencefuzz.trials", 100);
  private static final long SEED = Long.getLong("precedencefuzz.seed", 20261106L);

  @TempDir Path tmp;

  private static String fzn(Random r) {
    int n = 3 + r.nextInt(5);
    int horizon = 10 + r.nextInt(8);
    int[] d = new int[n];
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      d[i] = 1 + r.nextInt(4);
      sb.append("var 0..").append(horizon).append(": s").append(i).append(" :: output_var;\n");
    }
    List<String> constraints = new ArrayList<>();
    for (int j = 1; j < n; j++) {
      for (int i = 0; i < j; i++) {
        if (r.nextInt(3) == 0) {
          constraints.add("constraint int_lin_le([1,-1],[s" + i + ",s" + j + "]," + (-d[i]) + ");");
        } else if (r.nextInt(4) == 0) {
          // i and j do not overlap
          int b = constraints.size();
          sb.append("var bool: b").append(b).append(";\nvar bool: c").append(b).append(";\n");
          constraints.add(
              "constraint int_lin_le_imp([1,-1],[s"
                  + i
                  + ",s"
                  + j
                  + "],"
                  + (-d[i])
                  + ",b"
                  + b
                  + ");");
          constraints.add(
              "constraint int_lin_le_imp([1,-1],[s"
                  + j
                  + ",s"
                  + i
                  + "],"
                  + (-d[j])
                  + ",c"
                  + b
                  + ");");
          constraints.add("constraint bool_clause([b" + b + ",c" + b + "],[]);");
        }
      }
    }
    List<String> ys = new ArrayList<>();
    List<Integer> ws = new ArrayList<>();
    int bound = 0;
    for (int i = 0; i < n; i++) {
      int due = r.nextInt(horizon);
      int e = r.nextInt(5);
      int t = r.nextInt(5);
      if (t > 0) {
        String y = "late" + i;
        if (due == 0) {
          sb.append("var 0..").append(horizon).append(": ").append(y).append(";\n");
          constraints.add("constraint int_max(0,s" + i + "," + y + ");");
        } else {
          sb.append("var ").append(-due).append("..").append(horizon - due);
          sb.append(": a").append(y).append(";\n");
          sb.append("var 0..").append(horizon).append(": ").append(y).append(";\n");
          constraints.add("constraint int_lin_eq([1,-1],[s" + i + ",a" + y + "]," + due + ");");
          constraints.add(
              r.nextBoolean()
                  ? "constraint int_max(0,a" + y + "," + y + ");"
                  : "constraint int_max(a" + y + ",0," + y + ");");
        }
        ys.add(y);
        ws.add(t);
        bound += t * horizon;
      }
      if (e > 0) {
        String y = "early" + i;
        sb.append("var ").append(due - horizon).append("..").append(due);
        sb.append(": a").append(y).append(";\n");
        sb.append("var 0..").append(horizon).append(": ").append(y).append(";\n");
        constraints.add("constraint int_lin_eq([-1,-1],[s" + i + ",a" + y + "]," + (-due) + ");");
        constraints.add("constraint int_max(0,a" + y + "," + y + ");");
        ys.add(y);
        ws.add(e);
        bound += e * horizon;
      }
    }
    sb.append("var 0..").append(bound).append(": obj :: output_var;\n");
    StringBuilder coefs = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    boolean negative = r.nextBoolean();
    coefs.append(negative ? "1" : "-1");
    vars.append("obj");
    for (int k = 0; k < ys.size(); k++) {
      coefs.append(",").append(negative ? -ws.get(k) : ws.get(k));
      vars.append(",").append(ys.get(k));
    }
    constraints.add("constraint int_lin_eq([" + coefs + "],[" + vars + "],0);");
    for (String c : constraints) {
      sb.append(c).append('\n');
    }
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
    if (out.contains("% precedence cost:")) {
      detected++;
    }
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

  private int detected;

  @Test
  void earlinessTardinessModelsHaveTheOptimumOfTheDecomposition() throws IOException {
    Random r = new Random(SEED);
    List<String> failures = new ArrayList<>();
    int withPrecedences = 0;
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < 5; trial++) {
        String model = fzn(r);
        if (model.contains("int_lin_le([1,-1]") && model.split("int_max").length > 2) {
          withPrecedences++;
        }
        Integer expected;
        System.setProperty("org.jacop.fz.precedenceCost", "false");
        try {
          expected = solve(model, "--lcg", "off");
        } finally {
          System.clearProperty("org.jacop.fz.precedenceCost");
        }
        System.setProperty("jacop.lcg.check", "true");
        System.setProperty("org.jacop.fz.precedenceCost", "true");
        try {
          String[][] runs = {{"--lcg", "off", "-debug"}, {"-debug"}, {"-f", "-debug"}};
          for (String[] options : runs) {
            Integer got = solve(model, options);
            if (got == null || !got.equals(expected)) {
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
        } finally {
          System.clearProperty("jacop.lcg.check");
          System.clearProperty("org.jacop.fz.precedenceCost");
        }
      }
    } catch (IllegalStateException e) {
      failures.add(e.getMessage());
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
    // the three runs with -debug report the constraint for most models with precedences and two
    // terms (not when no precedence links two tasks with costs)
    assertTrue(2 * detected >= 3 * withPrecedences, detected + " detections, " + withPrecedences);
  }
}
