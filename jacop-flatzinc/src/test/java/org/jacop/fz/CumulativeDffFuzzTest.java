/*
 * CumulativeDffFuzzTest.java
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
 * Random small RCPSP models in FlatZinc (one or two cumulatives with fixed or two-valued resource
 * uses, precedences, makespan objective). Each is solved with the redundant resources of dual
 * feasible functions ({@code org.jacop.fz.cumulativeDff=3}, variable uses too, at the root only or
 * at every node in turn) without LCG, with LCG and the explanation checker, and with LCG and free
 * search, and compared with the optimum without them.
 *
 * <pre>
 * mvn -Pmin -pl jacop-flatzinc test -Dtest=CumulativeDffFuzzTest -Dcumulativedff.trials=2000
 * </pre>
 */
class CumulativeDffFuzzTest {

  private static final int TRIALS = Integer.getInteger("cumulativedff.trials", 60);
  private static final long SEED = Long.getLong("cumulativedff.seed", 20261108L);

  @TempDir Path tmp;

  private int posted;

  private static String fzn(Random r) {
    int n = 4 + r.nextInt(5);
    int horizon = 0;
    int[] d = new int[n];
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      d[i] = 1 + r.nextInt(4);
      horizon += d[i];
    }
    for (int i = 0; i < n; i++) {
      sb.append("var 0..").append(horizon).append(": s").append(i).append(" :: output_var;\n");
    }
    List<String> constraints = new ArrayList<>();
    int resources = 1 + r.nextInt(2);
    for (int k = 0; k < resources; k++) {
      int c = 3 + r.nextInt(10);
      StringBuilder uses = new StringBuilder();
      for (int i = 0; i < n; i++) {
        int u = 1 + r.nextInt(c);
        if (r.nextInt(4) == 0) {
          // a use with two values, as a mode choice gives
          String v = "u" + k + "_" + i;
          int w = 1 + r.nextInt(c);
          sb.append("var {").append(Math.min(u, w)).append(",").append(Math.max(u, w));
          sb.append("}: ").append(v).append(";\n");
          uses.append(i == 0 ? "" : ",").append(v);
        } else {
          uses.append(i == 0 ? "" : ",").append(u);
        }
      }
      StringBuilder starts = new StringBuilder();
      StringBuilder lengths = new StringBuilder();
      for (int i = 0; i < n; i++) {
        starts.append(i == 0 ? "" : ",").append("s").append(i);
        lengths.append(i == 0 ? "" : ",").append(d[i]);
      }
      constraints.add(
          "constraint jacop_cumulative(["
              + starts
              + "],["
              + lengths
              + "],["
              + uses
              + "],"
              + c
              + ");");
    }
    for (int j = 1; j < n; j++) {
      int i = r.nextInt(j);
      if (r.nextInt(3) == 0) {
        constraints.add("constraint int_lin_le([1,-1],[s" + i + ",s" + j + "]," + (-d[i]) + ");");
      }
    }
    sb.append("var 0..").append(horizon).append(": obj :: output_var;\n");
    for (int i = 0; i < n; i++) {
      constraints.add("constraint int_lin_le([1,-1],[s" + i + ",obj]," + (-d[i]) + ");");
    }
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
    if (out.contains("% redundant resource ")) {
      posted++;
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

  @Test
  void redundantResourcesKeepTheOptimum() throws IOException {
    Random r = new Random(SEED);
    List<String> failures = new ArrayList<>();
    int runs = 0;
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < 5; trial++) {
        String model = fzn(r);
        Integer expected = solve(model, "--lcg", "off");
        System.setProperty("jacop.lcg.check", "true");
        System.setProperty("org.jacop.fz.cumulativeDff", "3");
        System.setProperty("org.jacop.fz.cumulativeDff.variableUses", "true");
        try {
          String[][] options = {{"--lcg", "off", "-debug"}, {"-debug"}, {"-f", "-debug"}};
          for (String[] o : options) {
            runs++;
            // root-only resources on even trials, resources at every node on odd ones
            System.setProperty("org.jacop.fz.cumulativeDff.at", trial % 2 == 0 ? "root" : "search");
            Integer got = solve(model, o);
            if (got == null || !got.equals(expected)) {
              failures.add(
                  "trial "
                      + trial
                      + " "
                      + String.join(" ", o)
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
          System.clearProperty("org.jacop.fz.cumulativeDff");
          System.clearProperty("org.jacop.fz.cumulativeDff.variableUses");
          System.clearProperty("org.jacop.fz.cumulativeDff.at");
        }
      }
    } catch (IllegalStateException e) {
      failures.add(e.getMessage());
    }
    assertTrue(failures.isEmpty(), String.join("\n", failures));
    // most models have a use between a third and a half of a capacity, which u^(2) raises
    assertTrue(2 * posted >= runs, posted + " runs with a redundant resource of " + runs);
  }
}
