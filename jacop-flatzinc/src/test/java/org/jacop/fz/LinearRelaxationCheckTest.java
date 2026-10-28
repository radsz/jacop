/*
 * LinearRelaxationCheckTest.java
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
import java.util.StringJoiner;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

class LinearRelaxationCheckTest {

  private static final String PROPERTY = "org.jacop.fz.linearCheck";

  private static final String UNSAT = "=====UNSATISFIABLE=====";

  @TempDir Path tmp;

  // producers that must each deliver their demand over the periods, and a capacity per period;
  // infeasible exactly when the total demand is above periods * capacity
  private static String transport(int[] demand, int periods, int capacity) {
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < demand.length; i++) {
      for (int j = 0; j < periods; j++) {
        fzn.append("var 0..").append(capacity).append(": x_").append(i).append('_').append(j);
        fzn.append(":: output_var;\n");
      }
    }
    for (int i = 0; i < demand.length; i++) {
      StringJoiner a = new StringJoiner(",", "[", "]");
      StringJoiner x = new StringJoiner(",", "[", "]");
      for (int j = 0; j < periods; j++) {
        a.add("1");
        x.add("x_" + i + "_" + j);
      }
      fzn.append("constraint int_lin_eq(").append(a).append(',').append(x);
      fzn.append(',').append(demand[i]).append(");\n");
    }
    for (int j = 0; j < periods; j++) {
      StringJoiner a = new StringJoiner(",", "[", "]");
      StringJoiner x = new StringJoiner(",", "[", "]");
      for (int i = 0; i < demand.length; i++) {
        a.add("1");
        x.add("x_" + i + "_" + j);
      }
      fzn.append("constraint int_lin_le(").append(a).append(',').append(x);
      fzn.append(',').append(capacity).append(");\n");
    }
    return fzn.append("solve satisfy;\n").toString();
  }

  @Test
  void demandAboveTheTotalCapacityIsInfeasibleAtTheRoot() throws IOException {
    // 61 units over 6 periods of 10: every row alone holds, only their sum does not; search
    // without the check runs for minutes on these 24 variables
    String out = run(transport(new int[] {16, 15, 15, 15}, 6, 10), true, "-t", "10000");
    assertTrue(out.contains(UNSAT), out);
  }

  @Test
  void demandAtTheTotalCapacityIsFeasible() throws IOException {
    String out = run(transport(new int[] {15, 15, 15, 15}, 6, 10), true, "-t", "10000");
    assertTrue(out.contains("----------"), out);
  }

  @Test
  void randomModelsKeepTheirAnswer() throws IOException {
    Random random = new Random(20261028);
    int infeasible = 0;
    int proved = 0;
    for (int t = 0; t < 300; t++) {
      String fzn;
      if (t % 2 == 0) {
        fzn = randomModel(random);
      } else {
        int periods = 2 + random.nextInt(3);
        int capacity = 2 + random.nextInt(3);
        int[] demand = new int[2 + random.nextInt(2)];
        for (int i = 0; i < demand.length; i++) {
          demand[i] = random.nextInt(periods * capacity / demand.length + 3);
        }
        fzn = transport(demand, periods, capacity);
      }
      String off = run(fzn, false);
      String on = run(fzn, true, "-debug");
      boolean unsat = off.contains(UNSAT);
      assertEquals(unsat, on.contains(UNSAT), fzn + "\n" + off + "\n" + on);
      infeasible += unsat ? 1 : 0;
      proved += on.contains("% the linear relaxation of") ? 1 : 0;
    }
    assertTrue(
        infeasible > 20 && proved > 5, infeasible + " infeasible, " + proved + " by the check");
  }

  // small rows of all kinds the check reads, some over 0/1 variables and fixed variables, next to
  // reified rows that it must leave out
  private static String randomModel(Random random) {
    int n = 3 + random.nextInt(4);
    StringBuilder fzn = new StringBuilder();
    for (int j = 0; j < n; j++) {
      int lo = random.nextInt(3) - 1;
      int hi = lo + random.nextInt(5);
      fzn.append("var ").append(lo).append("..").append(hi).append(": x").append(j);
      fzn.append(":: output_var;\n");
    }
    fzn.append("var bool: b:: output_var;\n");
    fzn.append("var 3..3: f;\n");
    int rows = 2 + random.nextInt(4);
    for (int r = 0; r < rows; r++) {
      int kind = random.nextInt(5);
      if (kind == 3) {
        fzn.append("constraint int_le(x").append(random.nextInt(n)).append(", x");
        fzn.append(random.nextInt(n)).append(");\n");
        continue;
      }
      StringJoiner a = new StringJoiner(",", "[", "]");
      StringJoiner x = new StringJoiner(",", "[", "]");
      int sum = 0;
      for (int j = 0; j < n; j++) {
        int w = random.nextInt(7) - 3;
        if (w != 0) {
          a.add(Integer.toString(w));
          x.add("x" + j);
          sum += w;
        }
      }
      a.add("2");
      x.add("f");
      int c = random.nextInt(9) - 4 + sum + 6;
      if (kind == 4) {
        fzn.append("constraint int_lin_le_reif(").append(a).append(',').append(x);
        fzn.append(',').append(c).append(", b);\n");
      } else {
        fzn.append("constraint ").append(kind == 0 ? "int_lin_eq(" : "int_lin_le(").append(a);
        fzn.append(',').append(x).append(',').append(c).append(");\n");
      }
    }
    return fzn.append("solve satisfy;\n").toString();
  }

  private String run(String model, boolean check, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (!check) {
      System.setProperty(PROPERTY, "false");
    }
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
