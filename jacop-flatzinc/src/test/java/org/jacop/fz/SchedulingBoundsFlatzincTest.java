/*
 * SchedulingBoundsFlatzincTest.java
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
import java.util.Arrays;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the FlatZinc detection of weighted completion times on cumulatives of capacity above 1
 * (WeightedCompletion with the Eastman, Even and Isaacs bound) and of counts of late tasks on unary
 * resources (LateCount): on random models the optima must match those without the detection, with
 * the default options (lazy clause generation) and with free search.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class SchedulingBoundsFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.weightedCompletion";

  @TempDir Path tmp;

  private static String starts(int n, int horizon, Random random, StringBuilder fzn) {
    for (int i = 0; i < n; i++) {
      fzn.append("var ")
          .append(random.nextInt(4))
          .append("..")
          .append(horizon)
          .append(": s")
          .append(i)
          .append(";\n");
      fzn.append("var 0..").append(horizon + 4).append(": e").append(i).append(";\n");
    }
    String ss = IntStream.range(0, n).mapToObj(i -> "s" + i).collect(Collectors.joining(","));
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: s:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(ss)
        .append("];\n");
    return ss;
  }

  private static void ends(int[] d, StringBuilder fzn) {
    for (int i = 0; i < d.length; i++) {
      fzn.append("constraint int_lin_eq([1,-1],[s")
          .append(i)
          .append(",e")
          .append(i)
          .append("],")
          .append(-d[i])
          .append(");\n");
    }
  }

  /** P|r_j|sum w_j C_j: a cumulative of capacity 2 or 3 and a weighted sum of ends. */
  private static String parallelModel(Random random) {
    int n = 3 + random.nextInt(4);
    int capacity = 2 + random.nextInt(2);
    int horizon = 6 + random.nextInt(4);
    StringBuilder fzn = new StringBuilder();
    int[] d = new int[n];
    int[] r = new int[n];
    for (int i = 0; i < n; i++) {
      d[i] = 1 + random.nextInt(3);
      r[i] = 1 + random.nextInt(capacity);
    }
    starts(n, horizon, random, fzn);
    fzn.append("var 0..400: y0:: output_var;\n");
    fzn.append("constraint jacop_cumulative(s,")
        .append(Arrays.toString(d).replace(" ", ""))
        .append(',')
        .append(Arrays.toString(r).replace(" ", ""))
        .append(',')
        .append(capacity)
        .append(");\n");
    ends(d, fzn);
    StringBuilder coefficients = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (int i = 0; i < n; i++) {
      coefficients.append(random.nextInt(4)).append(',');
      vars.append(random.nextBoolean() ? "e" : "s").append(i).append(',');
    }
    fzn.append("constraint int_lin_eq([")
        .append(coefficients)
        .append("-1],[")
        .append(vars)
        .append("y0],")
        .append(random.nextInt(5) - 2)
        .append(");\n");
    fzn.append("solve minimize y0;\n");
    return fzn.toString();
  }

  /** 1|r_j|sum U_j: a unary cumulative and the count of ends past their due dates. */
  private static String lateModel(Random random) {
    int n = 3 + random.nextInt(4);
    int horizon = 8 + random.nextInt(4);
    StringBuilder fzn = new StringBuilder();
    int[] d = new int[n];
    for (int i = 0; i < n; i++) {
      d[i] = random.nextInt(4);
    }
    starts(n, horizon, random, fzn);
    fzn.append("var 0..").append(n + 3).append(": y0:: output_var;\n");
    for (int i = 0; i < n; i++) {
      fzn.append("var bool: b").append(i).append(";\n");
      fzn.append("var 0..1: u").append(i).append(";\n");
    }
    fzn.append("constraint jacop_cumulative(s,")
        .append(Arrays.toString(d).replace(" ", ""))
        .append(',')
        .append(Arrays.toString(IntStream.generate(() -> 1).limit(n).toArray()).replace(" ", ""))
        .append(",1);\n");
    ends(d, fzn);
    StringBuilder coefficients = new StringBuilder();
    StringBuilder vars = new StringBuilder();
    for (int i = 0; i < n; i++) {
      // late when s + d > due, as c <= s or c <= e, through int_le_reif or int_lt_reif
      int due = random.nextInt(horizon);
      boolean end = random.nextBoolean();
      boolean lt = random.nextBoolean();
      int c = (end ? due + 1 : due - d[i] + 1) - (lt ? 1 : 0);
      fzn.append("constraint int_")
          .append(lt ? "lt" : "le")
          .append("_reif(")
          .append(c)
          .append(',')
          .append(end ? "e" : "s")
          .append(i)
          .append(",b")
          .append(i)
          .append(");\n");
      fzn.append("constraint bool2int(b").append(i).append(",u").append(i).append(");\n");
      coefficients.append(1 + (random.nextInt(4) == 0 ? 1 : 0)).append(',');
      vars.append('u').append(i).append(',');
    }
    int k = random.nextInt(3);
    fzn.append("constraint int_lin_")
        .append(random.nextInt(4) == 0 ? "le" : "eq")
        .append("([")
        .append(coefficients)
        .append("-1],[")
        .append(vars)
        .append("y0],")
        .append(-k)
        .append(");\n");
    fzn.append("solve minimize y0;\n");
    return fzn.toString();
  }

  @Test
  void parallelDetectionKeepsOptima() throws IOException {
    Random random = new Random(21);
    int detected = 0;
    for (int trial = 0; trial < 150; trial++) {
      String model = parallelModel(random);
      String[] options = trial % 3 == 0 ? new String[] {"-debug", "-f"} : new String[] {"-debug"};
      String out = run(model, true, options);
      detected += out.contains("% redundant WeightedCompletion") ? 1 : 0;
      assertEquals(
          optimum(run(model, false, options)), optimum(out), "trial " + trial + "\n" + model);
    }
    assertTrue(detected > 75, "detected " + detected);
  }

  @Test
  void lateCountDetectionKeepsOptima() throws IOException {
    Random random = new Random(22);
    int detected = 0;
    for (int trial = 0; trial < 150; trial++) {
      String model = lateModel(random);
      String[] options = trial % 3 == 0 ? new String[] {"-debug", "-f"} : new String[] {"-debug"};
      String out = run(model, true, options);
      detected += out.contains("% redundant LateCount") ? 1 : 0;
      assertEquals(
          optimum(run(model, false, options)), optimum(out), "trial " + trial + "\n" + model);
    }
    assertTrue(detected > 75, "detected " + detected);
  }

  @Test
  void lateCountOfMiniZincModel() throws IOException {
    // flattened from sum(i)(bool2int(s[i] + p[i] > d[i])) with disjunctive(s, p)
    String fzn =
        """
        array [1..4] of int: p = [3,2,4,1];
        var 0..20: s1;
        var 1..20: s2;
        var 0..20: s3;
        var 2..20: s4;
        var 0..4: y0:: output_var;
        var bool: b1;
        var 0..1: u1;
        var bool: b2;
        var 0..1: u2;
        var bool: b3;
        var 0..1: u3;
        array [1..4] of var int: s = [s1,s2,s3,s4];
        constraint jacop_cumulative(s,p,[1,1,1,1],1);
        constraint int_lin_eq([1,1,1,-1],[u1,u2,u3,y0],-1);
        constraint int_le_reif(1,s1,b1);
        constraint bool2int(b1,u1);
        constraint int_le_reif(3,s2,b2);
        constraint bool2int(b2,u2);
        constraint int_le_reif(3,s3,b3);
        constraint bool2int(b3,u3);
        solve minimize y0;
        """;
    String on = run(fzn, true, "-debug");
    assertTrue(on.contains("LateCount([s1"), on);
    assertTrue(on.contains("[3, 4, 6, 2147483647]"), on);
    assertFalse(run(fzn, false, "-debug").contains("LateCount"));
    // s1, s2 and s3 must all start by 2 to be on time, so only one is; s4 is always late
    assertEquals("3", optimum(on));
    assertEquals("3", optimum(run(fzn, false)));
  }

  private String run(String model, boolean detection, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (!detection) {
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

  // the value of y0 or cost in the last solution, or the status when there is none
  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("y0 = ") || line.startsWith("cost = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out);
    return last;
  }
}
