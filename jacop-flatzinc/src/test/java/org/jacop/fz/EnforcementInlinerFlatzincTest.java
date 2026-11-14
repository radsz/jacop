/*
 * EnforcementInlinerFlatzincTest.java
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
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random models of disjunctions and literal clauses written with half-reified constraints, as
 * MiniZinc writes them: eliminating their controls must keep satisfiability and optima, and the
 * solutions it prints must satisfy the whole model.
 */
class EnforcementInlinerFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.enforcementInlining";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int n = 3 + random.nextInt(3);
    int m = 1 + random.nextInt(3);
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..").append(3 + random.nextInt(3)).append(": x").append(i).append(";\n");
    }
    for (int i = 0; i < m; i++) {
      // 0/1 variables for the literal bodies
      fzn.append("var 0..1: y").append(i).append(";\n");
    }
    List<String> constraints = new ArrayList<>();
    int controls = 0;
    int groups = 2 + random.nextInt(5);
    for (int g = 0; g < groups; g++) {
      int kind = random.nextInt(6);
      if (kind <= 2) {
        // a disjunction b1 \/ b2 of two half-reified constraints, or of three
        int k = kind == 2 ? 3 : 2;
        List<String> bs = new ArrayList<>();
        for (int j = 0; j < k; j++) {
          String b = "b" + controls++;
          bs.add(b);
          constraints.add(body(random, n, m, b));
        }
        constraints.add("constraint bool_clause([" + String.join(",", bs) + "],[])");
      } else if (kind == 3) {
        // a -> C written as b -> C, b \/ not a
        String b = "b" + controls++;
        constraints.add(body(random, n, m, b));
        constraints.add("constraint bool_clause([" + b + "],[y" + random.nextInt(m) + "])");
      } else if (kind == 4) {
        // the literal of b used in two clauses
        String b = "b" + controls++;
        constraints.add(body(random, n, m, b));
        String c = "b" + controls++;
        constraints.add(body(random, n, m, c));
        constraints.add("constraint bool_clause([" + b + "," + c + "],[])");
        constraints.add("constraint bool_clause([" + b + ",y" + random.nextInt(m) + "],[])");
      } else {
        // a control used elsewhere too, which must stay
        String b = "b" + controls++;
        constraints.add(body(random, n, m, b));
        String c = "b" + controls++;
        constraints.add(body(random, n, m, c));
        constraints.add("constraint bool_clause([" + b + "," + c + "],[])");
        constraints.add("constraint bool2int(" + b + ",i" + g + ")");
        fzn.append("var 0..1: i").append(g).append(";\n");
        constraints.add("constraint int_le(i" + g + ",x" + random.nextInt(n) + ")");
      }
    }
    for (int b = 0; b < controls; b++) {
      fzn.append("var bool: b").append(b).append(";\n");
    }
    fzn.append("array [1..")
        .append(n + m)
        .append("] of var int: v:: output_array([1..")
        .append(n + m)
        .append("]) = [")
        .append(
            IntStream.range(0, n + m)
                .mapToObj(i -> i < n ? "x" + i : "y" + (i - n))
                .collect(Collectors.joining(",")))
        .append("];\n");
    if (optimise) {
      fzn.append("var 0..1000: obj:: output_var;\n");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      int[] a =
          IntStream.range(0, n + m + 1).map(i -> i == n + m ? -1 : random.nextInt(5)).toArray();
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(a).replace(" ", ""))
          .append(",")
          .append(
              IntStream.rangeClosed(0, n + m)
                  .mapToObj(i -> i < n ? "x" + i : i < n + m ? "y" + (i - n) : "obj")
                  .collect(Collectors.joining(",", "[", "]")))
          .append(",0);\n");
      fzn.append(random.nextBoolean() ? "solve maximize obj;\n" : "solve minimize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  // a half-reified constraint with control b
  private static String body(Random random, int n, int m, String b) {
    String x = "x" + random.nextInt(n);
    String z = "x" + random.nextInt(n);
    String y = "y" + random.nextInt(m);
    int c = random.nextInt(4);
    return switch (random.nextInt(9)) {
      case 0 -> "constraint int_lin_le_imp([1,-1],[" + x + "," + z + "]," + (c - 2) + "," + b + ")";
      case 1 -> "constraint int_le_imp(" + x + "," + z + "," + b + ")";
      case 2 -> "constraint int_ne_imp(" + x + "," + c + "," + b + ")";
      case 3 -> "constraint int_eq_imp(" + x + "," + c + "," + b + ")";
      case 4 -> "constraint int_eq_imp(" + x + "," + z + "," + b + ")";
      case 5 -> "constraint int_lin_ne_imp([1,1],[" + x + "," + z + "]," + (c + 2) + "," + b + ")";
      case 6 -> "constraint int_ne_imp(" + y + ",1," + b + ")";
      case 7 -> "constraint int_eq_imp(" + y + "," + (c & 1) + "," + b + ")";
      default -> "constraint int_lin_le_imp([2,1],[" + x + "," + z + "]," + (c + 3) + "," + b + ")";
    };
  }

  @Test
  void inliningKeepsSatisfiabilityAndGivesSolutions() throws IOException {
    Random random = new Random(41);
    int inlined = 0;
    int trials = Integer.getInteger("enforcementInlining.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String out = run(model, true, "-debug");
      inlined += out.contains("enforcement inlining") ? 1 : 0;
      boolean sat = !out.contains("UNSATISFIABLE");
      assertEquals(
          !run(model, false).contains("UNSATISFIABLE"), sat, "trial " + trial + "\n" + model);
      if (sat) {
        assertSolution(model, out, "trial " + trial);
      }
    }
    assertTrue(inlined > trials / 2, "inlined " + inlined);
  }

  @Test
  void inliningKeepsOptima() throws IOException {
    Random random = new Random(42);
    int trials = Integer.getInteger("enforcementInlining.trials", 300) * 2 / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"));
      for (String[] options :
          List.of(
              new String[] {"--lcg", "off"}, new String[] {"--lcg", "on"}, new String[] {"-f"})) {
        String out = run(model, true, options);
        assertEquals(
            expected,
            optimum(out),
            "trial " + trial + " " + Arrays.toString(options) + "\n" + model);
        if (!"UNSATISFIABLE".equals(expected)) {
          assertSolution(model, out, "trial " + trial + " " + Arrays.toString(options));
        }
      }
    }
  }

  @Test
  void disjunctionLosesItsControl() throws IOException {
    String model =
        """
        var 0..9: s1:: output_var;
        var 0..9: s2:: output_var;
        var bool: b1;
        var bool: b2;
        constraint int_lin_le_imp([1,-1],[s1,s2],-3,b1);
        constraint int_lin_le_imp([1,-1],[s2,s1],-4,b2);
        constraint bool_clause([b1,b2],[]);
        constraint int_le(2,s1);
        constraint int_le(s1,6);
        constraint int_le(s2,4);
        solve minimize s1;
        """;
    String out = run(model, true, "-debug");
    assertTrue(out.contains("enforcement inlining: 1 controls eliminated"), out);
    assertTrue(out.contains("XplusClteqZImpliedNot"), out);
    assertEquals(optimum(run(model, false)), optimum(out));
  }

  // the last printed solution, fixed in the model, must satisfy it without inlining
  private void assertSolution(String model, String out, String message) throws IOException {
    String[] parts = out.split("----------");
    assertTrue(parts.length >= 2, message + "\n" + out);
    Matcher m =
        Pattern.compile("v = array1d\\(1\\.\\.\\d+, \\[([^\\]]*)\\]\\);")
            .matcher(parts[parts.length - 2]);
    assertTrue(m.find(), message + "\n" + out);
    String[] values = m.group(1).split(", ");
    Matcher decl =
        Pattern.compile("output_array\\(\\[1\\.\\.\\d+\\]\\) = \\[([^\\]]*)\\]").matcher(model);
    assertTrue(decl.find());
    String[] vars = decl.group(1).split(",");
    StringBuilder fixed = new StringBuilder();
    for (int i = 0; i < vars.length; i++) {
      fixed
          .append("constraint int_eq(")
          .append(vars[i])
          .append(",")
          .append(values[i])
          .append(");\n");
    }
    String check = model.replaceFirst("solve ", fixed.toString().replace("$", "\\$") + "solve ");
    String result = run(check, false, "--lcg", "off");
    assertTrue(
        result.contains("----------") && !result.contains("UNSATISFIABLE"),
        message + ": not a solution\n" + out + "\n" + model);
  }

  private String run(String model, boolean inlining, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, String.valueOf(inlining));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  // the value of obj in the last solution, or the status when there is none
  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      } else if (line.startsWith("s1 = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out);
    return last;
  }
}
