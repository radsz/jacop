/*
 * IntensionTableFlatzincTest.java
 * <p>
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
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Small expressions that MiniZinc flattens into several constraints linked by introduced variables
 * are replaced by the table of their solutions over the model's variables ({@code
 * IntensionTableDetector}): every solution of the output variables and every optimum must stay,
 * with and without LCG.
 */
class IntensionTableFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.intensionTable";

  @TempDir Path tmp;

  /** A random model: a few output variables with holes and flattened expressions over them. */
  private static final class Builder {
    private final Random random;
    private final StringBuilder decls = new StringBuilder();
    private final List<String> constraints = new ArrayList<>();
    private int next;

    Builder(Random random) {
      this.random = random;
    }

    private String intVar(int lo, int hi) {
      String v = "t" + next++;
      decls.append("var ").append(lo).append("..").append(hi).append(": ").append(v);
      decls.append(":: var_is_introduced :: is_defined_var;\n");
      return v;
    }

    private String boolVar() {
      String v = "b" + next++;
      decls.append("var bool: ").append(v).append(":: var_is_introduced :: is_defined_var;\n");
      return v;
    }

    // an integer expression over the scope, as an introduced variable or an outer one
    String expression(List<String> scope, int depth) {
      String x = scope.get(random.nextInt(scope.size()));
      if (depth == 0 || random.nextInt(4) == 0) {
        return x;
      }
      String a = expression(scope, depth - 1);
      String b = expression(scope, depth - 1);
      int kind = random.nextInt(9);
      String t;
      switch (kind) {
        case 0 -> {
          t = intVar(-10, 20);
          constraints.add("int_lin_eq([1,1,-1],[" + a + "," + b + "," + t + "],0)");
        }
        case 1 -> {
          t = intVar(-10, 30);
          constraints.add("int_times(" + a + "," + b + "," + t + ")");
        }
        case 2 -> {
          t = intVar(-10, 10);
          constraints.add("int_mod(" + a + "," + (1 + random.nextInt(4)) + "," + t + ")");
        }
        case 3 -> {
          t = intVar(-10, 10);
          constraints.add("int_div(" + a + "," + (1 + random.nextInt(3)) + "," + t + ")");
        }
        case 4 -> {
          t = intVar(-10, 10);
          constraints.add("int_min(" + a + "," + b + "," + t + ")");
        }
        case 5 -> {
          t = intVar(-10, 10);
          constraints.add("int_max(" + a + "," + b + "," + t + ")");
        }
        case 6 -> {
          t = intVar(0, 10);
          String d = intVar(-10, 10);
          constraints.add("int_lin_eq([1,-1,-1],[" + a + "," + b + "," + d + "],0)");
          constraints.add("int_abs(" + d + "," + t + ")");
        }
        case 7 -> {
          t = intVar(-5, 10);
          constraints.add("array_int_element(" + a + ",[3,1,4,1,5,9,2,6]," + t + ")");
        }
        default -> {
          t = intVar(-10, 10);
          constraints.add("int_mod(" + a + "," + b + "," + t + ")");
        }
      }
      return t;
    }

    // a Boolean over the scope: a reified or half-reified comparison of two expressions
    String condition(List<String> scope) {
      String a = expression(scope, 1);
      String b = random.nextBoolean() ? expression(scope, 1) : String.valueOf(random.nextInt(4));
      String r = boolVar();
      String rel = List.of("eq", "ne", "le", "lt").get(random.nextInt(4));
      String form = random.nextInt(3) == 0 ? "_imp" : "_reif";
      if (random.nextInt(4) == 0) {
        constraints.add("set_in" + form + "(" + a + ",{0,2,3}," + r + ")");
      } else if (random.nextInt(4) == 0) {
        constraints.add(
            "int_lin_"
                + (rel.equals("lt") ? "le" : rel)
                + form
                + "([1,2],["
                + a
                + ","
                + b
                + "],3,"
                + r
                + ")");
      } else {
        constraints.add("int_" + rel + form + "(" + a + "," + b + "," + r + ")");
      }
      return r;
    }

    // a constraint over a few outer variables, written the way MiniZinc flattens it
    void constraint(List<String> scope) {
      int kind = random.nextInt(5);
      switch (kind) {
        case 0 -> {
          String p = condition(scope);
          String q = condition(scope);
          constraints.add("bool_clause([" + p + "," + q + "],[])");
        }
        case 1 -> {
          String p = condition(scope);
          String q = condition(scope);
          constraints.add("bool_clause([" + p + "],[" + q + "])");
        }
        case 2 -> {
          String p = condition(scope);
          String q = condition(scope);
          String r = boolVar();
          constraints.add("array_bool_and([" + p + "," + q + "]," + r + ")");
          String i = intVar(0, 1);
          constraints.add("bool2int(" + r + "," + i + ")");
          constraints.add("int_le(" + i + "," + expression(scope, 1) + ")");
        }
        case 3 -> {
          String e = expression(scope, 2);
          constraints.add("int_ne(" + e + "," + random.nextInt(5) + ")");
        }
        default -> {
          String p = condition(scope);
          String q = condition(scope);
          String r = condition(scope);
          constraints.add("array_bool_or([" + p + "," + q + "," + r + "],true)");
        }
      }
    }
  }

  private static String randomModel(Random random, boolean optimise) {
    Builder b = new Builder(random);
    StringBuilder fzn = new StringBuilder();
    int nv = 3 + random.nextInt(3);
    List<String> names = new ArrayList<>();
    for (int i = 0; i < nv; i++) {
      String x = "x" + i;
      names.add(x);
      int hole = 1 + random.nextInt(3);
      fzn.append("var {")
          .append(
              IntStream.rangeClosed(0, 4)
                  .filter(v -> v != hole)
                  .mapToObj(String::valueOf)
                  .collect(Collectors.joining(",")))
          .append("}: ")
          .append(x)
          .append(";\n");
    }
    int count = 2 + random.nextInt(3);
    for (int c = 0; c < count; c++) {
      List<String> scope = new ArrayList<>(names);
      java.util.Collections.shuffle(scope, random);
      // a scope of four variables is too wide for a table: the constraints stay
      b.constraint(scope.subList(0, 1 + random.nextInt(Math.min(4, nv))));
    }
    fzn.append(b.decls);
    fzn.append("array [1..")
        .append(nv)
        .append("] of var int: x:: output_array([1..")
        .append(nv)
        .append("]) = ")
        .append(names.stream().collect(Collectors.joining(",", "[", "]")))
        .append(";\n");
    if (optimise) {
      fzn.append("var 0..1000: obj:: output_var;\n");
    }
    b.constraints.forEach(c -> fzn.append("constraint ").append(c).append(";\n"));
    if (optimise) {
      int[] w = IntStream.range(0, nv).map(i -> 1 + random.nextInt(5)).toArray();
      int[] a = Arrays.copyOf(w, nv + 1);
      a[nv] = -1;
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(a).replace(" ", ""))
          .append(",")
          .append(
              IntStream.rangeClosed(0, nv)
                  .mapToObj(i -> i < nv ? "x" + i : "obj")
                  .collect(Collectors.joining(",", "[", "]")))
          .append(",0);\n");
      fzn.append("solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  @Test
  void tabledExpressionsKeepAllSolutions() throws IOException {
    Random random = new Random(31);
    int tabled = 0;
    int trials = Integer.getInteger("intensionTable.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String out = run(model, "force", "-a", "-debug");
      tabled += out.matches("(?s).*intension table detector: [1-9].*") ? 1 : 0;
      assertEquals(
          solutions(run(model, "false", "-a")), solutions(out), "trial " + trial + "\n" + model);
    }
    assertTrue(tabled > trials / 3, "tabled " + tabled);
  }

  @Test
  void tabledExpressionsKeepOptimaUnderLcg() throws IOException {
    Random random = new Random(32);
    int trials = Integer.getInteger("intensionTable.trials", 300) * 2 / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, "false", "--lcg", "off"));
      assertEquals(
          expected, optimum(run(model, null, "--lcg", "on")), "trial " + trial + "\n" + model);
      assertEquals(
          expected,
          optimum(run(model, null, "--lcg", "on", "-f")),
          "trial " + trial + " -f\n" + model);
      assertEquals(
          expected,
          optimum(run(model, null, "--lcg", "off", "-f")),
          "trial " + trial + " cp\n" + model);
    }
  }

  @Test
  void flattenedDivisorRelationBecomesATable() throws IOException {
    // x mod y = 0 \/ y mod x = 0, as MiniZinc flattens it
    String model =
        """
        var 1..6: x:: output_var;
        var 1..6: y:: output_var;
        var 0..5: m1:: var_is_introduced :: is_defined_var;
        var 0..5: m2:: var_is_introduced :: is_defined_var;
        var bool: b1:: var_is_introduced :: is_defined_var;
        var bool: b2:: var_is_introduced :: is_defined_var;
        constraint int_ne(x,y);
        constraint int_mod(x,y,m1):: defines_var(m1);
        constraint int_mod(y,x,m2):: defines_var(m2);
        constraint int_eq_imp(m1,0,b1);
        constraint int_eq_imp(m2,0,b2);
        constraint bool_clause([b1,b2],[]);
        solve satisfy;
        """;
    String out = run(model, null, "-debug");
    assertTrue(out.contains("intension table detector: 1 tables of 5 constraints"), out);
    // 1 divides all, 2 divides 4 and 6, 3 divides 6: 2 * (5 + 2 + 1) ordered pairs
    assertEquals(16, solutions(run(model, "force", "-a")).size());
    assertEquals(16, solutions(run(model, "false", "-a")).size());
  }

  private String run(String model, String property, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (property != null) {
      System.setProperty(PROPERTY, property);
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

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    Arrays.stream(s.strip().split("\\R"))
                        .filter(l -> !l.isBlank() && !l.startsWith("%"))
                        .toList()))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }

  // the value of obj in the last solution, or the status when there is none
  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out);
    return last;
  }
}
