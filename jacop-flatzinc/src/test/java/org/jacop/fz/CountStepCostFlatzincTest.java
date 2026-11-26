/*
 * CountStepCostFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks {@link org.jacop.fz.constraints.CountStepCostBound}: the least step cost of the counts of
 * one array bounds the objective without cutting an optimum.
 */
class CountStepCostFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.countStepCost";

  @TempDir Path tmp;

  /**
   * A random model: variables with small domains, one to three arrays over some of them, counts of
   * some values in each with a step cost (a chain of int_le_reif and jacop_if_then_else_int, with
   * costs that sometimes fall), and the objective as a weighted sum of the costs and sometimes of
   * one variable.
   */
  private static String randomModel(Random random) {
    StringBuilder fzn = new StringBuilder();
    List<String> constraints = new ArrayList<>();
    int n = 4 + random.nextInt(5);
    int values = 2 + random.nextInt(3);
    List<String> xs = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      Set<Integer> d = new TreeSet<>();
      while (d.size() < 1 + random.nextInt(values)) {
        d.add(1 + random.nextInt(values + 1));
      }
      fzn.append("var ")
          .append(d.stream().map(String::valueOf).collect(Collectors.joining(",", "{", "}")))
          .append(": x")
          .append(i)
          .append(";\n");
      xs.add("x" + i);
    }
    List<String> terms = new ArrayList<>();
    List<Integer> weights = new ArrayList<>();
    int arrays = 1 + random.nextInt(3);
    int fresh = 0;
    for (int a = 0; a < arrays; a++) {
      List<String> members = new ArrayList<>();
      for (String x : xs) {
        if (a == 0 || random.nextInt(3) > 0) {
          members.add(x);
        }
      }
      String array = String.join(",", members);
      int m = members.size();
      for (int v = 1; v <= values; v++) {
        if (random.nextInt(4) == 0) {
          continue;
        }
        int id = fresh++;
        fzn.append("var 0..").append(m).append(": c").append(id).append(";\n");
        constraints.add("constraint jacop_count([" + array + "]," + v + ",c" + id + ")");
        int steps = 1 + random.nextInt(3);
        List<String> bools = new ArrayList<>();
        List<Integer> costs = new ArrayList<>();
        int limit = random.nextInt(2);
        for (int k = 0; k < steps; k++) {
          String b = "b" + id + "_" + k;
          fzn.append("var bool: ").append(b).append(";\n");
          constraints.add("constraint int_le_reif(c" + id + "," + limit + "," + b + ")");
          bools.add(b);
          costs.add(random.nextInt(4) == 0 ? random.nextInt(3) : 2 * k + random.nextInt(3));
          limit += 1 + random.nextInt(2);
        }
        bools.add("true");
        costs.add(2 * steps + random.nextInt(3));
        int top = costs.stream().mapToInt(Integer::intValue).max().orElse(0);
        fzn.append("var 0..").append(top).append(": y").append(id).append(";\n");
        constraints.add(
            "constraint jacop_if_then_else_int(["
                + String.join(",", bools)
                + "],"
                + costs.stream().map(String::valueOf).collect(Collectors.joining(",", "[", "]"))
                + ",y"
                + id
                + ")");
        terms.add("y" + id);
        weights.add(1 + random.nextInt(3));
      }
    }
    if (terms.isEmpty() || random.nextInt(4) == 0) {
      terms.add("x0");
      weights.add(random.nextInt(5) - 2);
    }
    fzn.append("var -100..1000: obj:: output_var;\n");
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(String.join(",", xs))
        .append("];\n");
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    StringBuilder w = new StringBuilder("[");
    weights.forEach(c -> w.append(c).append(","));
    w.append("-1]");
    fzn.append("constraint int_lin_eq(")
        .append(w)
        .append(",[")
        .append(String.join(",", terms))
        .append(",obj],")
        .append(random.nextInt(5) - 2)
        .append(");\n");
    fzn.append("solve minimize obj;\n");
    return fzn.toString();
  }

  @Test
  void boundKeepsOptima() throws IOException {
    Random random = new Random(41);
    int bounded = 0;
    for (int trial = 0; trial < 300; trial++) {
      String model = randomModel(random);
      String out = run(model, true, "-debug");
      bounded += out.contains("% count step cost bound") ? 1 : 0;
      String reference = optimum(run(model, false));
      assertEquals(reference, optimum(out), "trial " + trial + "\n" + model);
      assertEquals(
          reference,
          optimum(run(model, true, "--lcg", "on", "-f")),
          "trial " + trial + "\n" + model);
    }
    assertTrue(bounded > 50, "bounded " + bounded);
  }

  private String run(String model, boolean bound, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (!bound) {
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
