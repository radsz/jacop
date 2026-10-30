/*
 * ComponentsFlatzincTest.java
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
 * Checks --components, which solves and fixes before search the independent parts of a model the
 * objective does not depend on: on random models of a few independent groups, a solution found is a
 * solution, there is one when the model has one, and the optimum stays.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class ComponentsFlatzincTest {

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimize) {
    int groups = 2 + random.nextInt(2);
    StringBuilder fzn = new StringBuilder();
    List<String> all = new ArrayList<>();
    List<List<String>> members = new ArrayList<>();
    for (int g = 0; g < groups; g++) {
      List<String> group = new ArrayList<>();
      int size = 2 + random.nextInt(3);
      for (int i = 0; i < size; i++) {
        String x = "x" + g + "_" + i;
        fzn.append("var 0..").append(1 + random.nextInt(3)).append(": ").append(x).append(";\n");
        group.add(x);
        all.add(x);
      }
      members.add(group);
    }
    fzn.append("array [1..")
        .append(all.size())
        .append("] of var int: x:: output_array([1..")
        .append(all.size())
        .append("]) = [")
        .append(String.join(",", all))
        .append("];\n");
    for (List<String> group : members) {
      int constraints = 1 + random.nextInt(3);
      for (int k = 0; k < constraints; k++) {
        String a = group.get(random.nextInt(group.size()));
        String b = group.get(random.nextInt(group.size()));
        switch (random.nextInt(3)) {
          case 0 -> {
            int[] w = group.stream().mapToInt(v -> random.nextInt(5) - 2).toArray();
            fzn.append("constraint int_lin_le(")
                .append(Arrays.toString(w).replace(" ", ""))
                .append(",[")
                .append(String.join(",", group))
                .append("],")
                .append(random.nextInt(4) - 1)
                .append(");\n");
          }
          case 1 -> {
            if (!a.equals(b)) {
              fzn.append("constraint int_ne(").append(a).append(",").append(b).append(");\n");
            }
          }
          default ->
              fzn.append("constraint int_lin_eq([1,1],[")
                  .append(a)
                  .append(",")
                  .append(b)
                  .append("],")
                  .append(random.nextInt(5))
                  .append(");\n");
        }
      }
    }
    if (optimize) {
      // the objective depends on the first group only
      List<String> group = members.getFirst();
      int[] w = new int[group.size() + 1];
      for (int i = 0; i < group.size(); i++) {
        w[i] = random.nextInt(7) - 3;
      }
      w[group.size()] = -1;
      fzn.insert(0, "var -100..100: obj:: output_var;\n");
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(w).replace(" ", ""))
          .append(",[")
          .append(String.join(",", group))
          .append(",obj],0);\n");
      fzn.append(random.nextBoolean() ? "solve minimize obj;\n" : "solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  @Test
  void aSolutionIsASolutionAndOneIsFound() throws IOException {
    Random random = new Random(11);
    int solved = 0;
    for (int trial = 0; trial < 200; trial++) {
      String model = randomModel(random, false);
      Set<String> all = solutions(run(model, "--components", "off", "-a"));
      String out = run(model, "-s");
      solved += out.contains("componentsSolved=0") ? 0 : 1;
      Set<String> found = solutions(out);
      String context = "trial " + trial + "\n" + model + "\n" + out;
      assertEquals(all.isEmpty(), found.isEmpty(), context);
      assertTrue(all.containsAll(found), context);
    }
    assertTrue(solved > 50, "solved " + solved);
  }

  @Test
  void theOptimumStays() throws IOException {
    Random random = new Random(12);
    int solved = 0;
    for (int trial = 0; trial < 200; trial++) {
      String model = randomModel(random, true);
      String out = run(model, "-s");
      solved += out.contains("componentsSolved=0") ? 0 : 1;
      assertEquals(
          optimum(run(model, "--components", "off")),
          optimum(out),
          "trial " + trial + "\n" + model + "\n" + out);
    }
    assertTrue(solved > 50, "solved " + solved);
  }

  @Test
  void aComponentWithoutSolutionMakesTheModelInfeasible() throws IOException {
    String fzn =
        """
        var 0..5: obj:: output_var;
        var 0..3: a;
        var 0..3: b;
        var 0..1: c;
        var 0..1: d;
        constraint int_lin_le([1,-1],[a,obj],0);
        constraint int_ne(a,b);
        constraint int_ne(c,d);
        constraint int_lin_eq([1,1],[c,d],2);
        solve minimize obj;
        """;
    String out = run(fzn, "-s");
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                Arrays.stream(s.strip().split("\\R"))
                    .filter(l -> !l.isBlank() && !l.startsWith("%"))
                    .collect(Collectors.joining(" ")))
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
