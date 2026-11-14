/*
 * SetUnionFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Unions of singleton sets become membership clauses ({@code SetUnionDetector}): the model must
 * keep every solution and every optimum, with and without LCG.
 */
class SetUnionFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.setUnion";

  static {
    // the random chains are short; the detector's default skips chains of fewer than 8 singletons
    System.setProperty("org.jacop.fz.setUnion.min", "2");
  }

  @TempDir Path tmp;

  /**
   * A random set comprehension as MiniZinc flattens it: elements e_i with small domains (or
   * constants, or 0/1 variables), the singletons {e_i}, constant sets, a chain of set_union
   * constraints and constraints on the union: its cardinality, a membership, or a subset. An inner
   * union is sometimes printed, which keeps its chain.
   */
  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> constraints = new ArrayList<>();
    List<String> ints = new ArrayList<>();
    List<String> sets = new ArrayList<>();
    int unionsCount = 1 + random.nextInt(2);
    int s = 0;
    int e = 0;
    for (int u = 0; u < unionsCount; u++) {
      int leaves = 2 + random.nextInt(4);
      List<String> operands = new ArrayList<>();
      for (int k = 0; k < leaves; k++) {
        int kind = random.nextInt(10);
        if (kind == 0) {
          operands.add("{" + random.nextInt(5) + "}");
          continue;
        }
        String set = "s" + s++;
        String elem;
        if (kind == 1) {
          elem = String.valueOf(random.nextInt(5));
        } else {
          elem = "e" + e++;
          int lo = random.nextInt(3);
          int hi = kind == 2 ? lo + 1 : lo + random.nextInt(4);
          fzn.append("var ").append(lo).append("..").append(hi).append(": ").append(elem);
          fzn.append(";\n");
          ints.add(elem);
        }
        int lub = 3 + random.nextInt(3);
        fzn.append("var set of 0..").append(lub).append(": ").append(set).append(";\n");
        constraints.add("constraint set_card(" + set + ",1)");
        constraints.add("constraint set_in(" + elem + "," + set + ")");
        operands.add(set);
      }
      String acc = operands.get(0);
      String printed = null;
      for (int k = 1; k < operands.size(); k++) {
        String next = "t" + s++;
        int lub = 3 + random.nextInt(4);
        boolean print = random.nextInt(12) == 0;
        fzn.append("var set of 0..")
            .append(lub)
            .append(": ")
            .append(next)
            .append(print && k < operands.size() - 1 ? ":: output_var" : "")
            .append(";\n");
        if (print && k < operands.size() - 1) {
          printed = next;
        }
        constraints.add("constraint set_union(" + acc + "," + operands.get(k) + "," + next + ")");
        acc = next;
      }
      if (printed != null) {
        sets.add(printed);
      }
      String union = "u" + u;
      fzn.append("var set of 0..6: ").append(union).append(":: output_var;\n");
      constraints.add("constraint set_eq(" + acc + "," + union + ")");
      sets.add(union);
      String card = "c" + u;
      fzn.append("var 0..7: ").append(card).append(":: output_var;\n");
      constraints.add("constraint set_card(" + union + "," + card + ")");
      ints.add(card);
      switch (random.nextInt(3)) {
        case 0 -> constraints.add("constraint set_in(" + random.nextInt(4) + "," + union + ")");
        case 1 -> constraints.add("constraint set_subset(" + union + ",{0,1,2,3,4})");
        default -> {
          // only the cardinality
        }
      }
    }
    for (String v : ints) {
      if (v.startsWith("e")) {
        fzn.insert(fzn.indexOf(": " + v + ";") + v.length() + 2, ":: output_var");
      }
    }
    if (optimise) {
      fzn.append("var 0..100: obj:: output_var;\n");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      StringBuilder w = new StringBuilder("[");
      StringBuilder v = new StringBuilder("[");
      for (String x : ints) {
        w.append(random.nextInt(5) - 2).append(',');
        v.append(x).append(',');
      }
      w.append("-1]");
      v.append("obj]");
      fzn.append("constraint int_lin_eq(").append(w).append(',').append(v).append(",-50);\n");
      fzn.append("solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  @Test
  void unionsKeepAllSolutions() throws IOException {
    Random random = new Random(21);
    int rewritten = 0;
    for (int trial = 0; trial < 120; trial++) {
      String model = randomModel(random, false);
      String out = run(model, true, "-a", "-debug");
      rewritten += out.contains("set union detector") ? 1 : 0;
      assertEquals(
          solutions(run(model, false, "-a")), solutions(out), "trial " + trial + "\n" + model);
    }
    assertTrue(rewritten > 60, "rewritten " + rewritten);
  }

  @Test
  void unionsKeepOptimaUnderLcg() throws IOException {
    Random random = new Random(22);
    int rewritten = 0;
    for (int trial = 0; trial < 80; trial++) {
      String model = randomModel(random, true);
      String out = run(model, true, "--lcg", "on", "-debug");
      rewritten += out.contains("set union detector") ? 1 : 0;
      String expected = optimum(run(model, false, "--lcg", "off"));
      assertEquals(expected, optimum(out), "trial " + trial + "\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on", "-f")),
          "trial " + trial + " -f\n" + model);
    }
    assertTrue(rewritten > 40, "rewritten " + rewritten);
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
