/*
 * RegularFlowFlatzincTest.java
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
 * The aggregated flows of {@link org.jacop.fz.constraints.RegularFlowDetector} keep the solutions
 * of random models with a regular constraint whose residue classes are counted.
 */
class RegularFlowFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.regularFlow";

  @TempDir Path tmp;

  /**
   * A random model in the shape of rotating workforce scheduling: a regular constraint over p * k
   * variables, sometimes followed by a copy of the first p (the extra week) or by one more
   * variable, a few fixed positions, and a count of the values over the variables of each class i
   * mod p, sometimes leaving a value or a variable out.
   */
  private static String randomModel(Random random) {
    int p = 2 + random.nextInt(2);
    int k = 3 + random.nextInt(2);
    int symbols = 2 + random.nextInt(2);
    int states = 3 + random.nextInt(3);
    int[] d = new int[states * symbols];
    for (int i = 0; i < d.length; i++) {
      d[i] = random.nextInt(8) == 0 ? 0 : 1 + random.nextInt(states);
    }
    // a walk of the automaton from state 1, whose values the counts are drawn around
    int[] witness = new int[p * k];
    int q = 1;
    for (int i = 0; i < witness.length; i++) {
      int s = 1 + random.nextInt(symbols);
      for (int t = 0; t < symbols && q > 0 && d[(q - 1) * symbols + s - 1] == 0; t++) {
        s = s % symbols + 1;
      }
      witness[i] = s;
      q = q > 0 ? d[(q - 1) * symbols + s - 1] : 0;
    }
    StringBuilder fzn = new StringBuilder();
    List<String> seq = new ArrayList<>();
    List<List<Integer>> classes = new ArrayList<>();
    for (int c = 0; c < p; c++) {
      classes.add(new ArrayList<>());
    }
    for (int i = 0; i < p * k; i++) {
      String v;
      if (random.nextInt(12) == 0) {
        v = String.valueOf(witness[i]);
      } else {
        v = "x" + i;
        fzn.append("var 1..").append(symbols).append(": ").append(v).append(";\n");
      }
      seq.add(v);
      classes.get(i % p).add(i);
    }
    int tail = random.nextInt(3);
    if (tail == 1) {
      for (int c = 0; c < p; c++) {
        seq.add(seq.get(c));
      }
    } else if (tail == 2) {
      fzn.append("var 1..").append(symbols).append(": y;\n");
      seq.add("y");
    }
    String list = String.join(",", seq);
    List<String> finals = new ArrayList<>();
    for (int f = 1; f <= states; f++) {
      if (random.nextInt(3) != 0) {
        finals.add(String.valueOf(f));
      }
    }
    if (finals.isEmpty()) {
      finals.add(String.valueOf(states));
    }
    String output =
        seq.stream()
            .filter(v -> v.startsWith("x") || v.equals("y"))
            .distinct()
            .collect(Collectors.joining(","));
    long outputs = seq.stream().filter(v -> v.startsWith("x") || v.equals("y")).distinct().count();
    fzn.append("array [1..")
        .append(outputs)
        .append("] of var int: out:: output_array([1..")
        .append(outputs)
        .append("]) = [")
        .append(output)
        .append("];\n");
    fzn.append("constraint jacop_regular([")
        .append(list)
        .append("],")
        .append(states)
        .append(",")
        .append(symbols)
        .append(",")
        .append(Arrays.toString(d).replace(" ", ""))
        .append(",1,{")
        .append(String.join(",", finals))
        .append("},1);\n");
    for (List<Integer> cls : classes) {
      List<Integer> positions = new ArrayList<>(cls);
      if (random.nextInt(6) == 0 && positions.size() > 3) {
        positions.removeLast();
      }
      boolean around = random.nextInt(3) != 0;
      List<Integer> cover = new ArrayList<>();
      List<Integer> lb = new ArrayList<>();
      List<Integer> ub = new ArrayList<>();
      for (int s = 1; s <= symbols; s++) {
        if (random.nextInt(5) == 0) {
          continue;
        }
        int a;
        int b;
        if (around) {
          final int value = s;
          int count = (int) positions.stream().filter(i -> witness[i] == value).count();
          a = Math.max(0, count - random.nextInt(2));
          b = random.nextBoolean() ? count : count + random.nextInt(2);
        } else {
          a = random.nextInt(positions.size() + 1);
          b = random.nextBoolean() ? a : random.nextInt(positions.size() + 1);
        }
        cover.add(s);
        lb.add(Math.min(a, b));
        ub.add(Math.max(a, b));
      }
      if (cover.isEmpty()) {
        continue;
      }
      fzn.append("constraint jacop_count_values_bounds([")
          .append(positions.stream().map(seq::get).collect(Collectors.joining(",")))
          .append("],")
          .append(cover.toString().replace(" ", ""))
          .append(",")
          .append(lb.toString().replace(" ", ""))
          .append(",")
          .append(ub.toString().replace(" ", ""))
          .append(");\n");
    }
    fzn.append("solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void flowKeepsAllSolutions() throws IOException {
    Random random = new Random(1370);
    int posted = 0;
    int satisfiable = 0;
    int trials = Integer.getInteger("regularFlow.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random);
      String debug = run(model, true, "-debug", "-n", "1");
      posted += debug.contains("% regular flow") ? 1 : 0;
      Set<String> expected = solutions(run(model, false, "-a", "--lcg", "off"));
      satisfiable += expected.isEmpty() ? 0 : 1;
      assertEquals(
          expected,
          solutions(run(model, true, "-a", "--lcg", "off")),
          "trial " + trial + "\n" + model);
      assertEquals(
          expected, solutions(run(model, true, "-a")), "trial " + trial + " lcg\n" + model);
      String first = run(model, true, "-f");
      assertEquals(
          expected.isEmpty(), first.contains("UNSATISFIABLE"), "trial " + trial + " -f\n" + model);
      if (!expected.isEmpty()) {
        assertTrue(expected.containsAll(solutions(first)), "trial " + trial + " -f\n" + model);
      }
    }
    assertTrue(posted > trials / 4, "posted " + posted + " satisfiable " + satisfiable);
    assertTrue(satisfiable > trials / 10, "satisfiable " + satisfiable);
  }

  /**
   * The flows prove the rotating workforce instance the detector was made for infeasible: 2019
   * Example1370, which the search alone does not decide in minutes, is UNSAT after a few nodes with
   * them. The solution test above cannot see a flow posted weaker (a count or a conservation row
   * left out, a looser bound) or not at all, since that keeps every solution.
   */
  @Test
  void flowRefutesRotatingWorkforce() throws IOException {
    String model =
        Files.readString(
            Path.of("../jacop-benchmarks/src/test/fz/upTo5sec/rotating-workforce/Example1370.fzn"),
            StandardCharsets.UTF_8);
    String on = run(model, true, "-s", "--lcg", "on", "--default-search", "input", "-t", "20000");
    assertTrue(on.contains("=====UNSATISFIABLE====="), on);
    assertTrue(nodes(on) < 10_000, "nodes " + nodes(on));
    String off = run(model, false, "-s", "--lcg", "on", "--default-search", "input", "-t", "2000");
    assertTrue(!off.contains("UNSATISFIABLE") && nodes(off) > nodes(on), off);
  }

  private static long nodes(String out) {
    for (String line : out.split("\\R")) {
      if (line.startsWith("%%%mzn-stat: nodes=")) {
        return Long.parseLong(line.substring(19).replace(",", "").strip());
      }
    }
    return -1;
  }

  private String run(String model, boolean flow, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, Boolean.toString(flow));
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
}
