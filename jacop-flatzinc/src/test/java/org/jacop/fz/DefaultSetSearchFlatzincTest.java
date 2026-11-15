/*
 * DefaultSetSearchFlatzincTest.java
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
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The default search of a model without search annotation branches on its set variables in input
 * order. The model is gardner_dinner as MiniZinc flattens it: 35 dinners of three of 15 guests, any
 * two sharing at most one guest (a Steiner triple system of order 15). Input order finds a solution
 * in a few hundred nodes; JaCoP 5.0 picked the set of the largest failure count, and LCG's default
 * branching left the sets out, and neither found a solution in 30 s.
 */
class DefaultSetSearchFlatzincTest {

  private static final int DINNERS = 35;
  private static final int GUESTS = 15;

  @TempDir Path tmp;

  private static String model() {
    StringBuilder vars = new StringBuilder();
    StringBuilder constraints = new StringBuilder();
    for (int i = 0; i < DINNERS; i++) {
      vars.append("var set of 1..").append(GUESTS).append(": x").append(i);
      vars.append(":: output_var;\n");
    }
    for (int i = 0; i < DINNERS; i++) {
      for (int j = i + 1; j < DINNERS; j++) {
        String z = "z" + i + "_" + j;
        String c = "c" + i + "_" + j;
        vars.append("var set of 1..").append(GUESTS).append(": ").append(z);
        vars.append(":: var_is_introduced :: is_defined_var;\n");
        vars.append("var 0..1: ").append(c).append(":: var_is_introduced :: is_defined_var;\n");
        constraints.append("constraint set_intersect(x").append(i).append(",x").append(j);
        constraints.append(",").append(z).append("):: defines_var(").append(z).append(");\n");
        constraints.append("constraint set_card(").append(z).append(",").append(c);
        constraints.append("):: defines_var(").append(c).append(");\n");
        constraints.append("constraint set_ne(x").append(i).append(",x").append(j).append(");\n");
      }
    }
    for (int i = 0; i < DINNERS; i++) {
      constraints.append("constraint set_card(x").append(i).append(",3);\n");
    }
    return vars + constraints.toString() + "solve satisfy;\n";
  }

  @Test
  void freeSearchWithoutLcg() throws IOException {
    check(run("--lcg", "off"));
  }

  @Test
  void freeSearchWithLcg() throws IOException {
    check(run("--lcg", "on"));
  }

  @Test
  void lcgBacktracksOneLevelInTheDefaultBranching() throws IOException {
    // LCG's backjumps over the decisions of the default branching took them again after each of
    // the 90 conflicts: 2,242 decisions, 175 with one-level backtracking (266 nodes without LCG)
    String out = run("--lcg", "on", "-s");
    check(out);
    long nodes = nodes(out);
    assertTrue(nodes < 600, "nodes with one-level backtracking: " + nodes);
    long backjumping = nodes(run("--lcg", "on", "-s", "--free-config", "lcg-chrono=-1"));
    assertTrue(backjumping > 2 * nodes, "nodes with backjumps " + backjumping + ", " + nodes);
  }

  static long nodes(String out) {
    Matcher m = Pattern.compile("^%%%mzn-stat: nodes=(\\d+)$", Pattern.MULTILINE).matcher(out);
    long nodes = -1;
    while (m.find()) {
      nodes = Long.parseLong(m.group(1)); // the last one: the search's own
    }
    assertTrue(nodes >= 0, "no node count:\n" + out);
    return nodes;
  }

  @Test
  void freeSearchOption() throws IOException {
    check(run("-f", "--lcg", "on"));
  }

  @Test
  void failureCountHeuristicStillAvailable() throws IOException {
    String out = run("--lcg", "off", "--free-config", "set-heuristic=afc", "-t", "1000");
    assertTrue(out.contains("=====UNKNOWN=====") || out.contains("----------"), out);
  }

  private String run(String... options) throws IOException {
    Path fzn = tmp.resolve("gardner_dinner.fzn");
    Files.writeString(fzn, model(), StandardCharsets.UTF_8);
    List<String> args = new ArrayList<>(Arrays.asList(options));
    if (!args.contains("-t")) {
      args.add("-t");
      args.add("10000");
    }
    args.add(fzn.toString());
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  /** The output has a solution: 35 distinct triples, any two sharing at most one guest. */
  private static void check(String out) {
    assertTrue(out.contains("----------"), "no solution found:\n" + out);
    Pattern line = Pattern.compile("^x(\\d+) = (.*);$", Pattern.MULTILINE);
    List<TreeSet<Integer>> dinners = new ArrayList<>();
    for (int i = 0; i < DINNERS; i++) {
      dinners.add(null);
    }
    Matcher m = line.matcher(out);
    while (m.find()) {
      dinners.set(Integer.parseInt(m.group(1)), parse(m.group(2)));
    }
    for (int i = 0; i < DINNERS; i++) {
      TreeSet<Integer> a = dinners.get(i);
      assertTrue(a != null, "x" + i + " not printed:\n" + out);
      assertEquals(3, a.size(), "x" + i + " = " + a);
      assertTrue(a.first() >= 1 && a.last() <= GUESTS, "x" + i + " = " + a);
      for (int j = 0; j < i; j++) {
        TreeSet<Integer> common = new TreeSet<>(a);
        common.retainAll(dinners.get(j));
        assertTrue(common.size() <= 1, "x" + j + " and x" + i + " share " + common);
      }
    }
  }

  // a set as fzn-jacop prints it: {1, 10, 11}, 1..3 or {}
  private static TreeSet<Integer> parse(String set) {
    TreeSet<Integer> elements = new TreeSet<>();
    String s = set.strip();
    if (s.startsWith("{")) {
      s = s.substring(1, s.length() - 1);
    }
    for (String part : s.split(",")) {
      String p = part.strip();
      if (p.isEmpty()) {
        continue;
      }
      int dots = p.indexOf("..");
      if (dots < 0) {
        elements.add(Integer.parseInt(p));
      } else {
        int lo = Integer.parseInt(p.substring(0, dots).strip());
        int hi = Integer.parseInt(p.substring(dots + 2).strip());
        for (int v = lo; v <= hi; v++) {
          elements.add(v);
        }
      }
    }
    return elements;
  }
}
