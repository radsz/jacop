/*
 * PairCoverFlatzincTest.java
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
 * The item bounds of {@link org.jacop.fz.constraints.PairCoverDetector} keep the solutions and the
 * optima of random models in the shape of the SONET ring problem.
 */
class PairCoverFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.pairCover";

  @TempDir Path tmp;

  /**
   * A random SONET-like model: g rings of capacity c (sometimes one ring of another capacity), n
   * nodes, x[r][i] whether node i is on ring r, random demanded pairs, each needing k rings with
   * both nodes, written with the pair literal forms and the demand forms the detector reads, and
   * sometimes a demand with a literal that is not a pair literal.
   */
  private static String randomModel(Random random, boolean optimise) {
    int g = 2 + random.nextInt(3);
    int n = 4 + random.nextInt(3);
    int c = 2 + random.nextInt(3);
    StringBuilder fzn = new StringBuilder();
    StringBuilder con = new StringBuilder();
    List<String> all = new ArrayList<>();
    for (int r = 0; r < g; r++) {
      List<String> row = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        String b = "x" + r + "_" + i;
        fzn.append("var bool: ").append(b).append(":: output_var;\n");
        fzn.append("var 0..1: i").append(r).append("_").append(i).append(";\n");
        con.append("constraint bool2int(")
            .append(b)
            .append(",i")
            .append(r)
            .append("_")
            .append(i)
            .append(");\n");
        row.add("i" + r + "_" + i);
      }
      all.addAll(row);
      int cap = r == 0 && random.nextInt(3) == 0 ? c + 1 : c;
      con.append("constraint int_lin_le([")
          .append(String.join(",", java.util.Collections.nCopies(n, "1")))
          .append("],[")
          .append(String.join(",", row))
          .append("],")
          .append(cap)
          .append(");\n");
    }
    int lits = 0;
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (random.nextInt(3) == 0) {
          continue;
        }
        int k = random.nextInt(4) == 0 ? 2 : 1;
        List<String> b = new ArrayList<>();
        for (int r = 0; r < g; r++) {
          String l = "b" + lits++;
          fzn.append("var 0..1: ").append(l).append(";\n");
          if (random.nextBoolean()) {
            con.append("constraint int_lin_le_imp([-1,-1],[i")
                .append(r)
                .append("_")
                .append(i)
                .append(",i")
                .append(r)
                .append("_")
                .append(j)
                .append("],-2,")
                .append(l)
                .append(");\n");
          } else {
            fzn.append("var bool: a").append(l).append(";\n");
            con.append("constraint array_bool_and([x")
                .append(r)
                .append("_")
                .append(i)
                .append(",x")
                .append(r)
                .append("_")
                .append(j)
                .append("],a")
                .append(l)
                .append(");\n");
            con.append("constraint bool2int(a").append(l).append(",").append(l).append(");\n");
          }
          b.add(l);
        }
        if (random.nextInt(8) == 0) {
          // a demand also met otherwise: not a pair cover
          String l = "b" + lits++;
          fzn.append("var 0..1: ").append(l).append(";\n");
          b.add(l);
        }
        String list = String.join(",", b);
        switch (random.nextInt(2)) {
          case 0 -> {
            fzn.append("var ")
                .append(k)
                .append("..")
                .append(b.size())
                .append(": n")
                .append(lits)
                .append(";\n");
            con.append("constraint jacop_among([")
                .append(list)
                .append("],1..1,n")
                .append(lits)
                .append(");\n");
          }
          default ->
              con.append("constraint int_lin_le([")
                  .append(String.join(",", java.util.Collections.nCopies(b.size(), "-1")))
                  .append("],[")
                  .append(list)
                  .append("],")
                  .append(-k)
                  .append(");\n");
        }
      }
    }
    if (optimise) {
      fzn.append("var 0..").append(g * n).append(": obj:: output_var;\n");
    }
    fzn.append(con);
    if (optimise) {
      fzn.append("constraint int_lin_eq([")
          .append(String.join(",", java.util.Collections.nCopies(all.size(), "1")))
          .append(",-1],[")
          .append(String.join(",", all))
          .append(",obj],0);\n");
      fzn.append("solve minimize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  @Test
  void boundsKeepAllSolutions() throws IOException {
    Random random = new Random(51);
    int posted = 0;
    int satisfiable = 0;
    int trials = Integer.getInteger("pairCover.trials", 200);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String debug = run(model, true, "-debug", "-n", "1");
      posted += debug.contains("% pair cover") && !debug.contains(" 0 item bounds") ? 1 : 0;
      Set<String> expected = solutions(run(model, false, "-a"));
      satisfiable += expected.isEmpty() ? 0 : 1;
      assertEquals(expected, solutions(run(model, true, "-a")), "trial " + trial + "\n" + model);
    }
    assertTrue(posted > trials / 3, "posted " + posted);
    assertTrue(satisfiable > trials / 10, "satisfiable " + satisfiable);
  }

  @Test
  void boundsKeepOptima() throws IOException {
    Random random = new Random(52);
    int trials = Integer.getInteger("pairCover.trials", 200);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"), model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on", "-f"), model),
          "trial " + trial + " lcg -f\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "off"), model),
          "trial " + trial + " cp\n" + model);
    }
  }

  private String run(String model, boolean cover, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, Boolean.toString(cover));
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
  private static String optimum(String out, String model) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out + "\n" + model);
    return last;
  }
}
