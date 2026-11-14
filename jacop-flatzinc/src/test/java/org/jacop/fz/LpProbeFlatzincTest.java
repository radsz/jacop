/*
 * LpProbeFlatzincTest.java
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The search before an expensive root LP ({@code org.jacop.fz.lpProbe}): a probe that finishes the
 * search and a probe followed by the restart with the relaxation give the answer of the search
 * without a probe, under LCG and under plain depth-first search.
 */
class LpProbeFlatzincTest {

  private static final String UNSAT = "=====UNSATISFIABLE=====";
  private static final Pattern OBJECTIVE = Pattern.compile("%%%mzn-stat: objective=(-?\\d+)");
  private static final Pattern PROBE = Pattern.compile("%%%mzn-stat: lpProbe=(\\w+)");

  @TempDir Path tmp;

  @Test
  void probedSearchKeepsTheOptimumUnderLcg() throws IOException {
    check(new Random(20261114), 60, "--lcg", "on");
  }

  @Test
  void probedSearchKeepsTheOptimumWithoutLcg() throws IOException {
    check(new Random(20261115), 40, "--lcg", "off");
  }

  private void check(Random random, int models, String... options) throws IOException {
    int finished = 0;
    int restarted = 0;
    StringBuilder states = new StringBuilder();
    for (int t = 0; t < models; t++) {
      String fzn = randomModel(random, t % 4 == 3);
      String off = run(fzn, 0, options);
      // a probe of 1 ms restarts with the relaxation on most models (how many depends on the speed
      // of
      // the machine), a probe of 20 s finishes the search
      for (long probe : new long[] {1, 20_000}) {
        String on = run(fzn, probe, options);
        assertEquals(off.contains(UNSAT), on.contains(UNSAT), fzn + "\n" + off + "\n" + on);
        assertEquals(objective(off), objective(on), fzn + "\n" + off + "\n" + on);
        assertTrue(on.contains("==========") || on.contains(UNSAT), fzn + "\n" + on);
        String state = group(PROBE, on);
        states.append(probe).append(':').append(state).append(' ');
        finished += probe > 1 && "finished".equals(state) ? 1 : 0;
        restarted += probe == 1 && "solved".equals(state) ? 1 : 0;
      }
    }
    assertTrue(
        finished > models / 2 && restarted > models / 10,
        finished + " finished, " + restarted + " restarted: " + states);
  }

  // a knapsack with several capacity rows and equalities between pairs of items: rows enough for a
  // relaxation, and a search of some thousands of nodes; satisfiable models when unsat is false
  private static String randomModel(Random random, boolean unsat) {
    int n = 10 + random.nextInt(5);
    StringBuilder fzn = new StringBuilder();
    for (int j = 0; j < n; j++) {
      fzn.append("var 0..").append(3 + random.nextInt(5)).append(": x").append(j);
      fzn.append(":: output_var;\n");
    }
    fzn.append("var -1000..1000: z:: output_var;\n");
    for (int r = 0; r < 3; r++) {
      StringJoiner a = new StringJoiner(",", "[", "]");
      StringJoiner x = new StringJoiner(",", "[", "]");
      for (int j = 0; j < n; j++) {
        a.add(Integer.toString(1 + random.nextInt(9)));
        x.add("x" + j);
      }
      fzn.append("constraint int_lin_le(").append(a).append(',').append(x).append(',');
      fzn.append(20 + random.nextInt(30)).append(");\n");
    }
    int i = random.nextInt(n);
    int k = (i + 1 + random.nextInt(n - 1)) % n;
    fzn.append("constraint int_lin_eq([1,-1],[x").append(i).append(",x").append(k);
    fzn.append("],").append(unsat ? 100 : random.nextInt(3) - 1).append(");\n");
    StringJoiner a = new StringJoiner(",", "[", "]");
    StringJoiner x = new StringJoiner(",", "[", "]");
    for (int j = 0; j < n; j++) {
      a.add(Integer.toString(1 + random.nextInt(9)));
      x.add("x" + j);
    }
    a.add("-1");
    x.add("z");
    fzn.append("constraint int_lin_eq(").append(a).append(',').append(x).append(",0);\n");
    StringJoiner vars = new StringJoiner(",", "[", "]");
    for (int j = 0; j < n; j++) {
      vars.add("x" + j);
    }
    fzn.append("solve :: int_search(")
        .append(vars)
        .append(", input_order, indomain_min, complete)");
    return fzn.append(" maximize z;\n").toString();
  }

  private static String objective(String out) {
    return group(OBJECTIVE, out);
  }

  private static String group(Pattern pattern, String out) {
    String found = null;
    Matcher m = pattern.matcher(out);
    while (m.find()) {
      found = m.group(1);
    }
    return found;
  }

  private String run(String model, long probe, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 4);
    args[options.length] = "--search-statistics";
    args[options.length + 1] = "-t";
    args[options.length + 2] = "20000";
    args[options.length + 3] = fzn.toString();
    System.setProperty("org.jacop.fz.lpProbe", Long.toString(probe));
    System.setProperty("org.jacop.fz.lpProbeSize", "0");
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty("org.jacop.fz.lpProbe");
      System.clearProperty("org.jacop.fz.lpProbeSize");
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
