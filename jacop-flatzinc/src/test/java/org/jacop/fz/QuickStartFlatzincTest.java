/*
 * QuickStartFlatzincTest.java
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
import java.util.List;
import java.util.Random;
import java.util.StringJoiner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The quick start of free search on small models ({@code org.jacop.fz.quickStartWork}): a quick
 * start that finishes, and one that stops after some solutions and hands over to free search, give
 * the answer of free search without it, and the printed solutions only improve.
 */
class QuickStartFlatzincTest {

  private static final String UNSAT = "=====UNSATISFIABLE=====";
  private static final Pattern OBJECTIVE = Pattern.compile("%%%mzn-stat: objective=(-?\\d+)");
  private static final Pattern STATE = Pattern.compile("%%%mzn-stat: quickStart=([\\w-]+)");
  private static final Pattern Z = Pattern.compile("(?m)^z = (-?\\d+);");

  @TempDir Path tmp;

  @Test
  void quickStartKeepsTheAnswerOfFreeSearch() throws IOException {
    Random random = new Random(20261126);
    int finished = 0;
    int unfinished = 0;
    for (int t = 0; t < 24; t++) {
      String fzn = randomModel(random, t % 4 == 3);
      String off = run(fzn, 0);
      // a budget of 100 work stops after the first solutions, the default finishes
      for (long work : new long[] {100, 2_000_000}) {
        String on = run(fzn, work);
        assertEquals(off.contains(UNSAT), on.contains(UNSAT), fzn + "\n" + off + "\n" + on);
        assertEquals(group(OBJECTIVE, off), group(OBJECTIVE, on), fzn + "\n" + off + "\n" + on);
        assertTrue(on.contains("==========") || on.contains(UNSAT), fzn + "\n" + on);
        List<Integer> printed = new ArrayList<>();
        Matcher m = Z.matcher(on);
        while (m.find()) {
          printed.add(Integer.parseInt(m.group(1)));
        }
        for (int i = 1; i < printed.size(); i++) {
          // maximize z: every solution printed is better than the one before
          assertTrue(printed.get(i) > printed.get(i - 1), printed + "\n" + fzn + "\n" + on);
        }
        String state = group(STATE, on);
        finished += "finished".equals(state) ? 1 : 0;
        unfinished += work == 100 && "unfinished".equals(state) && !printed.isEmpty() ? 1 : 0;
      }
      assertEquals(null, group(STATE, off), off);
    }
    assertTrue(
        finished > 12 && unfinished > 0, finished + " finished, " + unfinished + " unfinished");
  }

  // a knapsack with several capacity rows and an equality between two items; unsatisfiable when
  // unsat is true
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
    return fzn.append("solve maximize z;\n").toString();
  }

  private static String group(Pattern pattern, String out) {
    String found = null;
    Matcher m = pattern.matcher(out);
    while (m.find()) {
      found = m.group(1);
    }
    return found;
  }

  private String run(String model, long work) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = {"-f", "--lcg", "on", "-a", "-s", "-t", "20000", fzn.toString()};
    // the quick start is off by default: restore the property afterwards
    String previous = System.setProperty("org.jacop.fz.quickStartWork", Long.toString(work));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      if (previous == null) {
        System.clearProperty("org.jacop.fz.quickStartWork");
      } else {
        System.setProperty("org.jacop.fz.quickStartWork", previous);
      }
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
