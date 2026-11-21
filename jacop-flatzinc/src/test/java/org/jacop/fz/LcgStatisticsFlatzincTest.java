/*
 * LcgStatisticsFlatzincTest.java
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * The standard statistics under --lcg: peakDepth was always 0 and restarts did not count the SAT
 * solver's restarts.
 */
@Timeout(60)
class LcgStatisticsFlatzincTest {

  @TempDir Path tmp;

  /** A 0/1 knapsack of 14 items: optimality takes search and conflicts under --lcg. */
  private static String knapsack(String search) {
    int[] w = {25, 47, 44, 18, 33, 48, 40, 50, 47, 14, 48, 10, 40, 26};
    int[] v = {45, 24, 22, 55, 40, 44, 45, 40, 35, 50, 19, 24, 50, 19};
    StringBuilder fzn = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    StringBuilder ws = new StringBuilder();
    StringBuilder vs = new StringBuilder();
    for (int i = 0; i < w.length; i++) {
      fzn.append("var 0..1: x").append(i).append(" :: output_var;\n");
      String sep = i == 0 ? "" : ",";
      xs.append(sep).append('x').append(i);
      ws.append(sep).append(w[i]);
      vs.append(sep).append(v[i]);
    }
    fzn.append("var 0..1000: obj :: output_var;\n")
        .append("constraint int_lin_le([")
        .append(ws)
        .append("],[")
        .append(xs)
        .append("],245);\n")
        .append("constraint int_lin_eq([")
        .append(vs)
        .append(",-1],[")
        .append(xs)
        .append(",obj],0);\n")
        .append("solve ")
        .append(search)
        .append(" maximize obj;\n");
    return fzn.toString();
  }

  @Test
  void peakDepthUnderAnnotatedLcgSearch() throws IOException {
    String out =
        solve(
            knapsack(
                ":: int_search(["
                    + "x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13"
                    + "], input_order, indomain_max, complete)"),
            "--lcg",
            "-s");
    assertTrue(out.contains("=========="), out);
    long depth = stat(out, "peakDepth");
    assertTrue(depth > 0, out);
    assertTrue(depth <= stat(out, "nodes"), out);
  }

  @Test
  void peakDepthAndRestartsUnderLcgFreeSearch() throws IOException {
    String out = solve(knapsack(""), "--lcg", "-f", "-s");
    assertTrue(out.contains("=========="), out);
    long depth = stat(out, "peakDepth");
    assertTrue(depth > 0, out);
    assertTrue(depth <= stat(out, "nodes"), out);
    assertEquals(stat(out, "lcgRestarts"), stat(out, "restarts"), out);
  }

  private static long stat(String out, String name) {
    Matcher m = Pattern.compile("%%%mzn-stat: " + name + "=(\\d+)").matcher(out);
    assertTrue(m.find(), name + " missing in\n" + out);
    return Long.parseLong(m.group(1));
  }

  private String solve(String model, String... options) throws IOException {
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
}
