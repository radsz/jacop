/*
 * DominanceFlatzincTest.java
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
 * The dominance nogoods are on by default for fixed search and off under {@code -f}; with them the
 * optimum of random covering models stays the one found without them.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class DominanceFlatzincTest {

  private static final Pattern OBJECTIVE = Pattern.compile("%%%mzn-stat: objective=(-?\\d+)");
  private static final Pattern NOGOODS = Pattern.compile("%%%mzn-stat: dominanceNogoods=(\\d+)");
  private static final String UNSAT = "=====UNSATISFIABLE=====";

  @TempDir Path tmp;

  @Test
  void onByDefaultForFixedSearchAndKeepsTheOptimum() throws IOException {
    Random random = new Random(20261114);
    int fired = 0;
    for (int t = 0; t < 40; t++) {
      String fzn = randomModel(random);
      String on = run(fzn, null);
      String off = run(fzn, "false");
      assertEquals(objective(off), objective(on), "model " + t + "\n" + fzn);
      assertEquals(off.contains(UNSAT), on.contains(UNSAT), "model " + t + "\n" + fzn);
      fired += nogoods(on) > 0 ? 1 : 0;
      assertEquals(-1, nogoods(off), "model " + t);
      assertEquals(-1, nogoods(run(fzn, null, "-f")), "model " + t + " under -f");
    }
    assertTrue(fired > 20, "nogoods on " + fired + " of 40 models");
  }

  // minimize sum c_i x_i subject to a cover sum x_i >= d and a few pair caps x_i + x_j <= u
  private static String randomModel(Random random) {
    int n = 4 + random.nextInt(4);
    StringBuilder s = new StringBuilder();
    StringJoiner xs = new StringJoiner(",");
    StringJoiner cs = new StringJoiner(",");
    StringJoiner ones = new StringJoiner(",");
    for (int i = 0; i < n; i++) {
      s.append("var 0..")
          .append(2 + random.nextInt(5))
          .append(": x")
          .append(i)
          .append(" :: output_var;\n");
      xs.add("x" + i);
      cs.add(Integer.toString(1 + random.nextInt(6)));
      ones.add("-1");
    }
    s.append("var 0..1000: cost :: output_var;\n");
    s.append("constraint int_lin_le([")
        .append(ones)
        .append("],[")
        .append(xs)
        .append("],")
        .append(-(n + random.nextInt(2 * n)))
        .append(");\n");
    for (int k = 0; k < 2; k++) {
      int i = random.nextInt(n);
      int j = (i + 1 + random.nextInt(n - 1)) % n;
      s.append("constraint int_lin_le([1,1],[x")
          .append(i)
          .append(",x")
          .append(j)
          .append("],")
          .append(2 + random.nextInt(6))
          .append(");\n");
    }
    s.append("constraint int_lin_eq([")
        .append(cs)
        .append(",-1],[")
        .append(xs)
        .append(",cost],0);\n");
    s.append("solve :: int_search([")
        .append(xs)
        .append("],input_order,indomain_max,complete) minimize cost;\n");
    return s.toString();
  }

  private static String objective(String out) {
    String found = null;
    for (Matcher m = OBJECTIVE.matcher(out); m.find(); ) {
      found = m.group(1);
    }
    return found;
  }

  private static int nogoods(String out) {
    Matcher m = NOGOODS.matcher(out);
    return m.find() ? Integer.parseInt(m.group(1)) : -1;
  }

  private String run(String model, String dominance, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 4);
    args[options.length] = "--search-statistics";
    args[options.length + 1] = "-t";
    args[options.length + 2] = "20000";
    args[options.length + 3] = fzn.toString();
    if (dominance != null) {
      System.setProperty("org.jacop.fz.dominance", dominance);
    }
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty("org.jacop.fz.dominance");
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
