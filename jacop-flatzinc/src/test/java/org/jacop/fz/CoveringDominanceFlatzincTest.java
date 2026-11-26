/*
 * CoveringDominanceFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertNotNull;
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
 * The column dominance of covering models ({@link CoveringDominance}) keeps the optimum: random
 * weighted set covering models, with some columns also in other constraints or negated in a clause,
 * have the same optimum with the rule as without it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class CoveringDominanceFlatzincTest {

  private static final Pattern OBJECTIVE = Pattern.compile("(?m)^cost = (-?\\d+);");
  private static final Pattern FIXED = Pattern.compile("%%%mzn-stat: coveringFixed=(\\d+)");
  private static final Pattern FOLDED = Pattern.compile("%%%mzn-stat: lpFoldedColumns=(\\d+)");

  @TempDir Path tmp;

  @Test
  void keepsTheOptimumOfRandomCoveringModels() throws IOException {
    Random random = new Random(20261126);
    int fired = 0;
    for (int t = 0; t < 30; t++) {
      // up to 40 columns, so that some objectives are split into block sums under LCG
      String fzn = randomModel(random, 6 + random.nextInt(35), 1, 3 + random.nextInt(10));
      String mode = t % 3 == 0 ? "-f" : null;
      String on = run(fzn, null, mode);
      String off = run(fzn, "false", mode);
      assertNotNull(objective(off), "model " + t + "\n" + off);
      assertEquals(objective(off), objective(on), "model " + t + "\n" + fzn);
      fired += count(FIXED, on) > 0 ? 1 : 0;
      assertEquals(-1, count(FIXED, off), "model " + t);
    }
    assertTrue(fired > 15, "the rule fixed columns on " + fired + " of 30 models");
  }

  @Test
  void foldsTheFixedColumnsOutOfTheRelaxation() throws IOException {
    // 30 distinct columns, each with 50 copies of higher cost: the rule fixes the copies, and the
    // relaxation takes them as constants of the objective's rows
    String fzn = randomModel(new Random(7), 30, 50, 40);
    String on = run(fzn, null, null);
    String off = run(fzn, "false", null);
    assertNotNull(objective(off), off);
    assertEquals(objective(off), objective(on));
    assertTrue(count(FIXED, on) >= 1000, on);
    assertTrue(count(FOLDED, on) >= 1000, on);
  }

  // minimize the cost of columns over random rows that must each hold a chosen column; each column
  // has copies of its rows at a higher cost; a few columns are also negated in a clause or in a
  // cap with another, so that they are no candidates
  private static String randomModel(Random random, int columns, int copies, int rows) {
    int n = columns * copies;
    boolean[][] in = new boolean[rows][columns];
    for (int r = 0; r < rows; r++) {
      for (int j = 0; j < columns; j++) {
        in[r][j] = random.nextInt(4) == 0;
      }
      in[r][random.nextInt(columns)] = true;
    }
    StringBuilder s = new StringBuilder();
    StringBuilder c = new StringBuilder();
    StringJoiner xs = new StringJoiner(",");
    StringJoiner cs = new StringJoiner(",");
    for (int i = 0; i < n; i++) {
      s.append("var bool: x").append(i).append(" :: output_var;\n");
      s.append("var 0..1: y").append(i).append(";\n");
      c.append("constraint bool2int(x").append(i).append(",y").append(i).append(");\n");
      xs.add("y" + i);
      int base = 1 + random.nextInt(4);
      cs.add(Integer.toString(i < columns ? base : base + random.nextInt(3)));
    }
    for (int r = 0; r < rows; r++) {
      StringJoiner lits = new StringJoiner(",");
      for (int i = 0; i < n; i++) {
        if (in[r][i % columns]) {
          lits.add("x" + i);
        }
      }
      c.append("constraint bool_clause([").append(lits).append("],[]);\n");
    }
    for (int k = random.nextInt(4); k > 0; k--) {
      int a = random.nextInt(n);
      int b = random.nextInt(n);
      c.append("constraint bool_clause([x").append(a).append("],[x").append(b).append("]);\n");
    }
    if (random.nextBoolean()) {
      int a = random.nextInt(n);
      int b = random.nextInt(n);
      if (a != b) {
        c.append("constraint int_lin_le([1,1],[y")
            .append(a)
            .append(",y")
            .append(b)
            .append("],1);\n");
      }
    }
    s.append("var 0..").append(4 * n).append(": cost :: output_var;\n");
    s.append(c);
    s.append("constraint int_lin_eq([")
        .append(cs)
        .append(",-1],[")
        .append(xs)
        .append(",cost],0);\n");
    s.append("solve minimize cost;\n");
    return s.toString();
  }

  private static String objective(String out) {
    String found = null;
    for (Matcher m = OBJECTIVE.matcher(out); m.find(); ) {
      found = m.group(1);
    }
    return found;
  }

  private static int count(Pattern p, String out) {
    Matcher m = p.matcher(out);
    return m.find() ? Integer.parseInt(m.group(1)) : -1;
  }

  private String run(String model, String covering, String mode) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] options = mode == null ? new String[0] : new String[] {mode};
    // the rule reads the clauses that lazy clause generation collects; the build runs without it
    String[] args = Arrays.copyOf(options, options.length + 7);
    args[options.length] = "--lcg";
    args[options.length + 1] = "on";
    args[options.length + 2] = "-s";
    args[options.length + 3] = "--search-statistics";
    args[options.length + 4] = "-t";
    args[options.length + 5] = "20000";
    args[options.length + 6] = fzn.toString();
    if (covering != null) {
      System.setProperty("org.jacop.fz.coveringDominance", covering);
    }
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty("org.jacop.fz.coveringDominance");
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
