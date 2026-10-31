/*
 * LcgSlowFallbackFlatzincTest.java
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of LCG free search giving way to free search without learning (--free-config
 * lcg-slow-rate). The store must get back the clauses of the model, which under LCG went to the SAT
 * solver only, and free search must improve on the solutions printed before it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class LcgSlowFallbackFlatzincTest {

  @TempDir Path tmp;

  private static final int N = 21;

  private static final Pattern COST = Pattern.compile("cost = (\\d+);");

  // a smallest set of vertices of a cycle of N with one in every three consecutive ones, N / 3, as
  // clauses
  private static String cover() {
    StringBuilder s = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    StringBuilder ones = new StringBuilder();
    for (int i = 1; i <= N; i++) {
      s.append("var bool: x").append(i).append(":: output_var;\n");
      xs.append(i == 1 ? "" : ",").append('x').append(i);
      ones.append(i == 1 ? "" : ",").append('1');
    }
    s.append("var 0..").append(N).append(": cost:: output_var:: is_defined_var;\n");
    for (int i = 1; i <= N; i++) {
      s.append("constraint bool_clause([x")
          .append(i)
          .append(",x")
          .append(i % N + 1)
          .append(",x")
          .append((i + 1) % N + 1)
          .append("],[]);\n");
    }
    s.append("constraint bool_lin_eq([").append(ones).append("],[").append(xs);
    s.append("],cost):: defines_var(cost);\nsolve minimize cost;\n");
    return s.toString();
  }

  @Test
  void optimumAfterGivingWayAtOnce() throws IOException {
    String out = run("lcg-slow-rate=1,lcg-slow-at=0");
    assertTrue(out.contains("lcgSlowConflicts=0"), out);
    checkOptimum(out);
  }

  @Test
  void optimumAfterGivingWayToLocalSearchSolution() throws IOException {
    // local search prints a solution first, which LCG at its root, or free search without learning,
    // must improve on or prove optimal
    checkOptimum(run("lcg-slow-rate=1,lcg-slow-at=0,ls=0.5,ls-patience=0"));
  }

  @Test
  void optimumWhenLcgIsFastEnough() throws IOException {
    String out = run("lcg-slow-rate=0.001,lcg-slow-at=0.5");
    assertTrue(!out.contains("lcgSlowConflicts="), out);
    checkOptimum(out);
  }

  private static void checkOptimum(String out) {
    List<Integer> costs = new ArrayList<>();
    Matcher m = COST.matcher(out);
    while (m.find()) {
      costs.add(Integer.parseInt(m.group(1)));
    }
    assertTrue(!costs.isEmpty(), out);
    for (int k = 1; k < costs.size(); k++) {
      assertTrue(costs.get(k) < costs.get(k - 1), out);
    }
    assertEquals(N / 3, costs.get(costs.size() - 1), out);
    assertTrue(out.contains("=========="), out);
  }

  private String run(String config) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, cover(), StandardCharsets.UTF_8);
    String[] args = {
      // without the linear relaxation, whose rows of the clauses would enforce them
      "--lcg",
      "-f",
      "-a",
      "-s",
      "--lp",
      "off",
      "-t",
      "10000",
      "--free-config",
      config,
      fzn.toString()
    };
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
