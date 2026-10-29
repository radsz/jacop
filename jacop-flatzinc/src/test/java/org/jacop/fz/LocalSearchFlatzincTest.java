/*
 * LocalSearchFlatzincTest.java
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of local search before free search (--free-config ls). Under --lcg the clauses of the model
 * go to the SAT solver, not to the store, so local search must evaluate them itself: a solution
 * that violated one, checked only in the store, gave a wrong optimum on amaze.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class LocalSearchFlatzincTest {

  @TempDir Path tmp;

  // a smallest vertex cover of a cycle of six vertices: 3
  private static final String COVER =
      """
      var bool: x1:: output_var;
      var bool: x2:: output_var;
      var bool: x3:: output_var;
      var bool: x4:: output_var;
      var bool: x5:: output_var;
      var bool: x6:: output_var;
      var 0..6: cost:: output_var:: is_defined_var;
      constraint bool_clause([x1,x2],[]);
      constraint bool_clause([x2,x3],[]);
      constraint bool_clause([x3,x4],[]);
      constraint bool_clause([x4,x5],[]);
      constraint bool_clause([x5,x6],[]);
      constraint bool_clause([x6,x1],[]);
      constraint bool_lin_eq([1,1,1,1,1,1],[x1,x2,x3,x4,x5,x6],cost):: defines_var(cost);
      """;

  private static final Pattern COST = Pattern.compile("cost = (\\d+);");

  @Test
  void optimumUnderLcg() throws IOException {
    checkOptimum(run(COVER + "solve minimize cost;\n", "--lcg", "-f", "-a", "-s", "-t", "5000"));
  }

  @Test
  void optimumUnderFreeSearch() throws IOException {
    checkOptimum(run(COVER + "solve minimize cost;\n", "-f", "-a", "-s", "-t", "5000"));
  }

  @Test
  void satisfactionUnderLcgPrintsAValidSolution() throws IOException {
    String out =
        run(
            COVER + "constraint int_le(cost,3);\nsolve satisfy;\n",
            "--lcg",
            "-f",
            "-s",
            "-t",
            "5000");
    assertTrue(out.contains("lsSolutions=1"), out);
    boolean[] x = new boolean[7];
    for (int i = 1; i <= 6; i++) {
      x[i] = out.contains("x" + i + " = true;");
    }
    for (int i = 1; i <= 6; i++) {
      assertTrue(x[i] || x[i % 6 + 1], "edge " + i + " uncovered: " + out);
    }
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
    assertEquals(3, costs.get(costs.size() - 1), out);
    assertTrue(out.contains("=========="), out);
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = Arrays.copyOf(options, options.length + 3);
    args[options.length] = "--free-config";
    args[options.length + 1] = "ls=0.5,ls-patience=0";
    args[options.length + 2] = fzn.toString();
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
