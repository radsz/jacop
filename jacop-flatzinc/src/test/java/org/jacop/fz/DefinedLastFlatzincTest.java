/*
 * DefinedLastFlatzincTest.java
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
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Free search on a model without a search annotation branches on the variables that no defines_var
 * annotation names before the defined ones (Solve.definedLast). The model is a feedback arc
 * ordering as XCSP 2026 Feedback translates it: x a permutation of the nodes and, for each arc i to
 * j, b = (x_i &lt; x_j), d = x_i - x_j and z = if b then 0 else d, all three defined. Every
 * permutation is a solution. Branching on the penalties z, smallest value first, pinned distances
 * x_i - x_j and failed: free search without learning found no solution in 10 s, after 27,000
 * failures, and LCG one after about 600 conflicts.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class DefinedLastFlatzincTest {

  @TempDir Path tmp;

  private static final Pattern FAILURES = Pattern.compile("%%%mzn-stat: failures=(\\d+)");

  // the nodes and arcs of the random digraph
  private static final int NODES = 100;
  private static final int ARCS = 1300;

  private static String feedback() {
    Random random = new Random(1);
    Set<Long> arcs = new TreeSet<>();
    while (arcs.size() < ARCS) {
      int i = random.nextInt(NODES);
      int j = random.nextInt(NODES);
      if (i != j) {
        arcs.add((long) i * NODES + j);
      }
    }
    StringBuilder s = new StringBuilder();
    s.append("predicate jacop_alldiff(array [int] of var int: x);\n");
    s.append("predicate jacop_if_then_else_int(array [int] of var bool: c,");
    s.append("array [int] of var int: x,var int: y);\n");
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < NODES; i++) {
      s.append("var 0..").append(NODES - 1).append(": x").append(i).append(":: output_var;\n");
      xs.append(i == 0 ? "" : ",").append('x').append(i);
    }
    StringBuilder constraints = new StringBuilder();
    constraints.append("constraint jacop_alldiff([").append(xs).append("]);\n");
    int k = 0;
    for (long arc : arcs) {
      long i = arc / NODES;
      long j = arc % NODES;
      s.append("var bool: b").append(k).append(":: is_defined_var;\n");
      s.append("var ").append(1 - NODES).append("..").append(NODES - 1);
      s.append(": d").append(k).append(":: is_defined_var;\n");
      s.append("var 0..").append(NODES - 1).append(": z").append(k);
      s.append(":: output_var:: is_defined_var;\n");
      constraints.append("constraint int_lin_le_reif([1,-1],[x").append(i).append(",x").append(j);
      constraints.append("],-1,b").append(k).append("):: defines_var(b").append(k).append(");\n");
      constraints.append("constraint int_lin_eq([1,-1,-1],[x").append(i).append(",x").append(j);
      constraints.append(",d").append(k).append("],0):: defines_var(d").append(k).append(");\n");
      constraints.append("constraint jacop_if_then_else_int([b").append(k).append(",true],[0,d");
      constraints.append(k).append("],z").append(k).append("):: defines_var(z").append(k);
      constraints.append(");\n");
      k++;
    }
    return s.append(constraints).append("solve satisfy;\n").toString();
  }

  @Test
  void freeSearchWithoutLearningOrdersTheNodes() throws IOException {
    String out = run("off");
    assertTrue(out.contains("----------"), out);
    // on the permutation alone no decision fails
    assertEquals(0, failures(out), out);
  }

  @Test
  void lcgFreeSearchOrdersTheNodes() throws IOException {
    String out = run("on");
    assertTrue(out.contains("----------"), out);
    assertEquals(0, failures(out), out);
  }

  private static long failures(String out) {
    Matcher m = FAILURES.matcher(out);
    assertTrue(m.find(), out);
    return Long.parseLong(m.group(1));
  }

  private String run(String lcg) throws IOException {
    Path fzn = tmp.resolve("feedback.fzn");
    Files.writeString(fzn, feedback(), StandardCharsets.UTF_8);
    String[] args = {"-f", "--lcg", lcg, "-s", "-t", "10000", fzn.toString()};
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
