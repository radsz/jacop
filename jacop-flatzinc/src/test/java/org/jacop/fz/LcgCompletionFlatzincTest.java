/*
 * LcgCompletionFlatzincTest.java
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
 * Under LCG, once the annotation has fixed its variables and every variable left has no constraint
 * that is not entailed, the assignment is taken as a solution when the solver's clauses are all
 * satisfied, as the search without learning stops after its annotation. Before, the activity
 * branching decided the variables left one at a time: on Krzysztof Kuchcinski's a_card_trick_1,
 * 1,014 decisions on 0/1 variables whose constraints had all become clauses, after 29 decisions of
 * the annotation. Here each b_i is in two clauses, b_i or c_i and b_i or b_(i+1) or c_i, where c_i
 * is x_i = 1: indomain_min sets every x_i to 1, which satisfies both clauses without b_i (40
 * decisions; 80 when the b_i were decided after the annotation).
 */
class LcgCompletionFlatzincTest {

  private static final int N = 40;

  @TempDir Path tmp;

  private static String model() {
    StringBuilder m = new StringBuilder();
    for (int i = 0; i < N; i++) {
      m.append("var 1..3: x").append(i).append(":: output_var;\n");
      m.append("var bool: c").append(i).append(":: var_is_introduced :: is_defined_var;\n");
      m.append("var bool: b").append(i).append(";\n");
    }
    for (int i = 0; i < N; i++) {
      m.append("constraint int_eq_reif(x").append(i).append(",1,c").append(i);
      m.append("):: defines_var(c").append(i).append(");\n");
      m.append("constraint bool_clause([b").append(i).append(",c").append(i).append("],[]);\n");
      m.append("constraint bool_clause([b").append(i).append(",b").append((i + 1) % N);
      m.append(",c").append(i).append("],[]);\n");
    }
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < N; i++) {
      xs.append(i == 0 ? "" : ",").append('x').append(i);
    }
    m.append("solve :: int_search([").append(xs).append("], input_order, indomain_min, complete)");
    return m.append(" satisfy;\n").toString();
  }

  @Test
  void annotationCompletesTheModel() throws IOException {
    String out = run("--lcg", "on", "-s", "-v");
    for (int i = 0; i < N; i++) {
      assertTrue(out.contains("x" + i + " = 1;"), "x" + i + " is not 1:\n" + out);
    }
    assertEquals(1, stat(out, "lcgCompletedModels"), out);
    assertTrue(stat(out, "nodes") <= N, "decisions after the annotation:\n" + out);
  }

  @Test
  void searchWithoutLearningAgrees() throws IOException {
    String out = run("--lcg", "off");
    for (int i = 0; i < N; i++) {
      assertTrue(out.contains("x" + i + " = 1;"), "x" + i + " is not 1:\n" + out);
    }
  }

  private static long stat(String out, String name) {
    Matcher m =
        Pattern.compile("^%%%mzn-stat: " + name + "=(\\d+)$", Pattern.MULTILINE).matcher(out);
    long value = -1;
    while (m.find()) {
      value = Long.parseLong(m.group(1)); // the last one: the search's own
    }
    assertTrue(value >= 0, "no " + name + ":\n" + out);
    return value;
  }

  private String run(String... options) throws IOException {
    Path fzn = tmp.resolve("completion.fzn");
    Files.writeString(fzn, model(), StandardCharsets.UTF_8);
    List<String> args = new ArrayList<>(Arrays.asList(options));
    args.add("-t");
    args.add("10000");
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
}
