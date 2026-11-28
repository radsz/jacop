/*
 * FixedCompletionFlatzincTest.java
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of the completion of a search annotation under LCG without -f (--free-config
 * fixed-completion): the output variables the annotation leaves open are decided in input order,
 * lower half first, and no solution is lost.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class FixedCompletionFlatzincTest {

  @TempDir Path tmp;

  private static final int N = 5;

  // x and y1..y4 all different in 1..5; the annotation covers x only
  private static String model(String solve) {
    return model("", solve);
  }

  // FlatZinc declares every variable before the constraints
  private static String model(String variables, String rest) {
    StringBuilder s = new StringBuilder("var 1..").append(N).append(": x:: output_var;\n");
    for (int i = 1; i < N; i++) {
      s.append("var 1..").append(N).append(": y").append(i).append(":: output_var;\n");
    }
    s.append(variables);
    for (int i = 0; i < N; i++) {
      for (int j = i + 1; j < N; j++) {
        s.append("constraint int_ne(").append(name(i)).append(',').append(name(j)).append(");\n");
      }
    }
    return s.append(rest).toString();
  }

  private static String name(int i) {
    return i == 0 ? "x" : "y" + i;
  }

  private static final String SATISFY =
      "solve :: int_search([x], input_order, indomain_max, complete) satisfy;\n";

  @Test
  void firstSolutionDecidesOutputVariablesInInputOrder() throws IOException {
    String out = run(model(SATISFY), "fixed-completion=output", false);
    String first = out.substring(0, out.indexOf("----------"));
    assertTrue(first.contains("x = 5;"), out);
    for (int i = 1; i < N; i++) {
      assertTrue(first.contains("y" + i + " = " + i + ";"), out);
    }
  }

  @Test
  void allSolutionsWithEitherCompletion() throws IOException {
    // 5! permutations
    for (String completion : new String[] {"output", "activity"}) {
      String out = run(model(SATISFY), "fixed-completion=" + completion, true);
      assertEquals(120, count(out, "----------"), completion + "\n" + out);
      assertTrue(out.contains("=========="), out);
    }
  }

  @Test
  void optimumWithEitherCompletion() throws IOException {
    // 4 y1 + 3 y2 + 2 y3 + y4 is smallest with y = 1, 2, 3, 4: 20
    String cost = "var 0..100: cost:: output_var:: is_defined_var;\n";
    String solve =
        "constraint int_lin_eq([4,3,2,1,-1],[y1,y2,y3,y4,cost],0):: defines_var(cost);\n"
            + "solve :: int_search([x], input_order, indomain_min, complete) minimize cost;\n";
    for (String completion : new String[] {"output", "activity"}) {
      String out = run(model(cost, solve), "fixed-completion=" + completion, false);
      Matcher m = Pattern.compile("cost = (\\d+);").matcher(out);
      int last = -1;
      while (m.find()) {
        last = Integer.parseInt(m.group(1));
      }
      assertEquals(20, last, completion + "\n" + out);
      assertTrue(out.contains("=========="), out);
    }
  }

  private static int count(String s, String part) {
    int n = 0;
    for (int k = s.indexOf(part); k >= 0; k = s.indexOf(part, k + 1)) {
      n++;
    }
    return n;
  }

  private String run(String model, String config, boolean all) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args =
        all
            ? new String[] {"--lcg", "-a", "-t", "10000", "--free-config", config, fzn.toString()}
            : new String[] {"--lcg", "-t", "10000", "--free-config", config, fzn.toString()};
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
