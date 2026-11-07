/*
 * ClauseValuesFlatzincTest.java
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
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks that a clause of literals b <-> (x = v) or b -> (x = v) on one variable x restricts x to
 * the values of the clause when the model is loaded, and that the solutions stay the same.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class ClauseValuesFlatzincTest {

  @TempDir Path tmp;

  private static final String HEADER =
      """
      var 1..6: x:: output_var;
      var bool: b1;
      var bool: b2;
      var bool: b3;
      var bool: c:: output_var;
      constraint int_eq_reif(x,2,b1);
      constraint int_eq_reif(x,4,b2);
      constraint int_eq_imp(x,5,b3);
      """;

  @Test
  void clauseOfOneVariableRestrictsItsDomain() throws IOException {
    String fzn = HEADER + "constraint bool_clause([b1,b2,b3],[]);\nsolve satisfy;\n";
    String out = run(fzn, "-a", "-debug");
    assertTrue(out.contains("x::{2, 4..5}"), out);
    assertEquals(Set.of("2", "4", "5"), values(out));
  }

  @Test
  void clauseWithAnotherLiteralKeepsTheDomain() throws IOException {
    String fzn = HEADER + "constraint bool_clause([b1,b2,c],[]);\nsolve satisfy;\n";
    String out = run(fzn, "-a", "-debug");
    assertTrue(out.contains("x::{1..6}"), out);
    assertEquals(Set.of("1", "2", "3", "4", "5", "6"), values(out));
  }

  /** The values of x over all solutions. */
  private static Set<String> values(String out) {
    Set<String> values = new TreeSet<>();
    Arrays.stream(out.split("\\R"))
        .filter(l -> l.startsWith("x = "))
        .forEach(l -> values.add(l.substring(4, l.length() - 1)));
    return values;
  }

  private String run(String model, String... options) throws IOException {
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
