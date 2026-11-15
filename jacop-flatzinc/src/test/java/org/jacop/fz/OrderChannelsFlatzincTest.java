/*
 * OrderChannelsFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
 * Checks the order channels of the FlatZinc front end (flag org.jacop.fz.orderChannels): the
 * reified comparisons of one variable with constants become one ChannelOrder, and the solutions and
 * the optimum stay the same with the default search, all-solutions search, LCG and free search. The
 * items cover the four comparisons, constants on either side, one Boolean for two items,
 * half-reifications (int_le_imp, int_lt_imp) as implied items, and a variable with a single
 * reification, which stays a reification.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class OrderChannelsFlatzincTest {

  @TempDir Path tmp;

  private static final String MODEL =
      """
      var 1..6: x:: output_var;
      var 0..5: y:: output_var;
      var bool: a:: output_var;
      var bool: b:: output_var;
      var bool: c:: output_var;
      var bool: d:: output_var;
      var bool: e:: output_var;
      var bool: f:: output_var;
      var bool: g:: output_var;
      var bool: h:: output_var;
      var 0..20: cost:: output_var;
      constraint int_le_reif(x,2,a);
      constraint int_lt_reif(x,5,b);
      constraint int_le_reif(4,x,c);
      constraint int_lt_reif(3,x,c);
      constraint int_le_reif(x,3,d);
      constraint int_le_reif(y,1,e);
      constraint int_lt_reif(y,3,f);
      constraint int_le_reif(x,y,e);
      constraint int_le_imp(x,4,g);
      constraint int_lt_imp(2,x,h);
      constraint bool_clause([g,h],[]);
      constraint bool_clause([a,c,f],[b]);
      constraint int_lin_eq([2,1,-1],[x,y,cost],-3);
      """;

  @Test
  void channelsKeepTheSolutions() throws IOException {
    String satisfy = MODEL + "solve satisfy;\n";
    Set<String> reference = solutions(run(false, satisfy, "-a"));
    assertTrue(reference.size() > 1, reference.toString());
    String channelled = run(true, satisfy, "-a", "-debug");
    assertTrue(channelled.contains("ChannelOrder(x"), channelled);
    assertTrue(channelled.contains("ChannelOrder(y"), channelled);
    assertEquals(reference, solutions(channelled));
    assertEquals(reference, solutions(run(true, satisfy, "-a", "--lcg")));
  }

  @Test
  void channelsKeepTheOptimum() throws IOException {
    String minimize = MODEL + "solve maximize cost;\n";
    String reference = optimum(run(false, minimize));
    assertFalse(reference.isEmpty());
    assertEquals(reference, optimum(run(true, minimize)));
    assertEquals(reference, optimum(run(true, minimize, "--lcg")));
    assertEquals(reference, optimum(run(true, minimize, "-f")));
  }

  private static String optimum(String out) {
    String[] parts = out.split("----------");
    assertTrue(out.contains("=========="), out);
    return Arrays.stream(parts[parts.length - 2].strip().split("\\R"))
        .filter(l -> l.startsWith("cost"))
        .findFirst()
        .orElse("");
  }

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    new TreeSet<>(
                        Arrays.stream(s.strip().split("\\R"))
                            .filter(l -> !l.isBlank() && !l.startsWith("%"))
                            .toList())))
        .filter(s -> !s.isEmpty() && !s.startsWith("====="))
        .forEach(solutions::add);
    return solutions;
  }

  private String run(boolean channels, String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty("org.jacop.fz.orderChannels", Boolean.toString(channels));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty("org.jacop.fz.orderChannels");
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
