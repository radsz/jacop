/*
 * StatisticsOptionFlatzincTest.java
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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * -s prints the standard FlatZinc statistics only; --search-statistics, or -s with -debug, adds the
 * statistics of JaCoP's own components.
 */
@Timeout(60)
class StatisticsOptionFlatzincTest {

  private static final String MODEL =
      """
      var 0..1: x0 :: output_var;
      var 0..1: x1 :: output_var;
      var 0..1: x2 :: output_var;
      var 0..1: x3 :: output_var;
      var 0..20: obj :: output_var;
      constraint int_lin_le([3,4,5,6],[x0,x1,x2,x3],10);
      constraint int_lin_eq([4,5,6,7,-1],[x0,x1,x2,x3,obj],0);
      solve maximize obj;
      """;

  private static final Pattern EXTRA =
      Pattern.compile("%%%mzn-stat: (lcg|presolve|lp|lns|ls|symmetry|probe|portfolio)[A-Z]");

  @TempDir Path tmp;

  @Test
  void statisticsAreStandardOnly() throws IOException {
    String out = solve("--lcg", "-s");
    assertTrue(out.contains("%%%mzn-stat: peakDepth="), out);
    assertTrue(out.contains("%%%mzn-stat: peakMem="), out);
    assertFalse(EXTRA.matcher(out).find(), out);
    assertFalse(out.contains("%% lcg "), out);
  }

  @Test
  void searchStatisticsAddJacopsOwn() throws IOException {
    String out = solve("--lcg", "--search-statistics");
    assertTrue(out.contains("%%%mzn-stat: peakDepth="), out);
    assertTrue(out.contains("%%%mzn-stat: lcgRestarts="), out);
  }

  @Test
  void debugWithStatisticsAddsJacopsOwn() throws IOException {
    String out = solve("--lcg", "-s", "-debug");
    assertTrue(out.contains("%%%mzn-stat: lcgRestarts="), out);
  }

  private String solve(String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, MODEL, StandardCharsets.UTF_8);
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
