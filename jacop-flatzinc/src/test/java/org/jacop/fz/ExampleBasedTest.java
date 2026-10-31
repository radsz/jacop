/*
 * ExampleBasedTest.java
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

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

class ExampleBasedTest {

  private static final int TIMEOUT_MS = 15_000;
  private static final int TIMEOUT_LONG_MS = 60_000;

  /** Search on these models only needs to start without an error, not to finish. */
  private static final int SHORT_SEARCH_MS = 1_000;

  private static void runFzn(String relativePathFromModuleRoot) {
    runFzn(relativePathFromModuleRoot, TIMEOUT_MS);
  }

  private static void runFzn(String relativePathFromModuleRoot, int timeOutMs) {
    String fzn = Path.of(relativePathFromModuleRoot).toString();
    new Fz2jacop().callMain(new String[] {"-n", "1", "-t", String.valueOf(timeOutMs), fzn});
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testConcert() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/concert.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testCurveFitting2() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/curve_fitting2.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testFilter() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/filter.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testGardnerDinner() {
    assertDoesNotThrow(
        () -> runFzn("src/main/java/org/jacop/fz/examples/gardner_dinner.fzn", SHORT_SEARCH_MS));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testJobshop() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/jobshop.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testRostering() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/rostering.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testTinyTsp() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/tiny_tsp.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testWilkinson() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/wilkinson.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincAr() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/ar.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincAssignment() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/assignment.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincBinpack() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/binpack.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincDct() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/dct.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincDfq() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/dfq.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincEwf() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/ewf.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincFir() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/fir.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincFir16() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/fir16.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincParcel() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/parcel.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_LONG_MS)
  void testMinizincPerfectSquare() {
    assertDoesNotThrow(
        () ->
            runFzn(
                "src/main/java/org/jacop/fz/examples/minizinc/perfect_square.fzn",
                SHORT_SEARCH_MS));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincTransistors() {
    assertDoesNotThrow(
        () -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/transistors.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincTransportation() {
    assertDoesNotThrow(
        () -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/transportation.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincTsp() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/tsp.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincTsp1() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/tsp1.fzn"));
  }

  @Test
  @Timeout(TIMEOUT_MS)
  void testMinizincTsp2() {
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/tsp2.fzn"));
  }

  /**
   * Regression test for quadratic memory use when deduplicating table tuples (MiniZinc
   * regression/bug284): each tuple row reserved capacity for the whole table, so a large table ran
   * out of memory before search started.
   */
  @Test
  @Timeout(TIMEOUT_LONG_MS)
  void testLargeTableIsPosted(@TempDir Path dir) throws IOException {
    int n = 100_000;
    StringBuilder fzn = new StringBuilder();
    fzn.append("predicate jacop_table_int(array [int] of var int: x,array [int] of int: t);\n");
    fzn.append("var 1..").append(n).append(": a:: output_var;\n");
    fzn.append("var 1..").append(n).append(": b:: output_var;\n");
    fzn.append("array [1..").append(2 * n).append("] of int: t = [");
    for (int i = 1; i <= n; i++) {
      fzn.append(i == 1 ? "" : ",").append(i).append(',').append(n + 1 - i);
    }
    fzn.append("];\n");
    fzn.append("constraint jacop_table_int([a,b],t);\n");
    fzn.append("constraint int_eq(a,7);\n");
    fzn.append("solve satisfy;\n");
    Path file = dir.resolve("large_table.fzn");
    Files.writeString(file, fzn.toString());

    PrintStream originalOut = System.out;
    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    try {
      System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
      runFzn(file.toString());
    } finally {
      System.setOut(originalOut);
    }
    String output = captured.toString(StandardCharsets.UTF_8);
    assertTrue(output.contains("b = " + (n - 6) + ";"), output);
  }
}
