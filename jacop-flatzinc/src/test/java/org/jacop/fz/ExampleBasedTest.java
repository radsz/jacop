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

import java.nio.file.Path;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

class ExampleBasedTest {

  private static final int TIMEOUT_MS = 15_000;
  private static final int TIMEOUT_LONG_MS = 60_000;

  private static void runFzn(String relativePathFromModuleRoot) {
    String fzn = Path.of(relativePathFromModuleRoot).toString();
    new Fz2jacop().callMain(new String[] {"-n", "1", "-t", String.valueOf(TIMEOUT_MS), fzn});
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
    assertDoesNotThrow(() -> runFzn("src/main/java/org/jacop/fz/examples/gardner_dinner.fzn"));
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
        () -> runFzn("src/main/java/org/jacop/fz/examples/minizinc/perfect_square.fzn"));
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
}
