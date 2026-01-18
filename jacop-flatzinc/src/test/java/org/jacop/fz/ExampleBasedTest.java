/*
 * ExampleBasedTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz;

import java.nio.file.Path;
import org.junit.Test;

public class ExampleBasedTest {

  private static final int TIMEOUT_MS = 15_000;
  private static final int TIMEOUT_LONG_MS = 60_000;

  private static void runFzn(String relativePathFromModuleRoot) {
    String fzn = Path.of(relativePathFromModuleRoot).toString();
    new Fz2jacop().callMain(new String[] {"-n", "1", "-t", String.valueOf(TIMEOUT_MS), fzn});
  }

  @Test(timeout = TIMEOUT_MS)
  public void testConcert() {
    runFzn("src/main/java/org/jacop/fz/examples/concert.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testCurveFitting2() {
    runFzn("src/main/java/org/jacop/fz/examples/curve_fitting2.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testFilter() {
    runFzn("src/main/java/org/jacop/fz/examples/filter.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testGardnerDinner() {
    runFzn("src/main/java/org/jacop/fz/examples/gardner_dinner.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testJobshop() {
    runFzn("src/main/java/org/jacop/fz/examples/jobshop.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testRostering() {
    runFzn("src/main/java/org/jacop/fz/examples/rostering.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testTinyTsp() {
    runFzn("src/main/java/org/jacop/fz/examples/tiny_tsp.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testWilkinson() {
    runFzn("src/main/java/org/jacop/fz/examples/wilkinson.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincAr() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/ar.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincAssignment() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/assignment.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincBinpack() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/binpack.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincDct() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/dct.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincDfq() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/dfq.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincEwf() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/ewf.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincFir() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/fir.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincFir16() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/fir16.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincParcel() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/parcel.fzn");
  }

  @Test(timeout = TIMEOUT_LONG_MS)
  public void testMinizincPerfectSquare() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/perfect_square.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincTransistors() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/transistors.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincTransportation() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/transportation.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincTsp() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/tsp.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincTsp1() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/tsp1.fzn");
  }

  @Test(timeout = TIMEOUT_MS)
  public void testMinizincTsp2() {
    runFzn("src/main/java/org/jacop/fz/examples/minizinc/tsp2.fzn");
  }
}
