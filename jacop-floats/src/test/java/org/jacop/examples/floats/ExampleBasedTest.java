/*
 * ExampleBasedTest.java
 * This file is part of JaCoP.
 *
 * JaCoP is a Java Constraint Programming solver.
 *
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.examples.floats;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

public class ExampleBasedTest {

  private static final int TIMEOUT_MS = 15_000;

  @Test
  @Timeout(TIMEOUT_MS)
  public void testWilkinson() {
    Wilkinson example = new Wilkinson();

    assertDoesNotThrow(() -> example.wilkinson());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testRosenbrock() {
    Rosenbrock example = new Rosenbrock();

    assertDoesNotThrow(() -> example.rosenbrock());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testMinCostFlow() {
    MinCostFlow example = new MinCostFlow();

    assertDoesNotThrow(() -> example.minCostFlow());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testCircleIntersection() {
    CircleIntersection example = new CircleIntersection();

    assertDoesNotThrow(() -> example.circleIntersection());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testCyclohexane() {
    Cyclohexane example = new Cyclohexane();

    assertDoesNotThrow(() -> example.cyclohexane());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testSixHumpCamelFunction() {
    SixHumpCamelFunction example = new SixHumpCamelFunction();

    assertDoesNotThrow(() -> example.sixHumpCamelFunction());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testCurveFitting() {
    CurveFitting example = new CurveFitting();

    assertDoesNotThrow(() -> example.curveFitting3());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testTinyTSP() {
    TinyTsp example = new TinyTsp();

    assertDoesNotThrow(() -> example.tinyTsp());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testSinCosExample() {
    SinCosExample example = new SinCosExample();

    assertDoesNotThrow(() -> example.model());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testTanExample() {
    TanExample example = new TanExample();

    assertDoesNotThrow(() -> example.model());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testLaplace() {
    Laplace example = new Laplace();

    assertDoesNotThrow(() -> example.laplace());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testMarkov() {
    Markov example = new Markov();

    assertDoesNotThrow(() -> example.markovChainsTaha());
  }

  @Test
  @Timeout(TIMEOUT_MS)
  public void testLoan() {
    Loan example = new Loan();

    double i = Double.parseDouble("0.04");
    double p = Double.parseDouble("1000.0");
    double r = Double.parseDouble("260.0");
    double b4 = Double.parseDouble("65.78");

    assertDoesNotThrow(() -> example.loan(i, p, r, b4));
  }
}
