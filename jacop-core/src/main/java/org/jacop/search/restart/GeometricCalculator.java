/*
 * GeometricCalculator.java
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

package org.jacop.search.restart;

/**
 * Defines functionality for constant calculator for restart search.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class GeometricCalculator extends Calculator {

  final int scale;
  final double base;
  int n;

  /**
   * Constructs a geometric calculator where the fail limit grows geometrically.
   *
   * @param base the base factor for geometric progression.
   * @param scale the initial scale value for the fail limit.
   */
  public GeometricCalculator(double base, int scale) {
    n = 0;
    failLimit = scale;
    this.base = base;
    this.scale = scale;
  }

  /**
   * Resets the fail counter and calculates a new fail limit using geometric progression. The new
   * limit is calculated as base^n * scale where n is incremented each time.
   */
  public void newLimit() {
    numberFails = 0;
    double p = Math.pow(base, ++n);
    failLimit = (long) p * scale;
  }

  /**
   * Returns a string representation of this geometric calculator.
   *
   * @return a string describing the calculator with its base and scale parameters.
   */
  public String toString() {
    return "geometricCalculator(" + base + ", " + scale + ")";
  }
}
