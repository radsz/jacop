/*
 * Fir16.java
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

package org.jacop.examples.fd.filters;

/**
 * Fir benchmark (16-point Fir filter).
 *
 * <p>Source: Kaijie Wu and Ramesh Karri, "Algorithm-Level Recomputing with Shifted Operands -- A
 * Register Transfer Level Concurrent Error Detection Technique" IEEE Trans. on CAD, vol. 25, no. 3,
 * March 2006.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Fir16 extends Filter {

  /** It constructs a simple Fir16 filter. */
  public Fir16() {
    this(1, 2);
  }

  /**
   * It constructs a Fir16 filter with the specified delay for the addition and multiplication
   * operation.
   *
   * @param addDel the delay of the addition operation.
   * @param mulDel the delay of the multiplication operation.
   */
  public Fir16(int addDel, int mulDel) {
    this.addDel = addDel;
    this.mulDel = mulDel;

    name = "Fir16";

    this.dependencies =
        new int[][] {
          {0, 17}, {1, 17}, {2, 18}, {3, 19}, {4, 20}, {5, 21}, {6, 22}, {7, 23}, {8, 24}, {9, 25},
          {10, 26}, {11, 27}, {12, 28}, {13, 29}, {14, 30}, {15, 31}, {16, 32}, {17, 18}, {18, 19},
          {19, 20}, {20, 21}, {21, 22}, {22, 23}, {23, 24}, {24, 25}, {25, 26}, {26, 27}, {27, 28},
          {28, 29}, {29, 30}, {30, 31}, {31, 32}
        };

    this.ids =
        new int[] {
          mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId,
          mulId, mulId, mulId, mulId, addId, addId, addId, addId, addId, addId, addId, addId, addId,
          addId, addId, addId, addId, addId, addId, addId
        };

    this.last = new int[] {32};
  }
}
