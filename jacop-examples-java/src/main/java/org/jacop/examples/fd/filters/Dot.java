/*
 * Dot.java
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
 * It specifies Dot benchmark.
 *
 * <p>Source:
 *
 * <p>Raghunathan, A. and Jha, N. K. "An Iterative Improvement Algorithm for Low Power Data Path
 * Synthesis" ICCAD 1995
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Dot extends Filter {

  /** It constructs a simple Dot filter. */
  public Dot() {
    this(1, 2);
  }

  /**
   * It constructs a Dot filter with the specified delay for the addition and multiplication
   * operation.
   *
   * @param addDel the delay of the addition operation.
   * @param mulDel the delay of the multiplication operation.
   */
  public Dot(int addDel, int mulDel) {

    this.addDel = addDel;

    this.mulDel = mulDel;

    name = "Dot";

    this.dependencies =
        new int[][] {
          {0, 6}, {1, 6}, {2, 7}, {3, 7}, {4, 8}, {5, 8}, {6, 9}, {7, 9}, {9, 10}, {8, 10}
        };

    this.ids =
        new int[] {mulId, mulId, mulId, mulId, mulId, mulId, addId, addId, addId, addId, addId};

    this.last = new int[] {10};
  }
}
