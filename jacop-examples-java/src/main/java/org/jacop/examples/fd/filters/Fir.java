/*
 * Fir.java
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
 * <p>Source: Ramesh Karri, Karin Hogstedt and Alex Orailoglu "Computer-Aided Design of
 * Fault-Tolerant VLSI Design Systems" IEEE Design {@literal &} Test, Fall 1996 (Vol. 13, No. 3),
 * pp. 88-96
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Fir extends Filter {

  /** It constructs a simple Fir filter. */
  public Fir() {
    this(1, 2);
  }

  /**
   * It constructs a Fir filter with the specified delay for the addition and multiplication
   * operation.
   *
   * @param addDel the delay of the addition operation.
   * @param mulDel the delay of the multiplication operation.
   */
  public Fir(int addDel, int mulDel) {
    this.addDel = addDel;
    this.mulDel = mulDel;

    name = "Fir";

    this.dependencies =
        new int[][] {
          {0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 7}, {7, 8}, {9, 10}, {10, 2},
          {11, 12}, {12, 3}, {13, 14}, {14, 4}, {15, 16}, {16, 5}, {17, 18}, {18, 6}, {19, 20},
          {20, 7}, {21, 22}, {22, 8}
        };

    this.ids =
        new int[] {
          ADD_ID, MUL_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, MUL_ID,
          ADD_ID, MUL_ID, ADD_ID, MUL_ID, ADD_ID, MUL_ID, ADD_ID, MUL_ID, ADD_ID, MUL_ID, ADD_ID,
          MUL_ID
        };

    this.last = new int[] {8};
  }
}
