/*
 * Ewf.java
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
 * It specifies Ewf benchmark.
 *
 * <p>Source:
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 * @see "Michel, P. and Lauther U. and Duzy, P., The Synthesis Approach to Digital System Design,
 *     Kluwer Academic Publisher, 1992"
 */
public class Ewf extends Filter {

  /** It constructs a simple Ewf filter. */
  public Ewf() {
    this(1, 2);
  }

  /**
   * It constructs a Ewf filter with the specified delay for the addition and multiplication
   * operation.
   *
   * @param addDel the delay of the addition operation.
   * @param mulDel the delay of the multiplication operation.
   */
  public Ewf(int addDel, int mulDel) {

    this.addDel = addDel;
    this.mulDel = mulDel;

    name = "Ewf";

    this.dependencies =
        new int[][] {
          {0, 2}, {0, 15}, {0, 17}, {1, 4}, {1, 8}, {1, 11}, {2, 3}, {2, 7}, {2, 9}, {3, 4}, {4, 5},
          {4, 6}, {4, 10}, {5, 7}, {6, 8}, {7, 9}, {7, 10}, {8, 11}, {8, 13}, {8, 19}, {9, 12},
          {10, 13}, {11, 14}, {12, 15}, {14, 16}, {15, 17}, {15, 18}, {15, 29}, {16, 20}, {16, 28},
          {16, 19}, {17, 21}, {18, 22}, {19, 23}, {20, 24}, {21, 27}, {22, 25}, {22, 32}, {23, 26},
          {23, 33}, {16, 28}, {24, 28}, {25, 30}, {26, 31}, {27, 29}, {30, 32}, {31, 33}
        };

    this.ids =
        new int[] {
          ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, MUL_ID, MUL_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID,
              ADD_ID, MUL_ID,
          ADD_ID, MUL_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, MUL_ID, ADD_ID, ADD_ID,
              MUL_ID, MUL_ID,
          MUL_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID
        };

    this.last = new int[] {13, 24, 28, 29, 30, 31, 32, 33};
  }
}
