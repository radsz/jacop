/*
 * Ar.java
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
 * It specifies Ar benchmark.
 *
 * <p>Source:
 *
 * <p>Rajiv Jain, Alice C. Parker "Experience with the ADAM Synthesis System" 26th ACM/IEEE Design
 * Automation Conference, 1989. and Rajiv Jain, Alice C. Parker, Nohbyung Park, "Predicting
 * Sysem-Level Area and Dealy for Pipelined and Nonpipelined Designs" IEEE Trans. on CAD, vol. 11,
 * no. 8, August 1992.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Ar extends Filter {

  /** It creates a default Ar filter with defaul delays for the operations. */
  public Ar() {
    this(1, 2);
  }

  /**
   * It possible to specify the delay of the addition and multiplication.
   *
   * @param addDel the delay of the addition operation.
   * @param mulDel the delay of the multiplication operation.
   */
  public Ar(int addDel, int mulDel) {

    this.addDel = addDel;
    this.mulDel = mulDel;
    name = "Ar";

    this.dependencies =
        new int[][] {
          {0, 8}, {1, 8}, {2, 9}, {3, 9}, {4, 10}, {5, 10}, {6, 11}, {7, 11}, {8, 26}, {9, 27},
          {10, 12}, {11, 13}, {12, 15}, {12, 16}, {13, 14}, {13, 17}, {14, 18}, {15, 18}, {16, 19},
          {17, 19}, {18, 21}, {18, 22}, {19, 20}, {19, 23}, {20, 24}, {21, 24}, {22, 25}, {23, 25},
          {24, 26}, {25, 27}
        };

    this.ids =
        new int[] {
          MUL_ID, MUL_ID, MUL_ID, MUL_ID, MUL_ID, MUL_ID, MUL_ID, MUL_ID, ADD_ID, ADD_ID, ADD_ID,
              ADD_ID, ADD_ID,
          ADD_ID, MUL_ID, MUL_ID, MUL_ID, MUL_ID, ADD_ID, ADD_ID, MUL_ID, MUL_ID, MUL_ID, MUL_ID,
              ADD_ID, ADD_ID,
          ADD_ID, ADD_ID
        };

    this.last = new int[] {12, 13, 26, 27};
  }
}
