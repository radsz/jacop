/*
 * Dfq.java
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
 * It specifies Dfq filter benchmark.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Dfq extends Filter {

  /**
   * It creates a standard Dfq filter problem with addition delay equal 1 and multiplication delay
   * equal 2.
   */
  public Dfq() {
    this(1, 2);
  }

  /**
   * It creates Dfq filter problem with specified delays.
   *
   * @param addDel addition delay.
   * @param mulDel multiplication delay.
   */
  public Dfq(int addDel, int mulDel) {

    this.addDel = addDel;
    this.mulDel = mulDel;

    name = "Dfq";

    this.dependencies =
        new int[][] {{0, 5}, {1, 5}, {2, 6}, {3, 7}, {4, 8}, {5, 9}, {6, 10}, {9, 10}};

    this.ids =
        new int[] {
          MUL_ID, MUL_ID, MUL_ID, MUL_ID, ADD_ID, MUL_ID, MUL_ID, ADD_ID, ADD_ID, ADD_ID, ADD_ID
        };

    this.last = new int[] {7, 8, 10};
  }
}
