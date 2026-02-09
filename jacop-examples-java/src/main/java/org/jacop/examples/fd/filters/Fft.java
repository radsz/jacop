/*
 * Fft.java
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
 * It specifies Fft benchmark.
 *
 * <p>Source: Naotaka Ohsawa, Masanori Hariyama and Michitaka Kameyama "High-Performance Field
 * Programmable VLSI Processor Based on a Direct Allocation of a Control/Data Flow Graph" IEEE
 * Computer Society Annual Symposium on VLSI p. 0095
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Fft extends Filter {

  /** It constructs a simple Fft filter. */
  public Fft() {
    this(1, 2);
  }

  /**
   * It constructs a Fft filter with the specified delay for the addition and multiplication
   * operation.
   *
   * @param addDel the delay of the addition operation.
   * @param mulDel the delay of the multiplication operation.
   */
  public Fft(int addDel, int mulDel) {

    this.addDel = addDel;
    this.mulDel = mulDel;

    name = "Fft";

    this.dependencies =
        new int[][] {{0, 4}, {1, 4}, {2, 5}, {3, 5}, {4, 6}, {4, 7}, {5, 8}, {5, 9}};

    this.ids = new int[] {mulId, mulId, mulId, mulId, addId, addId, addId, addId, addId, addId};

    this.last = new int[] {6, 7, 8, 9};
  }
}
