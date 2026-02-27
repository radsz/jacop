/*
 * TanExample.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.examples.floats;

import lombok.extern.slf4j.Slf4j;
import org.jacop.core.Store;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.TanPeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.DepthFirstSearch;

/** Example for tangent using float constraints. */
@Slf4j
public class TanExample {

  /**
   * It executes the program which computes values for tan(x) = -x.
   *
   * @param args no arguments
   */
  static void main(String[] args) {

    TanExample example = new TanExample();

    example.model();
  }

  /**
   * Defines the constraint model for solving the equation tan(x) = -x in the interval -4*pi..4*pi.
   */
  public void model() {

    log.info("\nProgram to solve tan(x) = -x problem in interval -4*pi..4*pi");

    long t1;
    t1 = System.currentTimeMillis();

    Store store = new Store();

    FloatDomain.setPrecision(1.0e-11);
    FloatDomain.intervalPrint(false);

    FloatVar p = new FloatVar(store, "p", -4 * FloatDomain.PI, 4 * FloatDomain.PI);
    FloatVar q = new FloatVar(store, "q", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);

    store.impose(new TanPeqR(p, q));
    store.impose(new PplusQeqR(p, q, new FloatVar(store, 0.0, 0.0)));

    log.info(
        "\bVar store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());

    DepthFirstSearch<FloatVar> label = new DepthFirstSearch<>();
    SplitSelectFloat<FloatVar> s =
        new SplitSelectFloat<>(
            store, new FloatVar[] {p, q}, null); // new SmallestDomainFloat<FloatVar>());
    label.setAssignSolution(true);
    label.getSolutionListener().recordSolutions(true);
    label.getSolutionListener().searchAll(true);
    s.roundRobin = false;
    // s.leftFirst = false;

    boolean result = label.labeling(store, s);

    if (result) {
      label.printAllSolutions();
    } else {
      log.info("NO SOLUTION");
    }

    log.info("\nPrecision = " + FloatDomain.precision());

    long t2 = System.currentTimeMillis();

    log.info("\n\t*** Execution time = " + (t2 - t1) + " ms");
  }
}
