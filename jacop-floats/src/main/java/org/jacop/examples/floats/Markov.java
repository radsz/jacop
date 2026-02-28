/*
 * Markov.java
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
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.DepthFirstSearch;

/** Example for Markov chains using float constraints. */
@Slf4j
public class Markov {

  /**
   * It executes the program.
   *
   * @param args no arguments
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    Markov example = new Markov();

    example.markovChainsTaha();
  }

  void markovChainsTaha() {

    long t1;
    t1 = System.currentTimeMillis();

    log.info("========= markovChainsTaha =========");

    Store store = new Store();

    FloatDomain.setPrecision(1.0e-13);
    FloatDomain.intervalPrint(false);

    FloatVar[] meanFirstReturnTime = new FloatVar[3];
    for (int i = 0; i < 3; i++) {
      meanFirstReturnTime[i] = new FloatVar(store, "mean_first_return_time[" + i + "]", 0.0, 1.0);
    }

    FloatVar[] p = new FloatVar[3];
    for (int i = 0; i < 3; i++) {
      p[i] = new FloatVar(store, "p[" + i + "]", 0.0, 1.0);
    }

    FloatVar totalCost = new FloatVar(store, "tot_cost", 0.0, 385.0);

    store.impose(
        new LinearFloat(
            new FloatVar[] {p[2], p[0], p[1], p[2]},
            new double[] {-1.0, 0.1, 0.3, 0.55},
            "==",
            0.0));
    store.impose(
        new LinearFloat(
            new FloatVar[] {p[0], p[0], p[1], p[2]},
            new double[] {-1.0, 0.3, 0.1, 0.05},
            "==",
            0.0));
    store.impose(
        new LinearFloat(
            new FloatVar[] {p[1], p[0], p[1], p[2]},
            new double[] {-1.0, 0.6, 0.6, 0.4},
            "==",
            0.0));
    FloatVar one = new FloatVar(store, "1", 1.0, 1.0);
    store.impose(
        new LinearFloat(
            new FloatVar[] {one, p[0], p[1], p[2]}, new double[] {-1.0, 1.0, 1.0, 1.0}, "==", 0.0));
    store.impose(
        new LinearFloat(
            new FloatVar[] {totalCost, p[0], p[1], p[2]},
            new double[] {-1.0, 100.0, 125.0, 160.0},
            "==",
            0.0));

    FloatVar[] vars = new FloatVar[7];
    System.arraycopy(p, 0, vars, 0, 3);
    System.arraycopy(meanFirstReturnTime, 0, vars, 3, 3);
    vars[6] = totalCost;

    log.info(
        "\bVar store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());

    DepthFirstSearch<FloatVar> label = new DepthFirstSearch<>();
    SplitSelectFloat<FloatVar> s =
        new SplitSelectFloat<>(store, vars, null); // new SmallestDomainFloat<FloatVar>());
    label.setAssignSolution(true);
    label.getSolutionListener().recordSolutions(true);

    boolean result = label.labeling(store, s, totalCost);

    if (result) {
      log.info(totalCost.toString());
    } else {
      log.info("NO SOLUTION");
    }

    log.info("\nPrecision = " + FloatDomain.precision());

    long t2 = System.currentTimeMillis();
    long t = t2 - t1;

    log.info("\n\t*** Execution time = " + t + " ms");
  }
}
