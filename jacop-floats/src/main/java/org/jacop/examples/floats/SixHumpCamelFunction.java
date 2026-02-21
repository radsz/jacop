/*
 * SixHumpCamelFunction.java
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

import java.util.HashSet;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.floats.constraints.Derivative;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.Optimize;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.DepthFirstSearch;

/** Example for six-hump camel function using float constraints. */
public class SixHumpCamelFunction {

  final double minFloat = -1e+20;
  final double maxFloat = 1e+20;

  /**
   * It executes the program.
   *
   * @param args no arguments
   */
  static void main(String[] args) {

    SixHumpCamelFunction example = new SixHumpCamelFunction();

    example.sixHumpCamelFunction();
  }

  void sixHumpCamelFunction() {

    long t1;
    t1 = System.currentTimeMillis();

    IO.println("========= Six Hump Camel Function =========");

    Store store = new Store();

    FloatDomain.setPrecision(1.0e-5);
    FloatDomain.intervalPrint(false);

    FloatVar x1 = new FloatVar(store, "x1", -2.5, 2.5);
    FloatVar x2 = new FloatVar(store, "x2", -2.5, 2.5);

    FloatVar x1x1 = new FloatVar(store, "x1x1", minFloat, maxFloat);
    Constraint c0 = new PmulQeqR(x1, x1, x1x1);
    store.impose(c0);

    FloatVar x2x2 = new FloatVar(store, "x2x2", minFloat, maxFloat);
    Constraint c1 = new PmulQeqR(x2, x2, x2x2);
    store.impose(c1);

    FloatVar x1x2 = new FloatVar(store, "x1x2", minFloat, maxFloat);
    store.impose(new PmulQeqR(x1, x2, x1x2));

    FloatVar x1x1x1x1 = new FloatVar(store, "x1x1x1x1", minFloat, maxFloat);
    Constraint c2 = new PmulQeqR(x1x1, x1x1, x1x1x1x1);
    store.impose(c2);

    FloatVar x2x2x2x2 = new FloatVar(store, "x2x2x2x2", minFloat, maxFloat);
    Constraint c3 = new PmulQeqR(x2x2, x2x2, x2x2x2x2);
    store.impose(c3);

    FloatVar x1x1x1x1x1x1 = new FloatVar(store, "x1x1x1x1x1x1", minFloat, maxFloat);
    store.impose(new PmulQeqR(x1x1, x1x1x1x1, x1x1x1x1x1x1));

    FloatVar f = new FloatVar(store, "f", minFloat, maxFloat);
    store.impose(
        new LinearFloat(
            new FloatVar[] {f, x1x1, x1x1x1x1, x1x1x1x1x1x1, x1x2, x2x2, x2x2x2x2},
            new double[] {-1.0, 4.0, -2.1, (1.0 / 3.0), 1.0, -4.0, 4.0},
            "==",
            0.0));

    // with first derivative it computes minimum value
    // in 2.735s instead of 382s :)
    Set<FloatVar> vars = new HashSet<>();
    vars.add(x1);
    vars.add(x2);
    Derivative.init(store);

    IO.println("================== fx1 =================");
    FloatVar fx1 = Derivative.getDerivative(store, f, vars, x1);

    IO.println("================== fx2 =================");
    FloatVar fx2 = Derivative.getDerivative(store, f, vars, x2);
    store.impose(new PeqC(fx1, 0.0));
    store.impose(new PeqC(fx2, 0.0));

    IO.println(
        "Var store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());

    DepthFirstSearch<FloatVar> label = new DepthFirstSearch<>();
    SplitSelectFloat<FloatVar> s =
        new SplitSelectFloat<>(
            store, new FloatVar[] {x1, x2}, null); // new LargestDomainFloat<FloatVar>());

    Optimize<FloatVar> min = new Optimize<>(store, label, s, f);
    boolean result = min.minimize();

    if (!result) {
      IO.println("NO SOLUTION");
    }

    IO.println("\nPrecision = " + FloatDomain.precision());

    long t2 = System.currentTimeMillis();
    long t = t2 - t1;

    IO.println("\n\t*** Execution time = " + t + " ms");
  }
}
