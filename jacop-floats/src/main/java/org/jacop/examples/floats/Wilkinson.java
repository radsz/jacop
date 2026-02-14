/*
 * Wilkinson.java
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

import org.jacop.core.Store;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SmallestDomainFloat;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;

/** Example for Wilkinson polynomial using float constraints. */
public class Wilkinson {

  final double minFloat = -1e+150;
  final double maxFloat = 1e+150;

  /**
   * It executes the program.
   *
   * @param args no arguments
   */
  static void main(String[] args) {

    Wilkinson example = new Wilkinson();

    example.wilkinson();
  }

  void wilkinson() {

    long T1;
    T1 = System.currentTimeMillis();

    IO.println("========= wilkinson =========");

    Store store = new Store();

    FloatDomain.setPrecision(1e-13);
    FloatDomain.intervalPrint(false);

    FloatVar x = new FloatVar(store, "x", -100.0, 10.0);

    // 0.0 =
    // (x+1.0)*(x+2.0)*(x+3.0)*(x+4.0)*(x+5.0)*(x+6.0)*(x+7.0)*(x+8.0)*(x+9.0)*(x+10.0)*
    // (x+11.0)*(x+12.0)*(x+13.0)*(x+14.0)*(x+15.0)*(x+16.0)*(x+17.0)*(x+18.0)*(x+19.0)*(x+20.0)
    // +
    // 0.00000011920928955078*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x

    FloatVar[] temp = new FloatVar[20];
    for (int i = 0; i < 20; i++) {
      temp[i] = new FloatVar(store, "temp[" + i + "]", minFloat, maxFloat);
      FloatVar c = new FloatVar(store, (double) i + 1, (double) i + 1);
      store.impose(new PplusQeqR(x, c, temp[i]));
    }

    FloatVar t1 = x;
    for (int i = 0; i < 18; i++) {
      FloatVar t2 = new FloatVar(store, minFloat, maxFloat);
      store.impose(new PmulQeqR(x, t1, t2));
      t1 = t2;
    }

    FloatVar s1 = temp[0];
    for (int i = 1; i < 20; i++) {
      FloatVar s2 = new FloatVar(store, minFloat, maxFloat);
      store.impose(new PmulQeqR(s1, temp[i], s2));
      s1 = s2;
    }

    store.impose(
        new LinearFloat(
            new FloatVar[] {s1, t1}, new double[] {1.0, 0.00000011920928955078}, "==", 0.0));

    IO.println(
        "\bFloatVar store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());

    DepthFirstSearch<FloatVar> label = new DepthFirstSearch<>();
    SplitSelectFloat<FloatVar> s =
        new SplitSelectFloat<>(store, new FloatVar[] {x}, new SmallestDomainFloat<>());
    label.setAssignSolution(true);
    // s.leftFirst = false;

    label.setSolutionListener(new PrintOutListener<>());

    label.labeling(store, s, x);

    IO.println(x);

    IO.println("\nPrecision = " + FloatDomain.precision());

    long T2 = System.currentTimeMillis();
    long T = T2 - T1;

    IO.println("\n\t*** Execution time = " + T + " ms");
  }
}
