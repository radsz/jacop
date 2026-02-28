/*
 * CurveFitting.java
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

import java.util.Arrays;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.Store;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;

/** Example for curve fitting using float constraints. */
@Slf4j
public class CurveFitting {

  final double minFloat = -1e+150;
  final double maxFloat = 1e+150;

  /**
   * It executes the program.
   *
   * @param args no arguments
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    CurveFitting example = new CurveFitting();

    example.curveFitting3();
  }

  void curveFitting3() {

    log.info("========= curveFitting3 =========");

    Store store = new Store();

    FloatDomain.setPrecision(1e-14);

    int n = 19;

    FloatVar[] ex = new FloatVar[n];
    FloatVar[] ey = new FloatVar[n];
    for (int i = 0; i < n; i++) {
      ex[i] = new FloatVar(store, "Ex[" + i + "]", minFloat, maxFloat);
      ey[i] = new FloatVar(store, "Ey[" + i + "]", minFloat, maxFloat);
    }

    FloatVar sumExEx = new FloatVar(store, "sumExEx", minFloat, maxFloat);

    FloatVar[] exEx = new FloatVar[n + 1];
    FloatVar[] exEy = new FloatVar[n + 1];
    double[] w = new double[n + 1];
    for (int i = 0; i < n; i++) {
      exEx[i] = new FloatVar(store, "ExEx[" + i + "]", minFloat, maxFloat);
      store.impose(new PmulQeqR(ex[i], ex[i], exEx[i]));

      exEy[i] = new FloatVar(store, "ExEy[" + i + "]", minFloat, maxFloat);
      store.impose(new PmulQeqR(ex[i], ey[i], exEy[i]));

      w[i] = 1.0;
    }
    w[n] = -1.0;
    exEx[n] = sumExEx;

    store.impose(new LinearFloat(exEx, w, "==", 0.0));

    FloatVar[] div = new FloatVar[n + 1];
    for (int i = 0; i < n; i++) {
      div[i] = new FloatVar(store, "div[" + i + "]", minFloat, maxFloat);
      store.impose(new PmulQeqR(sumExEx, div[i], exEy[i]));
    }
    FloatVar b1 = new FloatVar(store, "b1", minFloat, maxFloat);
    div[n] = b1;

    double[] ones1 = new double[n + 1];
    for (int i = 0; i < n; i++) {
      ones1[i] = 1.0;
    }
    ones1[n] = -1.0;
    store.impose(new LinearFloat(div, ones1, "==", 0.0));

    double[] ones = new double[n];
    Arrays.fill(ones, 1.0);
    store.impose(new LinearFloat(ex, ones, "==", 0.0));
    store.impose(new LinearFloat(ey, ones, "==", 0.0));

    double[] sx = {
      0.0, 0.5, 1.0, 1.5, 1.9, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 5.5, 6.0, 6.6, 7.0, 7.6, 8.5, 9.0, 10.0
    };
    double[] sy = {
      1.0, 0.9, 0.7, 1.5, 2.0, 2.4, 3.2, 2.0, 2.7, 3.5, 1.0, 4.0, 3.6, 2.7, 5.7, 4.6, 6.0, 6.8, 7.3
    };
    FloatVar x = new FloatVar(store, "X", minFloat, maxFloat); // -10, 10);
    FloatVar y = new FloatVar(store, "Y", minFloat, maxFloat); // -10, 10);
    for (int i = 0; i < n; i++) {
      store.impose(new PplusQeqR(x, ex[i], new FloatVar(store, sx[i], sx[i])));
      store.impose(new PplusQeqR(y, ey[i], new FloatVar(store, sy[i], sy[i])));
    }

    FloatVar[] vars = new FloatVar[2 * n + 1];
    System.arraycopy(ex, 0, vars, 0, n);
    System.arraycopy(ey, 0, vars, n, 2 * n - n);
    vars[2 * n] = b1;

    log.info(
        "\bFloatVar store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());

    // solve minimize cost;
    DepthFirstSearch<FloatVar> label = new DepthFirstSearch<>();
    SplitSelectFloat<FloatVar> s =
        new SplitSelectFloat<>(store, vars, null); // new SmallestDomainFloat<FloatVar>());
    label.setAssignSolution(true);
    // s.leftFirst = false;

    label.setSolutionListener(new PrintOutListener<>());

    label.labeling(store, s);

    log.info(x + "\n" + y + "\n" + b1);

    log.info("\nPrecision = " + FloatDomain.precision());
  }
}
