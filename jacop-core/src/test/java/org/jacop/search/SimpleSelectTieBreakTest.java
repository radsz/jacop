/*
 * SimpleSelectTieBreakTest.java
 * <p>
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

package org.jacop.search;

import static org.junit.jupiter.api.Assertions.assertSame;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks that input order tie-breaking follows the order the variables were given in, after the
 * selector has moved variables around in its search array.
 */
class SimpleSelectTieBreakTest {

  @Test
  void tieGoesToEarliestInputVariableAfterSwaps() {
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 4);
    }
    SimpleSelect<IntVar> select =
        new SimpleSelect<>(x, new SmallestDomain<>(), new IndomainMin<>());

    // the search array is now x3, x1, x2, x0; every domain has the same size
    select.placeSearchVariable(0, 3);

    assertSame(x[0], select.getChoiceVariable(0));
    assertSame(x[1], select.getChoiceVariable(1));
  }

  @Test
  void smallerDomainWinsOverInputOrder() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, i == 2 ? 2 : 4);
    }
    SimpleSelect<IntVar> select =
        new SimpleSelect<>(x, new SmallestDomain<>(), new IndomainMin<>());

    assertSame(x[2], select.getChoiceVariable(0));
    // x2 moved to the front and x0 to its place: x2, x1, x0
    assertSame(x[0], select.getChoiceVariable(1));
  }
}
