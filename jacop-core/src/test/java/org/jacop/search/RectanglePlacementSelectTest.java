/*
 * RectanglePlacementSelectTest.java
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.jacop.constraints.XeqC;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** Tests the bottom-left placement of rectangles. */
class RectanglePlacementSelectTest {

  @Test
  void theRectangleThatCanStartFirstIsPlacedWholeBeforeTheNext() {
    Store store = new Store();
    IntVar[][] r = new IntVar[3][];
    // origins x and y, lengths dx (variable for the first two) and dy
    r[0] = rectangle(store, "a", 2, 9, 2, 3, 1);
    r[1] = rectangle(store, "b", 0, 9, 1, 2, 2);
    r[2] = rectangle(store, "c", 0, 9, 3, 3, 1);
    store.impose(new Diffn(r));
    assertTrue(store.consistency());
    RectanglePlacementSelect select = new RectanglePlacementSelect(r);

    // b and c can both start at 0; b's second origin is 0 too, c's tie is broken by input order
    IntVar x = select.getChoiceVariable(0);
    assertSame(r[1][0], x);
    assertEquals(0, select.getChoiceValue());
    store.setLevel(1);
    store.impose(new XeqC(x, 0));
    assertTrue(store.consistency());
    // b is completed: its length in the first dimension, then its origin in the second
    assertSame(r[1][2], select.getChoiceVariable(select.getIndex()));
    assertEquals(1, select.getChoiceValue());
    store.impose(new XeqC(r[1][2], 1));
    assertTrue(store.consistency());
    assertSame(r[1][1], select.getChoiceVariable(select.getIndex()));
    assertEquals(0, select.getChoiceValue());
    store.impose(new XeqC(r[1][1], 0));
    assertTrue(store.consistency());
    // then c, which can still start at 0
    assertSame(r[2][0], select.getChoiceVariable(select.getIndex()));
    assertEquals(0, select.getChoiceValue());
  }

  @Test
  void depthFirstSearchFindsEveryPacking() {
    for (int seed = 0; seed < 2; seed++) {
      int[] counts = new int[2];
      for (int k = 0; k < 2; k++) {
        Store store = new Store();
        IntVar[][] r = new IntVar[3][];
        r[0] = rectangle(store, "a", 0, 3, 1, 2, 2);
        r[1] = rectangle(store, "b", 0, 3, 2, 2, 1);
        r[2] = rectangle(store, "c", 0, 3, 1, 1 + seed, 1);
        store.impose(new Diffn(r));
        // a 4 x 3 box
        for (IntVar[] t : r) {
          store.impose(new XplusYlteqZ(t[0], t[2], new IntVar(store, 4, 4)));
          store.impose(new XplusYlteqZ(t[1], t[3], new IntVar(store, 3, 3)));
        }
        IntVar[] all = new IntVar[12];
        for (int i = 0; i < 3; i++) {
          System.arraycopy(r[i], 0, all, 4 * i, 4);
        }
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(false);
        SelectChoicePoint<IntVar> select =
            k == 0
                ? new RectanglePlacementSelect(r)
                : new SimpleSelect<>(all, null, new IndomainMin<>());
        assertTrue(search.labeling(store, select));
        counts[k] = search.getSolutionListener().solutionsNo();
      }
      assertTrue(counts[1] > 0);
      assertEquals(counts[1], counts[0]);
    }
  }

  @Test
  void placedRectanglesLeaveNothingToChoose() {
    Store store = new Store();
    IntVar[][] r = {rectangle(store, "a", 1, 1, 2, 2, 1)};
    assertNull(new RectanglePlacementSelect(r).getChoiceVariable(0));
  }

  private static IntVar[] rectangle(
      Store store, String name, int min, int max, int lengthMin, int lengthMax, int height) {
    return new IntVar[] {
      new IntVar(store, name + "x", min, max),
      new IntVar(store, name + "y", min, max),
      new IntVar(store, name + "dx", lengthMin, lengthMax),
      new IntVar(store, name + "dy", height, height)
    };
  }
}
