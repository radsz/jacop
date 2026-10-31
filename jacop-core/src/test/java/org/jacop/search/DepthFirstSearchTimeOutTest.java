/*
 * DepthFirstSearchTimeOutTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

class DepthFirstSearchTimeOutTest {

  @Test
  void childSearchTimingOutAtStartRestoresTheStoreLevel() {
    // A child search whose time-out had passed when it started returned after raising the store
    // level without removing it. The master search then tried to remove its own level, which was
    // no longer the most recent one, and threw IllegalStateException. Fz2jacop hit this with -t.
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x0", 1, 3), new IntVar(store, "x1", 1, 3)};
    IntVar[] y = {new IntVar(store, "y0", 1, 3), new IntVar(store, "y1", 1, 3)};
    store.impose(new XneqY(x[0], x[1]));
    store.impose(new XneqY(y[0], y[1]));

    assertMasterTimesOutWithChild(store, x, y, 0, -1);
  }

  @Test
  void childSearchTimingOutMakesTheMasterSearchIncomplete() {
    // The master search labels x, which has a single value, and hands the 2^24 assignments of y
    // to the child search. None is a solution (an even sum cannot be 25), so the child times out.
    // The master had no node left to check its own time-out, so it ended with no solution and no
    // time-out, and Fz2jacop printed =====UNSATISFIABLE===== (hakank's farmer_and_cows).
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 0);
    IntVar[] y = new IntVar[24];
    int[] weights = new int[y.length + 1];
    IntVar[] all = new IntVar[y.length + 1];
    for (int i = 0; i < y.length; i++) {
      y[i] = new IntVar(store, "y" + i, 0, 1);
      weights[i] = 2;
      all[i] = y[i];
    }
    weights[y.length] = 1;
    all[y.length] = x;
    store.impose(new LinearInt(all, weights, "==", 25));

    assertMasterTimesOutWithChild(store, new IntVar[] {x}, y, 200, 200);
  }

  /** Labels x with a master search and y with its child search, which times out. */
  private static void assertMasterTimesOutWithChild(
      Store store, IntVar[] x, IntVar[] y, long masterTimeOut, long childTimeOut) {
    DepthFirstSearch<IntVar> master = new DepthFirstSearch<>();
    DepthFirstSearch<IntVar> child = new DepthFirstSearch<>();
    master.setPrintInfo(false);
    child.setPrintInfo(false);
    child.setSelectChoicePoint(new SimpleSelect<>(y, null, new IndomainMin<>()));
    if (masterTimeOut != 0) {
      master.setTimeOutMilliseconds(masterTimeOut);
    }
    child.setTimeOutMilliseconds(childTimeOut);
    master.addChildSearch(child);
    int level = store.level;

    boolean result = master.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()));

    assertThat(result).isFalse();
    assertThat(child.timeOutOccured).isTrue();
    assertThat(master.timeOutOccured).isTrue();
    assertThat(store.level).isEqualTo(level);
  }

  @Test
  void longPropagationStopsAtTheTimeOut() {
    // x < y and y < x lower the maximum of one variable by 1 per propagator call, so proving the
    // failure takes 2 * 10^8 calls. The time-out was checked between search nodes only, so the
    // search ran far past it (hakank's ages, where float bounds converge as slowly) and then
    // reported the failure as a complete search.
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 100_000_000);
    IntVar y = new IntVar(store, "y", 0, 100_000_000);
    store.impose(new XltY(x, y));
    store.impose(new XltY(y, x));

    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setTimeOutMilliseconds(100);
    int level = store.level;
    long start = System.currentTimeMillis();

    boolean result =
        search.labeling(store, new SimpleSelect<>(new IntVar[] {x, y}, null, new IndomainMin<>()));

    assertThat(result).isFalse();
    assertThat(search.timeOutOccured).isTrue();
    assertThat(System.currentTimeMillis() - start).isLessThan(10_000);
    assertThat(store.level).isEqualTo(level);
    assertThat(store.getConsistencyDeadline()).isZero();
  }
}
