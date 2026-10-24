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

    DepthFirstSearch<IntVar> master = new DepthFirstSearch<>();
    DepthFirstSearch<IntVar> child = new DepthFirstSearch<>();
    master.setPrintInfo(false);
    child.setPrintInfo(false);
    child.setSelectChoicePoint(new SimpleSelect<>(y, null, new IndomainMin<>()));
    child.setTimeOutMilliseconds(-1);
    master.addChildSearch(child);
    int level = store.level;

    boolean result = master.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()));

    assertThat(result).isFalse();
    assertThat(child.timeOutOccured).isTrue();
    assertThat(store.level).isEqualTo(level);
  }
}
