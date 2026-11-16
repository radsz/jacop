/*
 * ClauseMinerTest.java
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

package org.jacop.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Map;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** Tests the classification of learnt clauses by {@link ClauseMiner}. */
class ClauseMinerTest {

  private static IntDomain domain(int... values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v);
    }
    return d;
  }

  @Test
  void classifiesClausesOfOneConstraint() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", domain(0, 2));
    IntVar y = new IntVar(store, "y", domain(0, 2));
    IntVar z = new IntVar(store, "z", 0, 4);
    store.impose(new XplusYeqZ(x, y, z));
    AtomicTrail trail = new AtomicTrail(store);
    // no time budget: every clause is mined
    System.setProperty("jacop.lcg.mine.budget", "1e9");
    ClauseMiner miner;
    try {
      miner = new ClauseMiner(trail, store, null);
    } finally {
      System.clearProperty("jacop.lcg.mine.budget");
    }
    // z != 1 holds in every solution, but bounds propagation keeps 1: only z = 1 fails
    miner.learnt(
        new IntVar[] {z}, new int[] {ClauseMiner.EQ}, new int[] {1}, new boolean[] {false});
    // z >= 3 does not hold in every solution
    miner.learnt(new IntVar[] {z}, new int[] {ClauseMiner.GE}, new int[] {3}, new boolean[] {true});
    // x <= 0 \/ z >= 2: with x = 2 propagation alone raises z to 2
    miner.learnt(
        new IntVar[] {z, x},
        new int[] {ClauseMiner.GE, ClauseMiner.GE},
        new int[] {2, 1},
        new boolean[] {true, false});
    Map<String, long[]> counts = miner.counts();
    assertThat(counts).containsOnlyKeys("XplusYeqZ |1v", "XplusYeqZ |2v");
    long[] one = counts.get("XplusYeqZ |1v");
    assertThat(one[0]).isEqualTo(2); // tested
    assertThat(one[3]).isEqualTo(1); // not implied
    assertThat(one[7]).isEqualTo(1); // implied by failure only
    assertThat(one[5]).isEqualTo(1); // a gap
    long[] two = counts.get("XplusYeqZ |2v");
    assertThat(two[1]).isEqualTo(1); // implied by propagation
    assertThat(two[5]).isZero();
  }
}
