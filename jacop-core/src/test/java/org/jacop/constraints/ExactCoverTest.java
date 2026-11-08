/*
 * ExactCoverTest.java
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

package org.jacop.constraints;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Random;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link ExactCover}: the rules on small cases, and the solutions of random covers against
 * enumeration.
 */
class ExactCoverTest {

  private static IntVar[] bools(Store store, int n) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    return x;
  }

  // options {0,1}, {1}, {0,2}, {2}: selecting {0,1} removes {1} and {0,2}, and selects {2}
  @Test
  void selectionRemovesAndSelects() {
    Store store = new Store();
    IntVar[] x = bools(store, 4);
    store.impose(new ExactCover(x, new int[][] {{0, 1}, {1}, {0, 2}, {2}}, 3));
    assertThat(store.consistency()).isTrue();
    store.setLevel(1);
    x[0].domain.inValue(1, x[0], 1);
    assertThat(store.consistency()).isTrue();
    assertThat(x[1].singleton(0)).isTrue();
    assertThat(x[2].singleton(0)).isTrue();
    assertThat(x[3].singleton(1)).isTrue();
    store.removeLevel(1);
    store.setLevel(0);
    assertThat(x[1].singleton()).isFalse();
    assertThat(x[3].singleton()).isFalse();

    // after backtracking: removing {0,1} selects {1} and {0,2}, and removes {2}
    store.setLevel(1);
    x[0].domain.inValue(1, x[0], 0);
    assertThat(store.consistency()).isTrue();
    assertThat(x[1].singleton(1)).isTrue();
    assertThat(x[2].singleton(1)).isTrue();
    assertThat(x[3].singleton(0)).isTrue();
  }

  // DL+: every option of element 0 ({0,1} and {0,1,2}) covers element 1, so {1,3}, which covers 1
  // but not 0, is removed at the root; the equalities alone remove nothing there
  @Test
  void inclusionRemovesAtTheRoot() {
    Store store = new Store();
    IntVar[] x = bools(store, 5);
    store.impose(new ExactCover(x, new int[][] {{0, 1}, {0, 1, 2}, {1, 3}, {2}, {3}}, 4));
    assertThat(store.consistency()).isTrue();
    assertThat(x[2].singleton(0)).isTrue();
    // then element 3 has only {3} left
    assertThat(x[4].singleton(1)).isTrue();
    assertThat(x[0].singleton()).isFalse();
  }

  // an element no option covers fails
  @Test
  void uncoverableElementFails() {
    Store store = new Store();
    IntVar[] x = bools(store, 2);
    store.impose(new ExactCover(x, new int[][] {{0}, {0}}, 2));
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void randomCoversHaveTheSolutionsOfEnumeration() {
    Random rnd = new Random(20261108L);
    for (int trial = 0; trial < 400; trial++) {
      int n = 1 + rnd.nextInt(7);
      int m = 1 + rnd.nextInt(12);
      int[][] sets = new int[m][];
      int[] mask = new int[m];
      for (int o = 0; o < m; o++) {
        int bits = 0;
        while (bits == 0) {
          for (int e = 0; e < n; e++) {
            if (rnd.nextInt(3) == 0) {
              bits |= 1 << e;
            }
          }
        }
        mask[o] = bits;
        sets[o] = new int[Integer.bitCount(bits)];
        int k = 0;
        for (int e = 0; e < n; e++) {
          if ((bits >> e & 1) == 1) {
            sets[o][k++] = e;
          }
        }
      }
      // a side constraint, so that options get fixed by other propagators too
      int a = rnd.nextInt(m);
      int b = rnd.nextInt(m);
      boolean side = a != b && rnd.nextBoolean();

      int expected = 0;
      for (int s = 0; s < 1 << m; s++) {
        int covered = 0;
        boolean ok = !side || ((s >> a) & 1) <= ((s >> b) & 1);
        for (int o = 0; o < m && ok; o++) {
          if ((s >> o & 1) == 1) {
            ok = (covered & mask[o]) == 0;
            covered |= mask[o];
          }
        }
        if (ok && covered == (1 << n) - 1) {
          expected++;
        }
      }

      Store store = new Store();
      IntVar[] x = bools(store, m);
      ExactCover cover = new ExactCover(x, sets, n);
      store.impose(cover);
      if (side) {
        store.impose(new XlteqY(x[a], x[b]));
      }
      int found = 0;
      if (store.consistency()) {
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(true);
        search.labeling(store, new SimpleSelect<>(x, null, new IndomainRandom<>(rnd.nextInt())));
        found = search.getSolutionListener().solutionsNo();
        for (int s = 1; s <= found; s++) {
          int covered = 0;
          for (int o = 0; o < m; o++) {
            if (((IntDomain) search.getSolution(s)[o]).value() == 1) {
              assertThat(covered & mask[o]).as("trial %d solution %d", trial, s).isZero();
              covered |= mask[o];
            }
          }
          assertThat(covered).as("trial %d solution %d", trial, s).isEqualTo((1 << n) - 1);
        }
      }
      assertThat(found).as("trial %d: %s", trial, cover).isEqualTo(expected);
    }
  }
}
