/*
 * XorSystemTest.java
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
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link XorSystem}: the values that only a combination of rows implies, a failure that only
 * the sum of all rows shows, and the solutions of random systems, found by a search that fixes and
 * frees the variables in random order, against enumeration.
 */
class XorSystemTest {

  private static IntVar[] bools(Store store, int n) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    return x;
  }

  // a + b + c = 1 and b + c + d = 0 give a + d = 1, which no row gives alone
  @Test
  void combinationOfRowsPropagates() {
    Store store = new Store();
    IntVar[] x = bools(store, 4);
    store.impose(
        new XorSystem(new IntVar[][] {{x[0], x[1], x[2]}, {x[1], x[2], x[3]}}, new int[] {1, 0}));
    assertThat(store.consistency()).isTrue();
    store.setLevel(1);
    x[0].domain.inValue(1, x[0], 1);
    assertThat(store.consistency()).isTrue();
    assertThat(x[3].singleton(0)).isTrue();
    assertThat(x[1].singleton()).isFalse();
    store.removeLevel(1);
    store.setLevel(0);
    assertThat(x[3].singleton()).isFalse();

    // the other way round after backtracking, with the matrix already eliminated
    store.setLevel(1);
    x[3].domain.inValue(1, x[3], 1);
    assertThat(store.consistency()).isTrue();
    assertThat(x[0].singleton(0)).isTrue();
  }

  // a + b = 1, b + c = 1 and a + c = 1 sum to 0 = 1: the system fails before any variable is fixed
  @Test
  void inconsistentSystemFailsAtTheRoot() {
    Store store = new Store();
    IntVar[] x = bools(store, 3);
    store.impose(
        new XorSystem(
            new IntVar[][] {{x[0], x[1]}, {x[1], x[2]}, {x[0], x[2]}}, new int[] {1, 1, 1}));
    assertThat(store.consistency()).isFalse();
  }

  // a variable listed twice in a row cancels out: a + b + b = 1 is a = 1
  @Test
  void repeatedVariableCancels() {
    Store store = new Store();
    IntVar[] x = bools(store, 2);
    store.impose(new XorSystem(new IntVar[][] {{x[0], x[1], x[1]}}, new int[] {1}));
    assertThat(store.consistency()).isTrue();
    assertThat(x[0].singleton(1)).isTrue();
    assertThat(x[1].singleton()).isFalse();
  }

  @Test
  void randomSystemsHaveTheSolutionsOfEnumeration() {
    Random rnd = new Random(20261106L);
    for (int trial = 0; trial < 400; trial++) {
      int n = 2 + rnd.nextInt(8);
      int m = 1 + rnd.nextInt(n + 2);
      int[][] rows = new int[m][];
      int[] parities = new int[m];
      for (int i = 0; i < m; i++) {
        rows[i] = new int[1 + rnd.nextInt(Math.min(n, 5))];
        for (int j = 0; j < rows[i].length; j++) {
          rows[i][j] = rnd.nextInt(n);
        }
        parities[i] = rnd.nextInt(2);
      }
      // a side constraint, so that variables get fixed by other propagators too
      int a = rnd.nextInt(n);
      int b = rnd.nextInt(n);
      boolean side = a != b && rnd.nextBoolean();

      int expected = 0;
      for (int s = 0; s < 1 << n; s++) {
        boolean ok = !side || ((s >> a) & 1) <= ((s >> b) & 1);
        for (int i = 0; i < m && ok; i++) {
          int sum = parities[i];
          for (int c : rows[i]) {
            sum ^= (s >> c) & 1;
          }
          ok = sum == 0;
        }
        if (ok) {
          expected++;
        }
      }

      Store store = new Store();
      IntVar[] x = bools(store, n);
      IntVar[][] vars = new IntVar[m][];
      for (int i = 0; i < m; i++) {
        vars[i] = new IntVar[rows[i].length];
        for (int j = 0; j < rows[i].length; j++) {
          vars[i][j] = x[rows[i][j]];
        }
      }
      XorSystem system = new XorSystem(vars, parities);
      store.impose(system);
      if (side) {
        store.impose(new XlteqY(x[a], x[b]));
      }
      int found = 0;
      if (store.consistency()) {
        IntVar[] order = x.clone();
        for (int i = order.length - 1; i > 0; i--) {
          int j = rnd.nextInt(i + 1);
          IntVar t = order[i];
          order[i] = order[j];
          order[j] = t;
        }
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(true);
        search.labeling(
            store, new SimpleSelect<>(order, null, new IndomainRandom<>(rnd.nextInt())));
        found = search.getSolutionListener().solutionsNo();
        for (int s = 1; s <= found; s++) {
          int value = 0;
          for (int i = 0; i < order.length; i++) {
            int v = ((IntDomain) search.getSolution(s)[i]).value();
            for (int c = 0; c < n; c++) {
              if (x[c] == order[i]) {
                value |= v << c;
              }
            }
          }
          for (int i = 0; i < m; i++) {
            int sum = parities[i];
            for (int c : rows[i]) {
              sum ^= (value >> c) & 1;
            }
            assertThat(sum).as("trial %d solution %d row %d", trial, s, i).isZero();
          }
        }
      }
      assertThat(found).as("trial %d: %s", trial, system).isEqualTo(expected);
    }
  }

  // a redundant system that finds no failure switches itself off and the model keeps its solutions
  @Test
  public void redundantSystemSwitchesOffWithoutFailures() {
    for (boolean redundant : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar[] x = bools(store, 16);
      IntVar[] first = new IntVar[8];
      IntVar[] second = new IntVar[8];
      System.arraycopy(x, 0, first, 0, 8);
      System.arraycopy(x, 8, second, 0, 8);
      XorSystem system = new XorSystem(new IntVar[][] {first, second}, new int[] {1, 0});
      system.setRedundant(redundant);
      store.impose(system);
      store.impose(new XorBool(first, new IntVar(store, 1, 1)));
      store.impose(new XorBool(second, new IntVar(store, 0, 0)));
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      assertThat(search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()))).isTrue();
      assertThat(search.getSolutionListener().solutionsNo()).isEqualTo(1 << 14);
      assertThat(system.isOff()).as("redundant %s", redundant).isEqualTo(redundant);
    }
  }
}
