/*
 * ReservoirTest.java
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

package org.jacop;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.cumulative.Reservoir;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.Search;
import org.junit.jupiter.api.Test;

/**
 * Checks of {@link Reservoir}: the rules of the balance constraint on small examples, and the
 * solutions of random producer and consumer problems against the decomposition into one sum per
 * event. Solution sets of the constraint alone are compared with a brute-force enumeration in
 * {@link GlobalConstraintBruteForceTest}.
 */
class ReservoirTest {

  // -Dreservoir.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("reservoir.instances", 1000);

  @Test
  void consumptionWaitsForProductions() {
    // productions of 2 at 3..9 and 5..9, then a consumption of 3 that needs both of them
    Store store = new Store();
    IntVar[] t = {
      new IntVar(store, "p1", 3, 9), new IntVar(store, "p2", 5, 9), new IntVar(store, "c", 0, 9)
    };
    store.impose(new Reservoir(t, new int[] {2, 2, -3}, 0, 10));
    assertTrue(store.consistency());
    assertEquals(5, t[2].min());
  }

  @Test
  void productionComesBeforeTheConsumption() {
    // a consumption of 2 by time 6 needs the production of 2 before it, and so by time 6 too
    Store store = new Store();
    IntVar p = new IntVar(store, "p", 0, 9);
    IntVar c = new IntVar(store, "c", 0, 6);
    store.impose(new Reservoir(new IntVar[] {p, c}, new int[] {2, -2}, 0, 5));
    assertTrue(store.consistency());
    assertEquals(6, p.max());
  }

  @Test
  void productionsFollowingAProductionComeWithIt() {
    // x consumes 4 by time 5 from productions of 2 at y1, y2 and y3, and y2 follows y1: if y1 came
    // after x, so would y2, and y3 alone is not enough, so y1 comes before x. Without the
    // precedence each production alone could be missing
    for (boolean withPrecedence : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", 0, 5);
      IntVar y1 = new IntVar(store, "y1", 0, 10);
      IntVar y2 = new IntVar(store, "y2", 0, 10);
      IntVar y3 = new IntVar(store, "y3", 0, 10);
      IntVar[] t = {x, y1, y2, y3};
      int[] q = {-4, 2, 2, 2};
      store.impose(
          withPrecedence
              ? new Reservoir(t, q, 0, 0, 10, new IntVar[] {y1}, new IntVar[] {y2}, new int[] {1})
              : new Reservoir(t, q, 0, 10));
      store.impose(new XplusClteqZ(y1, 1, y2));
      assertTrue(store.consistency());
      assertEquals(withPrecedence ? 5 : 9, y1.max(), "with precedence " + withPrecedence);
    }
  }

  @Test
  void levelOutOfRangeFails() {
    Store store = new Store();
    IntVar[] t = {new IntVar(store, 0, 3), new IntVar(store, 0, 3)};
    store.impose(new Reservoir(t, new int[] {-1, -1}, 0, 5));
    assertFalse(store.consistency());
  }

  @Test
  void randomProblemsMatchTheDecomposition() {
    Random random = new Random(20261027);
    for (int k = 0; k < INSTANCES; k++) {
      Problem p = Problem.random(random);
      long reservoir = p.solutions(true);
      long decomposition = p.solutions(false);
      assertEquals(decomposition, reservoir, () -> p.toString());
    }
  }

  /** Producers and consumers, some linked by precedences, on one reservoir. */
  private record Problem(
      int n, int horizon, int[] changes, int initial, int min, int max, List<int[]> arcs) {

    static Problem random(Random random) {
      int n = 3 + random.nextInt(4);
      int[] changes = new int[n];
      for (int i = 0; i < n; i++) {
        changes[i] = random.nextInt(9) - 4;
      }
      int min = -random.nextInt(3);
      int max = 1 + random.nextInt(5);
      int initial = min + random.nextInt(max - min + 1);
      List<int[]> arcs = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          int c = random.nextInt(8);
          if (c < 2) {
            arcs.add(new int[] {i, j, c});
          } else if (c == 2) {
            arcs.add(new int[] {j, i, -2});
          }
        }
      }
      return new Problem(n, 5, changes, initial, min, max, arcs);
    }

    @Override
    public String toString() {
      StringBuilder b = new StringBuilder("changes=" + Arrays.toString(changes));
      b.append(" initial=").append(initial).append(" [").append(min).append(", ").append(max);
      b.append("]");
      for (int[] a : arcs) {
        b.append(" t").append(a[0]).append("+").append(a[2]).append("<=t").append(a[1]);
      }
      return b.toString();
    }

    long solutions(boolean global) {
      Store store = new Store();
      IntVar[] t = new IntVar[n];
      for (int i = 0; i < n; i++) {
        t[i] = new IntVar(store, "t" + i, 0, horizon);
      }
      IntVar[] from = new IntVar[arcs.size()];
      IntVar[] to = new IntVar[arcs.size()];
      int[] lag = new int[arcs.size()];
      for (int k = 0; k < arcs.size(); k++) {
        int[] a = arcs.get(k);
        from[k] = t[a[0]];
        to[k] = t[a[1]];
        lag[k] = a[2];
        store.impose(new XplusClteqZ(from[k], lag[k], to[k]));
      }
      if (global) {
        store.impose(new Reservoir(t, changes, initial, min, max, from, to, lag));
      } else {
        if (initial < min || initial > max) {
          return 0;
        }
        for (int x = 0; x < n; x++) {
          IntVar[] b = new IntVar[n];
          for (int y = 0; y < n; y++) {
            b[y] = new IntVar(store, 0, 1);
            if (y == x) {
              b[y].domain.in(store.level, b[y], 1, 1);
            } else {
              store.impose(new Reified(new XlteqY(t[y], t[x]), b[y]));
            }
          }
          IntVar level = new IntVar(store, min - initial, max - initial);
          store.impose(new LinearInt(b, changes, "==", level));
        }
      }
      if (!store.consistency()) {
        return 0;
      }
      Search<IntVar> search = new DepthFirstSearch<>();
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      search.setPrintInfo(false);
      if (!search.labeling(store, new InputOrderSelect<>(store, t, new IndomainMin<>()))) {
        return 0;
      }
      return search.getSolutionListener().solutionsNo();
    }
  }
}
