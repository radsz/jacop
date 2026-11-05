/*
 * RoutesTest.java
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

import static org.assertj.core.api.Assertions.assertThatThrownBy;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.TreeSet;
import org.jacop.constraints.Routes;
import org.jacop.constraints.SumInt;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/** Brute-force checks of {@link Routes} against an enumeration of every arc assignment. */
class RoutesTest {

  // -Droutes.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("routes.instances", 600);

  /** A random graph on nodes 0..n-1, with demands and a capacity (or none) and fixed literals. */
  private record Instance(
      int n, int[] tails, int[] heads, int[] demands, int capacity, int[] fixed) {

    /** Whether an assignment of the arcs is a set of routes from the depot, by plain search. */
    boolean routes(int[] bits) {
      int[] in = new int[n];
      int[] out = new int[n];
      int[] succ = new int[n];
      boolean[] off = new boolean[n];
      Arrays.fill(succ, -1);
      for (int a = 0; a < bits.length; a++) {
        if (fixed[a] >= 0 && bits[a] != fixed[a]) {
          return false;
        }
        if (bits[a] == 1) {
          out[tails[a]]++;
          in[heads[a]]++;
          if (tails[a] == heads[a]) {
            if (tails[a] == 0) {
              return false;
            }
            off[tails[a]] = true;
          } else {
            succ[tails[a]] = heads[a];
          }
        }
      }
      for (int v = 1; v < n; v++) {
        if (in[v] != 1 || out[v] != 1) {
          return false;
        }
      }
      boolean[] visited = new boolean[n];
      for (int a = 0; a < bits.length; a++) {
        if (bits[a] == 1 && tails[a] == 0 && heads[a] != 0) {
          int load = 0;
          for (int w = heads[a]; w != 0; w = succ[w]) {
            if (visited[w]) {
              return false;
            }
            visited[w] = true;
            load += demands == null ? 0 : demands[w];
          }
          if (demands != null && load > capacity) {
            return false;
          }
        }
      }
      for (int v = 1; v < n; v++) {
        if (!off[v] && !visited[v]) {
          return false;
        }
      }
      return true;
    }

    TreeSet<String> solutions() {
      TreeSet<String> result = new TreeSet<>();
      int m = tails.length;
      int[] bits = new int[m];
      for (long mask = 0; mask < (1L << m); mask++) {
        for (int a = 0; a < m; a++) {
          bits[a] = (int) (mask >> a & 1);
        }
        if (routes(bits)) {
          result.add(Arrays.toString(bits));
        }
      }
      return result;
    }

    @Override
    public String toString() {
      return "n="
          + n
          + " tails="
          + Arrays.toString(tails)
          + " heads="
          + Arrays.toString(heads)
          + " demands="
          + Arrays.toString(demands)
          + " capacity="
          + capacity
          + " fixed="
          + Arrays.toString(fixed);
    }
  }

  private static Instance random(Random random) {
    int n = 2 + random.nextInt(5);
    List<int[]> all = new ArrayList<>();
    for (int t = 0; t < n; t++) {
      for (int h = 0; h < n; h++) {
        if (t != h || t != 0 && random.nextInt(3) == 0) {
          all.add(new int[] {t, h});
        }
      }
    }
    Collections.shuffle(all, random);
    int m = Math.min(all.size(), 6 + random.nextInt(9));
    // drop some arcs, at random
    int[] tails = new int[m];
    int[] heads = new int[m];
    for (int a = 0; a < m; a++) {
      tails[a] = all.get(a)[0];
      heads[a] = all.get(a)[1];
    }
    // the nodes of the constraint are those on its arcs
    n = 1;
    for (int a = 0; a < m; a++) {
      n = Math.max(n, Math.max(tails[a], heads[a]) + 1);
    }
    int[] demands = null;
    int capacity = 0;
    if (random.nextBoolean()) {
      demands = new int[n];
      for (int v = 1; v < n; v++) {
        demands[v] = random.nextInt(4);
      }
      capacity = random.nextInt(8);
    }
    int[] fixed = new int[m];
    for (int a = 0; a < m; a++) {
      fixed[a] = random.nextInt(6) == 0 ? random.nextInt(2) : -1;
    }
    return new Instance(n, tails, heads, demands, capacity, fixed);
  }

  private static TreeSet<String> solve(Instance in, Random random) {
    return solve(in, random, true);
  }

  // with degrees false, the degrees are kept by one linear row per node and direction instead
  private static TreeSet<String> solve(Instance in, Random random, boolean degrees) {
    Store store = new Store();
    IntVar[] x = new IntVar[in.tails.length];
    for (int a = 0; a < x.length; a++) {
      x[a] = new IntVar(store, "x" + a, 0, 1);
      if (in.fixed[a] >= 0) {
        x[a].domain.in(store.level, x[a], in.fixed[a], in.fixed[a]);
      }
    }
    Routes routes = new Routes(in.tails, in.heads, x, in.demands, in.capacity);
    routes.setDegrees(degrees);
    store.impose(routes);
    if (!degrees) {
      for (int v = 1; v < in.n; v++) {
        for (int side = 0; side < 2; side++) {
          List<IntVar> row = new ArrayList<>();
          for (int a = 0; a < x.length; a++) {
            if ((side == 0 ? in.tails[a] : in.heads[a]) == v) {
              row.add(x[a]);
            }
          }
          if (row.isEmpty()) {
            return new TreeSet<>();
          }
          store.impose(new SumInt(row, "==", new IntVar(store, 1, 1)));
        }
      }
    }
    TreeSet<String> found = new TreeSet<>();
    if (!store.consistency()) {
      return found;
    }
    List<IntVar> shuffled = new ArrayList<>(Arrays.asList(x));
    Collections.shuffle(shuffled, random);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            shuffled.toArray(new IntVar[0]), null, new IndomainRandom<>(random.nextInt()));
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);
    if (search.labeling(store, select)) {
      int count = search.getSolutionListener().solutionsNo();
      for (int s = 1; s <= count; s++) {
        Domain[] sol = search.getSolutionListener().getSolution(s);
        int[] t = new int[x.length];
        for (int q = 0; q < x.length; q++) {
          t[q] = ((IntDomain) sol[shuffled.indexOf(x[q])]).value();
        }
        found.add(Arrays.toString(t));
      }
    }
    return found;
  }

  @Test
  void allSolutionsMatchBruteForce() {
    Random random = new Random(20261104);
    int nonEmpty = 0;
    for (int i = 0; i < INSTANCES; i++) {
      Instance in = random(random);
      TreeSet<String> expected = in.solutions();
      if (!expected.isEmpty()) {
        nonEmpty++;
      }
      assertEquals(expected, solve(in, random), in.toString());
    }
    assertTrue(nonEmpty > INSTANCES / 10, "too few instances with routes: " + nonEmpty);
  }

  @Test
  void pathsAloneWithLinearDegreesMatchBruteForce() {
    Random random = new Random(20261105);
    for (int i = 0; i < INSTANCES; i++) {
      Instance in = random(random);
      assertEquals(in.solutions(), solve(in, random, false), in.toString());
    }
  }

  @Test
  void aPathCannotCloseWithoutTheDepot() {
    // 0 -> 1 -> 2 -> 0 or the circuit 1 -> 2 -> 1; with 1 -> 2 fixed, 2 -> 1 must go
    Store store = new Store();
    int[] tails = {0, 1, 2, 2, 1, 0};
    int[] heads = {1, 2, 0, 1, 0, 2};
    IntVar[] x = new IntVar[tails.length];
    for (int a = 0; a < x.length; a++) {
      x[a] = new IntVar(store, "x" + a, 0, 1);
    }
    store.impose(new Routes(tails, heads, x));
    x[1].domain.in(store.level, x[1], 1, 1);
    assertTrue(store.consistency());
    assertEquals(0, x[3].max());
  }

  @Test
  void twoPathsOverTheCapacityCannotJoin() {
    // nodes 1 and 2 each with demand 3 and capacity 5: arcs 1 -> 2 and 2 -> 1 go
    Store store = new Store();
    int[] tails = {0, 0, 1, 2, 1, 2};
    int[] heads = {1, 2, 2, 1, 0, 0};
    IntVar[] x = new IntVar[tails.length];
    for (int a = 0; a < x.length; a++) {
      x[a] = new IntVar(store, "x" + a, 0, 1);
    }
    store.impose(new Routes(tails, heads, x, new int[] {0, 3, 3}, 5));
    assertTrue(store.consistency());
    assertEquals(0, x[2].max());
    assertEquals(0, x[3].max());
    assertEquals(1, x[0].min());
    assertEquals(1, x[1].min());
    assertTrue(new Routes(tails, heads, x, new int[] {0, 3, 3}, 5).satisfied());
  }

  @Test
  void argumentsAreValidated() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    assertThatThrownBy(() -> new Routes(new int[] {0}, new int[] {1, 0}, new IntVar[] {a, b}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new Routes(new int[] {0, 1}, new int[] {1, 0}, new IntVar[] {a, a}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new Routes(
                    new int[] {0, 1}, new int[] {1, 0}, new IntVar[] {a, b}, new int[] {0, -1}, 3))
        .isInstanceOf(IllegalArgumentException.class);
    assertFalse(new Routes(new int[] {0, 1}, new int[] {1, 0}, new IntVar[] {a, b}).satisfied());
  }
}
