/*
 * CapacityCutsTest.java
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
package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.Routes;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks the rounded capacity cuts of {@link CapacityCuts} against every set of routes of small
 * random graphs, found by enumeration: no cut may cut off a set of routes, whatever the LP values
 * the cuts were separated from, and a solution that is a set of routes violates no cut.
 */
class CapacityCutsTest {

  private static final int INSTANCES = Integer.getInteger("capacity.instances", 100);

  private record Graph(int n, int[] tails, int[] heads, int[] demands, int capacity) {

    // whether the arcs at 1 are routes from the depot over every node not on its self loop
    boolean routes(int[] bits) {
      int[] in = new int[n];
      int[] out = new int[n];
      int[] succ = new int[n];
      boolean[] off = new boolean[n];
      Arrays.fill(succ, -1);
      for (int a = 0; a < bits.length; a++) {
        if (bits[a] == 1) {
          if (tails[a] == heads[a]) {
            off[tails[a]] = true;
          } else {
            succ[tails[a]] = heads[a];
          }
          out[tails[a]]++;
          in[heads[a]]++;
        }
      }
      boolean[] visited = new boolean[n];
      for (int v = 1; v < n; v++) {
        if (in[v] != 1 || out[v] != 1) {
          return false;
        }
      }
      for (int a = 0; a < bits.length; a++) {
        if (bits[a] == 1 && tails[a] == 0 && heads[a] != 0) {
          long load = 0;
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

    List<int[]> solutions() {
      List<int[]> result = new ArrayList<>();
      int m = tails.length;
      for (long mask = 0; mask < (1L << m); mask++) {
        int[] bits = new int[m];
        for (int a = 0; a < m; a++) {
          bits[a] = (int) (mask >> a & 1);
        }
        if (routes(bits)) {
          result.add(bits);
        }
      }
      return result;
    }
  }

  private static Graph graph(Random rnd) {
    int n = 4 + rnd.nextInt(2);
    List<int[]> arcs = new ArrayList<>();
    for (int t = 0; t < n; t++) {
      for (int h = 0; h < n; h++) {
        if (t != h && (t == 0 || h == 0 || rnd.nextInt(4) > 0)) {
          arcs.add(new int[] {t, h});
        } else if (t == h && t > 0 && rnd.nextInt(6) == 0) {
          arcs.add(new int[] {t, h});
        }
      }
    }
    while (arcs.size() > 17) {
      arcs.remove(rnd.nextInt(arcs.size()));
    }
    int[] tails = arcs.stream().mapToInt(a -> a[0]).toArray();
    int[] heads = arcs.stream().mapToInt(a -> a[1]).toArray();
    int[] demands = null;
    int capacity = 0;
    if (rnd.nextInt(4) > 0) {
      demands = new int[n];
      for (int v = 1; v < n; v++) {
        demands[v] = rnd.nextInt(6);
      }
      capacity = 3 + rnd.nextInt(8);
    }
    return new Graph(n, tails, heads, demands, capacity);
  }

  private static boolean holds(CapacityCuts.Cut cut, int[] bits) {
    long sum = 0;
    for (int a : cut.arcs()) {
      sum += bits[a];
    }
    return cut.entering() ? sum >= cut.bound() : sum <= cut.bound();
  }

  private static double activity(CapacityCuts.Cut cut, double[] value) {
    double sum = 0;
    for (int a : cut.arcs()) {
      sum += value[a];
    }
    return sum;
  }

  /** No cut, from any LP values, cuts off a set of routes; routes themselves violate no cut. */
  @Test
  void cutsKeepEverySetOfRoutes() {
    int separated = 0;
    for (int run = 0; run < INSTANCES; run++) {
      Random rnd = new Random(run);
      Graph g = graph(rnd);
      Store store = new Store();
      IntVar[] literals = new IntVar[g.tails().length];
      for (int a = 0; a < literals.length; a++) {
        literals[a] = new IntVar(store, "x" + a, 0, 1);
      }
      CapacityCuts cuts =
          new CapacityCuts(new Routes(g.tails(), g.heads(), literals, g.demands(), g.capacity()));
      List<int[]> solutions = g.solutions();
      for (int[] s : solutions) {
        double[] value = Arrays.stream(s).asDoubleStream().toArray();
        assertThat(cuts.separate(value, 100)).as("seed %d solution %s", run, s).isEmpty();
      }
      for (int trial = 0; trial < 20; trial++) {
        double[] value = new double[literals.length];
        for (int a = 0; a < value.length; a++) {
          value[a] = rnd.nextInt(3) == 0 ? 0 : rnd.nextDouble();
        }
        for (CapacityCuts.Cut cut : cuts.separate(value, 100)) {
          separated++;
          double act = activity(cut, value);
          assertThat(cut.entering() ? act < cut.bound() : act > cut.bound())
              .as("seed %d: the values violate %s", run, cut)
              .isTrue();
          for (int[] s : solutions) {
            assertThat(holds(cut, s)).as("seed %d: %s cuts off %s", run, cut, s).isTrue();
          }
        }
      }
    }
    assertThat(separated).isPositive();
  }

  /** Two customers whose demands fill more than a vehicle need two routes into them. */
  @Test
  void twoRoutesIntoCustomersOverTheCapacity() {
    // depot 0, customers 1 and 2 of demand 3 each, capacity 4: one route 0-1-2-0 at 1/2 and the
    // two single routes at 1/2 give one entering arc only
    int[] tails = {0, 0, 1, 2, 1, 2};
    int[] heads = {1, 2, 2, 1, 0, 0};
    Store store = new Store();
    IntVar[] x = new IntVar[tails.length];
    for (int a = 0; a < x.length; a++) {
      x[a] = new IntVar(store, "x" + a, 0, 1);
    }
    CapacityCuts cuts = new CapacityCuts(new Routes(tails, heads, x, new int[] {0, 3, 3}, 4));
    double[] value = {0.5, 0.5, 0.5, 0.5, 0.5, 0.5};
    List<CapacityCuts.Cut> found = cuts.separate(value, 10);
    assertThat(found).isNotEmpty();
    CapacityCuts.Cut best = found.get(0);
    // either two arcs from the depot at least, or the arcs between 1 and 2 at most 0
    assertThat(best.entering() ? best.bound() : 2 - best.bound()).isEqualTo(2);
  }
}
