/*
 * CombCutsTest.java
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
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.Routes;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks the blossom and comb cuts of {@link CombCuts} against every set of routes of small random
 * graphs with five to seven customers, found by enumeration: no cut cuts off a set of routes,
 * whatever the LP values it was separated from, every cut is violated by those values, and a
 * solution that is a set of routes gives no cut.
 */
class CombCutsTest {

  private static final int INSTANCES = Integer.getInteger("comb.instances", 60);

  private record Graph(int n, int[] tails, int[] heads, boolean[] optional) {

    int arc(int t, int h) {
      for (int a = 0; a < tails.length; a++) {
        if (tails[a] == t && heads[a] == h) {
          return a;
        }
      }
      return -1;
    }

    // every set of routes, by depth-first search over the arcs: routes from the depot over every
    // node, an optional node either on a route or on its self loop
    Set<List<Integer>> solutions() {
      Set<List<Integer>> result = new HashSet<>();
      int[] bits = new int[tails.length];
      for (int skip = 0; skip < 1 << n; skip++) {
        boolean ok = (skip & 1) == 0;
        Arrays.fill(bits, 0);
        boolean[] visited = new boolean[n];
        for (int v = 1; v < n && ok; v++) {
          if ((skip >> v & 1) == 1) {
            int loop = arc(v, v);
            ok = optional[v] && loop >= 0;
            if (ok) {
              bits[loop] = 1;
              visited[v] = true;
            }
          }
        }
        if (ok) {
          extend(0, visited, bits, result);
        }
      }
      return result;
    }

    private void extend(int at, boolean[] visited, int[] bits, Set<List<Integer>> result) {
      if (at == 0) {
        boolean all = true;
        for (int v = 1; v < n; v++) {
          all &= visited[v];
        }
        if (all) {
          result.add(Arrays.stream(bits).boxed().toList());
          return;
        }
      }
      for (int v = 0; v < n; v++) {
        int a = arc(at, v);
        if (a < 0 || v == at || at == 0 && v == 0 || v != 0 && visited[v]) {
          continue;
        }
        bits[a] = 1;
        if (v != 0) {
          visited[v] = true;
        }
        extend(v, visited, bits, result);
        if (v != 0) {
          visited[v] = false;
        }
        bits[a] = 0;
      }
    }
  }

  private static Graph graph(Random rnd) {
    int n = 6 + rnd.nextInt(3);
    List<int[]> arcs = new ArrayList<>();
    boolean[] optional = new boolean[n];
    for (int t = 0; t < n; t++) {
      for (int h = 0; h < n; h++) {
        if (t != h && (t == 0 || h == 0 || rnd.nextInt(5) > 0)) {
          arcs.add(new int[] {t, h});
        } else if (t == h && t > 0 && rnd.nextInt(8) == 0) {
          arcs.add(new int[] {t, h});
          optional[t] = true;
        }
      }
    }
    int[] tails = arcs.stream().mapToInt(a -> a[0]).toArray();
    int[] heads = arcs.stream().mapToInt(a -> a[1]).toArray();
    return new Graph(n, tails, heads, optional);
  }

  // LP-like values: a mix of two or three sets of routes, or of two directed half cycles over the
  // customers, plus noise on some arcs
  private static double[] values(Random rnd, Graph g, List<List<Integer>> solutions) {
    double[] value = new double[g.tails().length];
    int k = 2 + rnd.nextInt(2);
    for (int i = 0; i < k; i++) {
      List<Integer> s = solutions.get(rnd.nextInt(solutions.size()));
      for (int a = 0; a < value.length; a++) {
        value[a] += s.get(a) / (double) k;
      }
    }
    for (int a = 0; a < value.length; a++) {
      if (rnd.nextInt(6) == 0) {
        value[a] = rnd.nextInt(2) == 0 ? rnd.nextDouble() : Math.round(2 * rnd.nextDouble()) / 2.0;
      }
    }
    return value;
  }

  private static long activity(CapacityCuts.Cut cut, List<Integer> bits) {
    long sum = 0;
    int[] arcs = cut.arcs();
    long[] w = cut.weights();
    for (int k = 0; k < arcs.length; k++) {
      sum += w[k] * bits.get(arcs[k]);
    }
    return sum;
  }

  private static double activity(CapacityCuts.Cut cut, double[] value) {
    double sum = 0;
    int[] arcs = cut.arcs();
    long[] w = cut.weights();
    for (int k = 0; k < arcs.length; k++) {
      sum += w[k] * Math.max(0, value[arcs[k]]);
    }
    return sum;
  }

  private static List<CapacityCuts.Cut> combs(Graph g, double[] value) {
    int n = g.n();
    boolean[] mandatory = new boolean[n];
    for (int v = 1; v < n; v++) {
      mandatory[v] = !g.optional()[v];
    }
    double[][] flow = new double[n][n];
    for (int a = 0; a < value.length; a++) {
      int t = g.tails()[a];
      int h = g.heads()[a];
      if (t != h) {
        flow[t][h] += Math.max(0, value[a]);
        flow[h][t] += Math.max(0, value[a]);
      }
    }
    return CombCuts.separate(g.tails(), g.heads(), value, mandatory, flow);
  }

  /** No blossom or comb cut, from any LP values, cuts off a set of routes. */
  @Test
  void cutsKeepEverySetOfRoutes() {
    int separated = 0;
    for (int run = 0; run < INSTANCES; run++) {
      Random rnd = new Random(run);
      Graph g = graph(rnd);
      List<List<Integer>> solutions = new ArrayList<>(g.solutions());
      if (solutions.isEmpty()) {
        continue;
      }
      for (List<Integer> s : solutions) {
        double[] value = s.stream().mapToDouble(Integer::doubleValue).toArray();
        assertThat(combs(g, value)).as("seed %d solution %s", run, s).isEmpty();
      }
      for (int trial = 0; trial < 200; trial++) {
        double[] value = values(rnd, g, solutions);
        for (CapacityCuts.Cut cut : combs(g, value)) {
          separated++;
          if (Boolean.getBoolean("comb.print")) {
            System.out.println(run + " " + cut);
          }
          assertThat(cut.entering()).isFalse();
          assertThat(activity(cut, value))
              .as("seed %d: the values violate %s", run, cut)
              .isGreaterThan(cut.bound());
          for (List<Integer> s : solutions) {
            assertThat(activity(cut, s))
                .as("seed %d: %s cuts off %s", run, cut, s)
                .isLessThanOrEqualTo(cut.bound());
          }
        }
      }
    }
    assertThat(separated).isPositive();
  }

  /**
   * The classic fractional point of the travelling salesman: two triangles 1-2-3 and 4-5-6 at 1/2
   * joined by edges at 1, 1-4, 2-5 and 3-7-0-6 through customer 7 and the depot, which every
   * subtour cut keeps; the blossom with handle {1, 2, 3} and teeth 1-4, 2-5, 3-7 cuts it off.
   */
  @Test
  void blossomCutsTheTwoTriangles() {
    int n = 8;
    List<int[]> arcs = new ArrayList<>();
    for (int t = 0; t < n; t++) {
      for (int h = 0; h < n; h++) {
        if (t != h) {
          arcs.add(new int[] {t, h});
        }
      }
    }
    int[] tails = arcs.stream().mapToInt(a -> a[0]).toArray();
    int[] heads = arcs.stream().mapToInt(a -> a[1]).toArray();
    Graph g = new Graph(n, tails, heads, new boolean[n]);
    double[][] y = new double[n][n];
    for (int[] e : new int[][] {{1, 2}, {2, 3}, {1, 3}, {4, 5}, {5, 6}, {4, 6}}) {
      y[e[0]][e[1]] = 0.5;
    }
    for (int[] e : new int[][] {{1, 4}, {2, 5}, {3, 7}, {0, 7}, {0, 6}}) {
      y[e[0]][e[1]] = 1;
    }
    // each edge at y is both arcs at y / 2: every customer has one arc in and one out
    double[] value = new double[tails.length];
    for (int a = 0; a < tails.length; a++) {
      value[a] = y[Math.min(tails[a], heads[a])][Math.max(tails[a], heads[a])] / 2;
    }
    List<CapacityCuts.Cut> found = combs(g, value);
    assertThat(found).isNotEmpty();
    for (List<Integer> s : g.solutions()) {
      for (CapacityCuts.Cut cut : found) {
        assertThat(activity(cut, s)).isLessThanOrEqualTo(cut.bound());
      }
    }
    // the cut is also found through CapacityCuts, over a Routes
    Store store = new Store();
    IntVar[] x = new IntVar[tails.length];
    for (int a = 0; a < x.length; a++) {
      x[a] = new IntVar(store, "x" + a, 0, 1);
    }
    CapacityCuts cuts = new CapacityCuts(new Routes(tails, heads, x));
    assertThat(cuts.separate(value, 100)).anyMatch(c -> !c.entering() && c.arcs().length > 6);
  }
}
