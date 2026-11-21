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
import org.jacop.lcg.LinearForm;
import org.junit.jupiter.api.Test;

/**
 * Checks the rounded capacity and multistar cuts of {@link CapacityCuts} against every set of
 * routes of small random graphs, found by enumeration: no cut may cut off a set of routes, whatever
 * the LP values the cuts were separated from, and a solution that is a set of routes violates no
 * cut.
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
    int[] arcs = cut.arcs();
    long[] w = cut.weights();
    for (int k = 0; k < arcs.length; k++) {
      sum += w[k] * bits[arcs[k]];
    }
    return cut.entering() ? sum >= cut.bound() : sum <= cut.bound();
  }

  private static double activity(CapacityCuts.Cut cut, double[] value) {
    double sum = 0;
    int[] arcs = cut.arcs();
    long[] w = cut.weights();
    for (int k = 0; k < arcs.length; k++) {
      sum += w[k] * value[arcs[k]];
    }
    return sum;
  }

  /** No cut, from any LP values, cuts off a set of routes; routes themselves violate no cut. */
  @Test
  void cutsKeepEverySetOfRoutes() {
    int separated = 0;
    int multistar = 0;
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
          if (Arrays.stream(cut.weights()).anyMatch(w -> w != 1)) {
            multistar++;
          }
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
    assertThat(multistar).isPositive();
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

  // whether every route of the arcs at 1 keeps the time windows: it leaves the depot at
  // earliest[0], reaches each node at max(earliest, time + travel) by latest, and comes back by
  // latest[0]
  private static boolean timely(
      int[] tails, int[] heads, int[] bits, long[] earliest, long[] latest, long[] travel) {
    int n = earliest.length;
    int[] arcOut = new int[n];
    Arrays.fill(arcOut, -1);
    for (int a = 0; a < bits.length; a++) {
      if (bits[a] == 1 && tails[a] != heads[a] && tails[a] != 0) {
        arcOut[tails[a]] = a;
      }
    }
    for (int a = 0; a < bits.length; a++) {
      if (bits[a] != 1 || tails[a] != 0 || heads[a] == 0) {
        continue;
      }
      long t = earliest[0];
      int arc = a;
      for (int steps = 0; steps <= n; steps++) {
        int w = heads[arc];
        t = Math.max(earliest[w], t + travel[arc]);
        if (t > latest[w]) {
          return false;
        }
        if (w == 0) {
          break;
        }
        arc = arcOut[w];
      }
    }
    return true;
  }

  /**
   * No infeasible path cut, from any LP values, cuts off a set of routes that keeps the time
   * windows, and such routes violate no cut.
   */
  @Test
  void pathCutsKeepEveryTimelySetOfRoutes() {
    // the 2-path cuts are among them: sets that one route cannot visit in one stretch
    int separated = 0;
    int twoPaths = 0;
    for (int run = 0; run < INSTANCES; run++) {
      Random rnd = new Random(1000 + run);
      Graph g = graph(rnd);
      int n = g.n();
      long[] earliest = new long[n];
      long[] latest = new long[n];
      latest[0] = 10 + rnd.nextInt(20);
      for (int v = 1; v < n; v++) {
        earliest[v] = rnd.nextInt(10);
        latest[v] = earliest[v] + rnd.nextInt(12);
      }
      long[] travel = new long[g.tails().length];
      for (int a = 0; a < travel.length; a++) {
        travel[a] = rnd.nextInt(8) == 0 ? Long.MIN_VALUE : 1 + rnd.nextInt(6);
      }
      Store store = new Store();
      IntVar[] literals = new IntVar[g.tails().length];
      for (int a = 0; a < literals.length; a++) {
        literals[a] = new IntVar(store, "x" + a, 0, 1);
      }
      Routes routes = new Routes(g.tails(), g.heads(), literals, g.demands(), g.capacity());
      routes.setTimeWindows(earliest, latest, travel);
      CapacityCuts cuts = new CapacityCuts(routes);
      List<int[]> solutions = new ArrayList<>();
      for (int[] s : g.solutions()) {
        if (timely(g.tails(), g.heads(), s, earliest, latest, travel)) {
          solutions.add(s);
        }
      }
      for (int[] s : solutions) {
        double[] value = Arrays.stream(s).asDoubleStream().toArray();
        assertThat(cuts.separate(value, 100))
            .as(
                "seed %d solution %s tails %s heads %s e %s l %s tr %s",
                run,
                Arrays.toString(s),
                Arrays.toString(g.tails()),
                Arrays.toString(g.heads()),
                Arrays.toString(earliest),
                Arrays.toString(latest),
                Arrays.toString(travel))
            .isEmpty();
      }
      for (int trial = 0; trial < 20; trial++) {
        double[] value = new double[literals.length];
        for (int a = 0; a < value.length; a++) {
          value[a] = rnd.nextInt(3) == 0 ? 0 : rnd.nextInt(2) == 0 ? 1 : rnd.nextDouble();
        }
        int before = cuts.pathCuts();
        int twoBefore = cuts.twoPathCuts();
        for (CapacityCuts.Cut cut : cuts.separate(value, 100)) {
          double act = activity(cut, value);
          assertThat(cut.entering() ? act < cut.bound() : act > cut.bound())
              .as("seed %d: the values violate %s", run, cut)
              .isTrue();
          for (int[] s : solutions) {
            assertThat(holds(cut, s)).as("seed %d: %s cuts off %s", run, cut, s).isTrue();
          }
        }
        separated += cuts.pathCuts() - before;
        twoPaths += cuts.twoPathCuts() - twoBefore;
      }
    }
    assertThat(separated).isPositive();
    assertThat(twoPaths).isPositive();
  }

  // the earliest times of the routes of a timely set of routes, each node at the earliest time its
  // predecessor allows; a node off the routes at its earliest time
  private static long[] times(
      int[] tails, int[] heads, int[] bits, long[] earliest, long[] travel, int n) {
    long[] t = Arrays.copyOf(earliest, n);
    int[] arcOut = new int[n];
    Arrays.fill(arcOut, -1);
    for (int a = 0; a < bits.length; a++) {
      if (bits[a] == 1 && tails[a] != heads[a] && tails[a] != 0) {
        arcOut[tails[a]] = a;
      }
    }
    for (int a = 0; a < bits.length; a++) {
      if (bits[a] != 1 || tails[a] != 0 || heads[a] == 0) {
        continue;
      }
      long time = earliest[0];
      int arc = a;
      for (int steps = 0; steps <= n; steps++) {
        int w = heads[arc];
        if (w == 0) {
          break;
        }
        time =
            travel[arc] == Long.MIN_VALUE ? earliest[w] : Math.max(earliest[w], time + travel[arc]);
        t[w] = time;
        arc = arcOut[w];
      }
    }
    return t;
  }

  /**
   * The arc-time rows of the relaxation hold in every set of routes that keeps the time windows,
   * with the earliest times of its routes.
   */
  @Test
  void arcTimeRowsHoldInEveryTimelySetOfRoutes() {
    int rows = 0;
    for (int run = 0; run < INSTANCES; run++) {
      Random rnd = new Random(3000 + run);
      Graph g = graph(rnd);
      int n = g.n();
      long[] earliest = new long[n];
      long[] latest = new long[n];
      latest[0] = 10 + rnd.nextInt(20);
      for (int v = 1; v < n; v++) {
        earliest[v] = rnd.nextInt(10);
        latest[v] = earliest[v] + rnd.nextInt(12);
      }
      long[] travel = new long[g.tails().length];
      for (int a = 0; a < travel.length; a++) {
        travel[a] = rnd.nextInt(8) == 0 ? Long.MIN_VALUE : 1 + rnd.nextInt(6);
      }
      Store store = new Store();
      IntVar[] literals = new IntVar[g.tails().length];
      for (int a = 0; a < literals.length; a++) {
        literals[a] = new IntVar(store, "x" + a, 0, 1);
      }
      IntVar[] t = new IntVar[n];
      for (int v = 1; v < n; v++) {
        t[v] = new IntVar(store, "t" + v, (int) earliest[v], (int) latest[v]);
      }
      Routes routes = new Routes(g.tails(), g.heads(), literals, g.demands(), g.capacity());
      routes.setTimeWindows(earliest, latest, travel);
      routes.setTimes(t);
      List<LinearForm> forms = CapacityCuts.arcTimeRows(routes, true);
      rows += forms.size();
      for (int[] s : g.solutions()) {
        if (!timely(g.tails(), g.heads(), s, earliest, latest, travel)) {
          continue;
        }
        long[] time = times(g.tails(), g.heads(), s, earliest, travel, n);
        for (LinearForm f : forms) {
          long lhs = 0;
          for (int k = 0; k < f.vars().length; k++) {
            IntVar v = f.vars()[k];
            int arc = Arrays.asList(literals).indexOf(v);
            int node = Arrays.asList(t).indexOf(v);
            lhs += f.weights()[k] * (arc >= 0 ? s[arc] : time[node]);
          }
          assertThat(lhs)
              .as("seed %d: %s on %s", run, f, Arrays.toString(s))
              .isGreaterThanOrEqualTo(f.c());
        }
      }
    }
    assertThat(rows).isPositive();
  }

  /**
   * Two customers that one route cannot visit one after the other in either order within their
   * windows are entered twice: a single route over both gets a 2-path cut.
   */
  @Test
  void customersNoRouteVisitsInOneStretchAreEnteredTwice() {
    // depot 0, customers 1 and 2, both open in [0, 5] and 10 apart either way
    int[] tails = {0, 0, 1, 2, 1, 2};
    int[] heads = {1, 2, 2, 1, 0, 0};
    Store store = new Store();
    IntVar[] x = new IntVar[tails.length];
    for (int a = 0; a < x.length; a++) {
      x[a] = new IntVar(store, "x" + a, 0, 1);
    }
    Routes routes = new Routes(tails, heads, x);
    routes.setTimeWindows(
        new long[] {0, 0, 0}, new long[] {100, 5, 5}, new long[] {1, 1, 10, 10, 1, 1});
    CapacityCuts cuts = new CapacityCuts(routes);
    // 0-1-2-0 at 1/2: x(0,1) + x(0,2) = 1 enters {1, 2} once
    double[] value = {0.5, 0.5, 0.5, 0.5, 0.5, 0.5};
    List<CapacityCuts.Cut> found = cuts.separate(value, 10);
    assertThat(cuts.twoPathCuts()).isPositive();
    assertThat(found)
        .anyMatch(c -> c.entering() && c.bound() == 2 || !c.entering() && c.bound() == 0);
  }

  /** A path whose second customer closes before the first can be left is cut off. */
  @Test
  void infeasiblePathIsCut() {
    // depot 0, customers 1 and 2: 2 opens at 0 and closes at 3, 1 opens at 5, so 1-2 cannot be
    // followed although the arc is there; 0-1-2-0 at 1 violates x(0,1) + x(1,2) <= 1
    int[] tails = {0, 0, 1, 2, 1, 2};
    int[] heads = {1, 2, 2, 1, 0, 0};
    Store store = new Store();
    IntVar[] x = new IntVar[tails.length];
    for (int a = 0; a < x.length; a++) {
      x[a] = new IntVar(store, "x" + a, 0, 1);
    }
    Routes routes = new Routes(tails, heads, x);
    routes.setTimeWindows(
        new long[] {0, 5, 0}, new long[] {100, 20, 3}, new long[] {1, 1, 1, 1, 1, 1});
    CapacityCuts cuts = new CapacityCuts(routes);
    double[] value = {1, 0, 1, 0, 0, 1};
    List<CapacityCuts.Cut> found = cuts.separate(value, 10);
    assertThat(found).isNotEmpty();
    assertThat(cuts.pathCuts()).isPositive();
  }
}
