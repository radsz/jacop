/*
 * RouteNeighbourhoodsTest.java
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

package org.jacop.search.lns;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Routes;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** Tests of the route neighbourhoods of {@link AdaptiveLns} on a small two-index vrp model. */
class RouteNeighbourhoodsTest {

  // customers 1..6 on a line, in three pairs far apart; the depot 0 at position 0
  private static final int[] POSITION = {0, 1, 2, 10, 11, 20, 21};
  private static final int N = POSITION.length;
  private static final int CAPACITY = 2;
  // the solution: three routes 0-1-2-0, 0-3-4-0, 0-5-6-0
  private static final int[][] ROUTES = {{1, 2}, {3, 4}, {5, 6}};

  private final Store store = new Store();
  private final List<int[]> arcs = new ArrayList<>();
  private final List<IntVar> literals = new ArrayList<>();
  private final IntVar[] load = new IntVar[N];
  private final IntVar cost;

  RouteNeighbourhoodsTest() {
    for (int i = 0; i < N; i++) {
      for (int j = 0; j < N; j++) {
        if (i != j) {
          arcs.add(new int[] {i, j});
          literals.add(new IntVar(store, "x" + i + "_" + j, 0, 1));
        }
      }
    }
    for (int v = 1; v < N; v++) {
      load[v] = new IntVar(store, "u" + v, 1, CAPACITY);
      List<IntVar> in = new ArrayList<>();
      List<IntVar> out = new ArrayList<>();
      for (int k = 0; k < arcs.size(); k++) {
        if (arcs.get(k)[1] == v) {
          in.add(literals.get(k));
        }
        if (arcs.get(k)[0] == v) {
          out.add(literals.get(k));
        }
      }
      store.impose(new LinearInt(in.toArray(new IntVar[0]), ones(in.size()), "==", 1));
      store.impose(new LinearInt(out.toArray(new IntVar[0]), ones(out.size()), "==", 1));
    }
    // u[i] - u[j] + Q * x[i,j] <= Q - 1 between customers
    for (int k = 0; k < arcs.size(); k++) {
      int i = arcs.get(k)[0];
      int j = arcs.get(k)[1];
      if (i > 0 && j > 0) {
        store.impose(
            new LinearInt(
                new IntVar[] {load[i], load[j], literals.get(k)},
                new int[] {1, -1, CAPACITY},
                "<=",
                CAPACITY - 1));
      }
    }
    cost = new IntVar(store, "cost", 0, 10000);
    IntVar[] terms = new IntVar[arcs.size() + 1];
    int[] w = new int[arcs.size() + 1];
    for (int k = 0; k < arcs.size(); k++) {
      terms[k] = literals.get(k);
      w[k] = Math.abs(POSITION[arcs.get(k)[0]] - POSITION[arcs.get(k)[1]]);
    }
    terms[arcs.size()] = cost;
    w[arcs.size()] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    assertTrue(store.consistency());
  }

  private static int[] ones(int n) {
    int[] a = new int[n];
    java.util.Arrays.fill(a, 1);
    return a;
  }

  private Routes routes() {
    int[] tails = new int[arcs.size()];
    int[] heads = new int[arcs.size()];
    for (int k = 0; k < tails.length; k++) {
      tails[k] = arcs.get(k)[0];
      heads[k] = arcs.get(k)[1];
    }
    int[] demands = ones(N);
    demands[0] = 0;
    return new Routes(tails, heads, literals.toArray(new IntVar[0]), demands, CAPACITY);
  }

  private IntVar[] decisionVars() {
    List<IntVar> vs = new ArrayList<>(literals);
    for (int v = 1; v < N; v++) {
      vs.add(load[v]);
    }
    return vs.toArray(new IntVar[0]);
  }

  private boolean used(int i, int j) {
    for (int[] r : ROUTES) {
      int[] path = {0, r[0], r[1], 0};
      for (int p = 0; p + 1 < path.length; p++) {
        if (path[p] == i && path[p + 1] == j) {
          return true;
        }
      }
    }
    return false;
  }

  /** Records the three-route solution and puts the store back at the root. */
  private AdaptiveLns withSolution(AdaptiveLns lns) {
    int level = store.level;
    store.setLevel(level + 1);
    for (int k = 0; k < arcs.size(); k++) {
      IntVar x = literals.get(k);
      x.domain.inValue(store.level, x, used(arcs.get(k)[0], arcs.get(k)[1]) ? 1 : 0);
    }
    for (int[] r : ROUTES) {
      load[r[0]].domain.inValue(store.level, load[r[0]], 1);
      load[r[1]].domain.inValue(store.level, load[r[1]], 2);
    }
    assertTrue(store.consistency());
    assertEquals(2 * (2 + 11 + 21), cost.value());
    lns.solution();
    store.removeLevel(level + 1);
    store.setLevel(level);
    return lns;
  }

  @Test
  void routesGivenWithoutImposingAreFollowedFromTheDepot() {
    AdaptiveLns lns = new AdaptiveLns(store, decisionVars(), cost, new Random(1));
    assertTrue(lns.routings().isEmpty());
    lns.addRoutes(routes());
    lns.addRoutes(routes());
    assertEquals(1, lns.routings().size());
    withSolution(lns);
    RouteStructure r = lns.routings().get(0);
    assertEquals(6, r.customers());
    Set<String> found = new HashSet<>();
    for (int[] route : r.routes()) {
      found.add(java.util.Arrays.toString(route));
    }
    assertEquals(Set.of("[1, 2]", "[3, 4]", "[5, 6]"), found);
  }

  @Test
  void routeRemovalTakesWholeRoutesAndRelaxesTheirArcsAndLoads() {
    store.impose(routes());
    assertTrue(store.consistency());
    AdaptiveLns lns = withSolution(new AdaptiveLns(store, decisionVars(), cost, new Random(2)));
    assertEquals(1, lns.routings().size());
    RouteStructure r = lns.routings().get(0);
    Random random = new Random(3);
    IntVar[] vars = lns.variables();
    for (int t = 0; t < 50; t++) {
      boolean[] removed = r.routeRemoval(0.2, random);
      int routesRemoved = 0;
      for (int[] route : ROUTES) {
        assertEquals(removed[route[0]], removed[route[1]], "a route is removed whole");
        if (removed[route[0]]) {
          routesRemoved++;
        }
      }
      assertEquals(2, routesRemoved);
      boolean[] relax = new boolean[vars.length];
      r.relax(removed, relax);
      for (int k = 0; k < arcs.size(); k++) {
        int i = arcs.get(k)[0];
        int j = arcs.get(k)[1];
        assertEquals(removed[i] || removed[j], relax[k], "arc " + i + "-" + j);
      }
      for (int v = 1; v < N; v++) {
        // the loads follow literals.size() in the variables
        assertEquals(removed[v], relax[arcs.size() + v - 1], "load of " + v);
      }
    }
  }

  @Test
  void relatedRemovalPrefersCloseCustomers() {
    AdaptiveLns lns = new AdaptiveLns(store, decisionVars(), cost, new Random(4));
    lns.addRoutes(routes());
    withSolution(lns);
    RouteStructure r = lns.routings().get(0);
    Random random = new Random(5);
    int partners = 0;
    for (int t = 0; t < 100; t++) {
      boolean[] removed = r.relatedRemoval(2.0 / 6, random);
      int count = 0;
      for (boolean b : removed) {
        count += b ? 1 : 0;
      }
      assertEquals(2, count);
      assertFalse(removed[0]);
      for (int[] route : ROUTES) {
        if (removed[route[0]] && removed[route[1]]) {
          partners++;
        }
      }
      boolean[] relax = new boolean[lns.variables().length];
      r.relax(removed, relax);
      for (int[] route : ROUTES) {
        // the loads of the routes touched are relaxed
        boolean touched = removed[route[0]] || removed[route[1]];
        assertEquals(touched, relax[arcs.size() + route[0] - 1]);
        assertEquals(touched, relax[arcs.size() + route[1] - 1]);
      }
    }
    // the nearest customer is a distance 1 away, the others at least 8: rank 0 of 10 for y^6 < 0.1
    assertTrue(partners > 55, "pairs removed together: " + partners);
  }

  @Test
  void adaptiveLnsUsesTheRouteKinds() {
    AdaptiveLns lns = new AdaptiveLns(store, decisionVars(), cost, new Random(6));
    lns.addRoutes(routes());
    withSolution(lns);
    int level = store.level;
    for (int k = 0; k < 300; k++) {
      int[] fixed = lns.neighbourhood();
      assertEquals(level, store.level);
      for (int i : fixed) {
        assertTrue(lns.variables()[i].domain.contains(lns.value(i)));
      }
      lns.outcome(k % 4 == 0 ? AdaptiveLns.Outcome.IMPROVED : AdaptiveLns.Outcome.LIMIT);
    }
    assertFalse(lns.statistics().contains("ROUTES 0/"), lns.statistics());
    assertFalse(lns.statistics().contains("RELATED 0/"), lns.statistics());
  }
}
