/*
 * RouteStructure.java
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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** Tests of the route neighbourhoods of {@link AdaptiveLns} over a giant tour (cvrp style). */
class SuccessorRoutesTest {

  // customers 0..5 on a line in three pairs far apart; vehicles start at 6..8 and end at 9..11
  private static final int[] POSITION = {1, 2, 10, 11, 20, 21};
  private static final int C = POSITION.length;
  private static final int V = 3;
  private static final int N = C + 2 * V;
  // the solution: 6-0-1-9, 7-2-3-10, 8-4-5-11, and 9-7, 10-8, 11-6
  private static final int[] NEXT = {1, 9, 3, 10, 5, 11, 0, 2, 4, 7, 8, 6};

  private final Store store = new Store();
  private final IntVar[] next = new IntVar[N];
  private final IntVar[] distance = new IntVar[N];
  private final IntVar[] load = new IntVar[N];
  private final IntVar cost;

  SuccessorRoutesTest() {
    for (int v = 0; v < N; v++) {
      next[v] = new IntVar(store, "next" + v, 1, N);
      load[v] = new IntVar(store, "load" + v, 0, N);
    }
    store.impose(new Circuit(next));
    // the end depot of each vehicle is followed by the start depot of the next
    for (int k = 0; k < V; k++) {
      store.impose(new XeqC(next[C + V + k], C + (k + 1) % V + 1));
    }
    for (int v = 0; v < N; v++) {
      int[] row = new int[N];
      for (int w = 0; w < N; w++) {
        row[w] = Math.abs(position(v) - position(w));
      }
      distance[v] = new IntVar(store, "d" + v, 0, 100);
      store.impose(new ElementInteger(next[v], row, distance[v], 0));
    }
    cost = new IntVar(store, "cost", 0, 10000);
    IntVar[] terms = Arrays.copyOf(distance, N + 1);
    int[] w = new int[N + 1];
    Arrays.fill(w, 1);
    terms[N] = cost;
    w[N] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    assertTrue(store.consistency());
  }

  private static int position(int v) {
    return v < C ? POSITION[v] : 0;
  }

  private IntVar[] decisionVars() {
    IntVar[] vs = Arrays.copyOf(next, 2 * N);
    System.arraycopy(load, 0, vs, N, N);
    return vs;
  }

  private AdaptiveLns withSolution(AdaptiveLns lns) {
    int level = store.level;
    store.setLevel(level + 1);
    for (int v = 0; v < N; v++) {
      next[v].domain.inValue(store.level, next[v], NEXT[v] + 1);
      load[v].domain.inValue(store.level, load[v], v);
    }
    assertTrue(store.consistency());
    lns.solution();
    store.removeLevel(level + 1);
    store.setLevel(level);
    return lns;
  }

  @Test
  void depotLinksSplitTheTourIntoRoutes() {
    AdaptiveLns lns = withSolution(new AdaptiveLns(store, decisionVars(), cost, new Random(1)));
    assertEquals(1, lns.routings().size());
    RouteStructure r = lns.routings().get(0);
    assertEquals(C, r.customerCount());
    Set<String> found = new HashSet<>();
    for (int[] route : r.bestRoutes()) {
      found.add(Arrays.toString(route));
    }
    assertEquals(Set.of("[0, 1]", "[2, 3]", "[4, 5]"), found);
  }

  @Test
  void routeRemovalRelaxesTheSuccessorsAroundTheRemovedCustomers() {
    AdaptiveLns lns = withSolution(new AdaptiveLns(store, decisionVars(), cost, new Random(2)));
    RouteStructure r = lns.routings().get(0);
    Random random = new Random(3);
    for (int t = 0; t < 50; t++) {
      boolean[] removed = r.routeRemoval(0.2, random);
      int routes = 0;
      for (int k = 0; k < V; k++) {
        assertEquals(removed[2 * k], removed[2 * k + 1], "a route is removed whole");
        routes += removed[2 * k] ? 1 : 0;
      }
      assertEquals(2, routes);
      boolean[] relax = new boolean[2 * N];
      r.relax(removed, relax);
      for (int v = 0; v < N; v++) {
        // its successor is free when v is removed or comes before a removed customer
        assertEquals(removed[v] || removed[NEXT[v]], relax[v], "next of " + v);
      }
    }
  }

  @Test
  void depotLinksOfEveryRouteCanBeFreed() {
    AdaptiveLns lns = withSolution(new AdaptiveLns(store, decisionVars(), cost, new Random(2)));
    SuccessorRoutes r = (SuccessorRoutes) lns.routings().get(0);
    boolean[] relax = new boolean[2 * N];
    r.relaxDepotLinks(relax);
    // the start depots and the last customer of each route; the links inside a route stay
    for (int v = 0; v < C + V; v++) {
      boolean link = v >= C || NEXT[v] >= C;
      assertEquals(link, relax[v], "next of " + v);
    }
  }

  @Test
  void relatedRemovalPrefersCloseCustomers() {
    AdaptiveLns lns = withSolution(new AdaptiveLns(store, decisionVars(), cost, new Random(4)));
    RouteStructure r = lns.routings().get(0);
    Random random = new Random(5);
    int partners = 0;
    for (int t = 0; t < 100; t++) {
      boolean[] removed = r.relatedRemoval(2.0 / C, random);
      int count = 0;
      for (int v = 0; v < N; v++) {
        count += removed[v] ? 1 : 0;
        assertFalse(removed[v] && v >= C, "a depot is removed");
      }
      assertEquals(2, count);
      for (int k = 0; k < V; k++) {
        partners += removed[2 * k] && removed[2 * k + 1] ? 1 : 0;
      }
    }
    assertTrue(partners > 55, "pairs removed together: " + partners);
  }

  @Test
  void neighbourhoodsFixOnlySuccessorsOutsideTheRemovedCustomers() {
    AdaptiveLns lns = withSolution(new AdaptiveLns(store, decisionVars(), cost, new Random(6)));
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

  @Test
  void aTourWithoutDepotsIsOneRoute() {
    Store s = new Store();
    IntVar[] x = new IntVar[6];
    for (int v = 0; v < x.length; v++) {
      x[v] = new IntVar(s, "x" + v, 1, x.length);
    }
    s.impose(new Circuit(x));
    IntVar c = new IntVar(s, "c", 0, 100);
    s.impose(new LinearInt(x, new int[] {1, 1, 1, 1, 1, 1}, "==", c));
    assertTrue(s.consistency());
    AdaptiveLns lns = new AdaptiveLns(s, x, c, new Random(7));
    s.setLevel(s.level + 1);
    for (int v = 0; v < x.length; v++) {
      x[v].domain.inValue(s.level, x[v], (v + 1) % x.length + 1);
    }
    assertTrue(s.consistency());
    lns.solution();
    s.removeLevel(s.level);
    s.setLevel(s.level - 1);
    RouteStructure r = lns.routings().get(0);
    assertEquals(1, r.bestRoutes().length);
    assertEquals(6, r.bestRoutes()[0].length);
    // one route: route removal falls back to removing related customers
    boolean[] removed = r.routeRemoval(0.4, new Random(8));
    int count = 0;
    for (boolean b : removed) {
      count += b ? 1 : 0;
    }
    assertEquals(2, count);
  }

  /**
   * A model numbered from 0 (XCSP VRP_LC through MiniZinc) posts its subcircuit on copies x[v] =
   * y[v] + 1 of its successors y: the routes must still be found over y, with the costs of the
   * elements on y and the pickup and delivery pairs of the vehicle labels.
   */
  @Test
  void aSubcircuitOnShiftedCopiesOfTheSuccessorsHasRoutes() {
    Store s = new Store();
    IntVar[] y = new IntVar[N];
    IntVar[] x = new IntVar[N];
    IntVar[] veh = new IntVar[N];
    IntVar[] d = new IntVar[N];
    for (int v = 0; v < N; v++) {
      y[v] = new IntVar(s, "succ" + v, 0, N - 1);
      x[v] = new IntVar(s, "x" + v, 1, N);
      veh[v] = new IntVar(s, "veh" + v, 0, V - 1);
      s.impose(new XplusCeqZ(y[v], 1, x[v]));
    }
    s.impose(new Subcircuit(x));
    for (int k = 0; k < V; k++) {
      s.impose(new XeqC(y[C + V + k], C + (k + 1) % V));
    }
    for (int v = 0; v < N; v++) {
      int[] row = new int[N];
      for (int w = 0; w < N; w++) {
        row[w] = Math.abs(position(v) - position(w));
      }
      d[v] = new IntVar(s, "d" + v, 0, 100);
      // the lists are numbered from 0: y = 0 reads the first value
      s.impose(new ElementInteger(y[v], row, d[v], -1));
      if (v < C + V) {
        // the vehicle along its route; an end depot is followed by the next vehicle's start
        s.impose(new ElementVariable(y[v], veh, veh[v], -1));
      }
    }
    // customers 0 and 1 share a vehicle (a pickup and its delivery)
    s.impose(new XeqY(veh[0], veh[1]));
    IntVar c = new IntVar(s, "cost", 0, 10000);
    IntVar[] terms = Arrays.copyOf(d, N + 1);
    int[] w = new int[N + 1];
    Arrays.fill(w, 1);
    terms[N] = c;
    w[N] = -1;
    s.impose(new LinearInt(terms, w, "==", 0));
    assertTrue(s.consistency());
    IntVar[] decisions = Arrays.copyOf(y, 2 * N);
    System.arraycopy(veh, 0, decisions, N, N);
    AdaptiveLns lns = new AdaptiveLns(s, decisions, c, new Random(9));
    int level = s.level;
    s.setLevel(level + 1);
    for (int v = 0; v < N; v++) {
      y[v].domain.inValue(s.level, y[v], NEXT[v]);
      // vehicle k starts at C + k, visits 2k and 2k + 1 and ends at C + V + k
      int k = v < C ? v / 2 : (v - C) % V;
      veh[v].domain.inValue(s.level, veh[v], k);
    }
    assertTrue(s.consistency());
    lns.solution();
    s.removeLevel(level + 1);
    s.setLevel(level);

    assertEquals(1, lns.routings().size());
    RouteStructure r = lns.routings().get(0);
    assertEquals(C, r.customerCount());
    Set<String> found = new HashSet<>();
    for (int[] route : r.bestRoutes()) {
      found.add(Arrays.toString(route));
    }
    assertEquals(Set.of("[0, 1]", "[2, 3]", "[4, 5]"), found);
    // the costs come from the elements on y: customer 1 is nearest to 0
    assertEquals(1, r.near[0][0]);
    assertEquals("[1]", Arrays.toString(r.partners[0]));
    assertEquals("[0]", Arrays.toString(r.partners[1]));
    assertEquals(0, r.partners[2].length);
    // removing a customer relaxes the successors y around it
    boolean[] removed = new boolean[N];
    removed[2] = true;
    boolean[] relax = new boolean[2 * N];
    r.relax(removed, relax);
    for (int v = 0; v < N; v++) {
      assertEquals(v == 2 || NEXT[v] == 2, relax[v], "succ of " + v);
    }
    // Shaw removal takes the partner with the customer
    Random random = new Random(10);
    for (int t = 0; t < 50; t++) {
      boolean[] shaw = r.relatedRemoval(1.0 / C, random);
      assertEquals(shaw[0], shaw[1], "a pair is removed together");
    }
  }
}
