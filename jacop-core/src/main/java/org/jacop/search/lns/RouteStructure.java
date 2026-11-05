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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

/**
 * The vehicle routes of a model, as large neighbourhood search sees them: customers on routes in
 * the best solution, the customers near each one (by the cost of travelling between them, nearest
 * first), and how removing customers relaxes the variables. Route removal and Shaw removal are
 * defined here; {@link RouteNeighbourhoods} (0/1 arcs of a {@link org.jacop.constraints.Routes})
 * and {@link SuccessorRoutes} (successor variables of a circuit) read the routes from the model.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
abstract class RouteStructure {

  // the randomness of Shaw removal: the rank of the next customer is size * y^SHAW for y in [0, 1)
  private static final double SHAW = 6;
  // and of the next route of route removal
  private static final double ROUTE_RANDOMNESS = 3;

  /** The number of nodes. */
  final int n;

  /** The customers: the nodes that removal may take. */
  int[] customers = new int[0];

  /** The nodes near each node, nearest first, and the cost to each; empty without costs. */
  int[][] near;

  /** The costs of {@link #near}. */
  long[][] nearCost;

  /** The route of each node in the best solution (-1: none), set by {@link #readRoutes()}. */
  int[] routeOf;

  /** The customers of each route in the best solution, in order; null until read. */
  int[][] routes;

  RouteStructure(int n) {
    this.n = n;
    near = new int[n][0];
    nearCost = new long[n][0];
    routeOf = new int[n];
    Arrays.fill(routeOf, -1);
  }

  /** Records the routes of the best solution, while the store holds it. */
  abstract void solution();

  /** Fills {@link #routes} and {@link #routeOf} from the best solution. */
  abstract void readRoutes();

  /**
   * Marks the variables that removing the customers relaxes.
   *
   * @param removed the removed nodes.
   * @param relax the variables of the neighbourhoods to relax, marked here.
   */
  abstract void relax(boolean[] removed, boolean[] relax);

  /**
   * Returns the number of customers.
   *
   * @return the nodes that removal may take.
   */
  int customers() {
    return customers.length;
  }

  /**
   * Returns the routes of the best solution, for tests.
   *
   * @return the routes, each the list of its customers in order.
   */
  int[][] routes() {
    readRoutes();
    return routes.clone();
  }

  /** Sets the near lists from the costs of travelling between nodes, keeping the cheapest. */
  final void setNear(List<List<long[]>> costs, int keep) {
    for (int v = 0; v < n; v++) {
      List<long[]> c = new ArrayList<>(costs.get(v));
      c.sort((a, b) -> Long.compare(a[1], b[1]));
      int m = Math.min(keep, c.size());
      near[v] = new int[m];
      nearCost[v] = new long[m];
      for (int j = 0; j < m; j++) {
        near[v][j] = (int) c.get(j)[0];
        nearCost[v][j] = c.get(j)[1];
      }
    }
  }

  private boolean hasCosts() {
    for (int[] nv : near) {
      if (nv.length > 0) {
        return true;
      }
    }
    return false;
  }

  /**
   * Route removal: the customers of a random route and of the routes nearest to it (by the cheapest
   * cost from the customers removed so far), at least two routes when there are two. With a single
   * route it is Shaw removal.
   *
   * @param share the share of the customers to remove.
   * @param random the source of randomness.
   * @return the removed customers.
   */
  boolean[] routeRemoval(double share, Random random) {
    readRoutes();
    if (routes.length < 2) {
      return relatedRemoval(share, random);
    }
    boolean[] removed = new boolean[n];
    int target = Math.max(2, (int) Math.round(share * customers.length));
    boolean[] chosen = new boolean[routes.length];
    int count = 0;
    int routesChosen = 0;
    int r = random.nextInt(routes.length);
    while (r >= 0) {
      chosen[r] = true;
      routesChosen++;
      for (int v : routes[r]) {
        removed[v] = true;
        count++;
      }
      if (count >= target && routesChosen >= 2) {
        break;
      }
      r = nextRoute(removed, chosen, random);
    }
    return removed;
  }

  /** The route to remove next: a route near the removed customers, or a random one. */
  private int nextRoute(boolean[] removed, boolean[] chosen, Random random) {
    long[] distance = new long[routes.length];
    Arrays.fill(distance, Long.MAX_VALUE);
    for (int v = 0; v < n; v++) {
      if (!removed[v]) {
        continue;
      }
      for (int j = 0; j < near[v].length; j++) {
        int rw = routeOf[near[v][j]];
        if (rw >= 0 && !chosen[rw]) {
          distance[rw] = Math.min(distance[rw], nearCost[v][j]);
        }
      }
    }
    List<Integer> open = new ArrayList<>();
    for (int r = 0; r < routes.length; r++) {
      if (!chosen[r]) {
        open.add(r);
      }
    }
    if (open.isEmpty()) {
      return -1;
    }
    open.sort((a, b) -> Long.compare(distance[a], distance[b]));
    if (distance[open.get(0)] == Long.MAX_VALUE) {
      return open.get(random.nextInt(open.size()));
    }
    return open.get(rank(open.size(), ROUTE_RANDOMNESS, random));
  }

  /**
   * Shaw removal: from a random customer, the customers related to those removed so far, each next
   * one near a random removed customer (by cost) or, without costs, next to it on its route.
   *
   * @param share the share of the customers to remove.
   * @param random the source of randomness.
   * @return the removed customers.
   */
  boolean[] relatedRemoval(double share, Random random) {
    readRoutes();
    boolean[] customer = new boolean[n];
    for (int v : customers) {
      customer[v] = true;
    }
    boolean costs = hasCosts();
    int[] position = costs ? null : positions();
    boolean[] removed = new boolean[n];
    int target = Math.max(2, (int) Math.round(share * customers.length));
    int[] list = new int[customers.length];
    int count = 0;
    int seed = customers[random.nextInt(customers.length)];
    removed[seed] = true;
    list[count++] = seed;
    int[] candidates = new int[n];
    while (count < target && count < customers.length) {
      int from = list[random.nextInt(count)];
      int size = 0;
      if (costs) {
        for (int w : near[from]) {
          if (customer[w] && !removed[w]) {
            candidates[size++] = w;
          }
        }
      } else if (routeOf[from] >= 0) {
        int[] route = routes[routeOf[from]];
        int p = position[from];
        for (int q : new int[] {p - 1, p + 1}) {
          if (q >= 0 && q < route.length && !removed[route[q]]) {
            candidates[size++] = route[q];
          }
        }
      }
      int pick = size == 0 ? randomCustomer(removed, random) : candidates[rank(size, SHAW, random)];
      if (pick < 0) {
        break;
      }
      removed[pick] = true;
      list[count++] = pick;
    }
    return removed;
  }

  /** The position of each node on its route. */
  private int[] positions() {
    int[] position = new int[n];
    for (int[] route : routes) {
      for (int p = 0; p < route.length; p++) {
        position[route[p]] = p;
      }
    }
    return position;
  }

  private int randomCustomer(boolean[] removed, Random random) {
    int start = random.nextInt(customers.length);
    for (int j = 0; j < customers.length; j++) {
      int v = customers[(start + j) % customers.length];
      if (!removed[v]) {
        return v;
      }
    }
    return -1;
  }

  private static int rank(int size, double power, Random random) {
    return Math.min(size - 1, (int) Math.floor(Math.pow(random.nextDouble(), power) * size));
  }
}
