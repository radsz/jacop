/*
 * RouteNeighbourhoods.java
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
import org.jacop.constraints.Routes;
import org.jacop.core.IntVar;

/**
 * Ruin-and-recreate neighbourhoods over the vehicle routes of a {@link Routes} structure: the
 * customers of whole routes (route removal), or customers related to each other (Shaw removal,
 * related by the cost of the arcs between them in the objective), are removed from the best
 * solution and the run reinserts them.
 *
 * <p>Removing a set S of customers relaxes the literal of every arc with an end in S, and the other
 * variables of the customers of every route that S touches (the loads of a load-based model, which
 * change along a route when its customers change). Arcs between customers outside S keep their
 * values, so the parts of the routes outside S stay and the run joins them again through the
 * customers of S, as in the routing neighbourhoods of CP-SAT.
 *
 * <p>The variables that belong to a customer are found in the constraint graph: a variable that is
 * not an arc belongs to the node that ends at least half of the arcs it shares constraints with
 * (the load u[i] of the rows {@code u[i] - u[j] + c * x[i,j] <= r} belongs to i).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class RouteNeighbourhoods {

  // the randomness of Shaw removal: the rank of the next customer is size * y^SHAW for y in [0, 1)
  private static final double SHAW = 6;
  // and of the next route of route removal
  private static final double ROUTE_RANDOMNESS = 3;

  private final int n;
  private final int[] tails;
  private final int[] heads;
  // the index of each arc's literal among the variables of the neighbourhoods, or -1
  private final int[] arcVar;
  private final IntVar[] literals;
  // the cost of each arc in the objective, 0 when unknown
  private final long[] arcCost;
  private final boolean costs;
  // arcs at each node (both directions), other than self loops
  private final int[][] arcsAt;
  // the variables other than arcs that belong to each node
  private final int[][] owned;
  // the nodes other than the depot that have arcs
  private final int[] customers;

  // the values of the literals in the best solution
  private final boolean[] used;

  // the routes of the best solution: the route of each node (-1: none) and the nodes of each route
  private int[] routeOf;
  private int[][] routes = new int[0][];

  /**
   * Builds the neighbourhoods of one routing structure.
   *
   * @param routes the structure; its node 0 is the depot.
   * @param literalNode the node of the graph of each literal of routes, or -1.
   * @param termCost the cost in the objective of each node of the graph (0 when not a term).
   * @param conVars the variable nodes of each constraint of the graph.
   * @param varCons the constraints of each variable node.
   * @param varCount the number of variables of the neighbourhoods (the first nodes of the graph).
   */
  RouteNeighbourhoods(
      Routes routes,
      int[] literalNode,
      long[] termCost,
      int[][] conVars,
      int[][] varCons,
      int varCount) {
    this.tails = routes.tails.clone();
    this.heads = routes.heads.clone();
    this.literals = routes.literals.clone();
    int m = tails.length;
    int nodes = 0;
    for (int k = 0; k < m; k++) {
      nodes = Math.max(nodes, Math.max(tails[k], heads[k]) + 1);
    }
    this.n = nodes;
    arcVar = new int[m];
    arcCost = new long[m];
    boolean anyCost = false;
    for (int k = 0; k < m; k++) {
      int node = literalNode[k];
      arcVar[k] = node >= 0 && node < varCount ? node : -1;
      arcCost[k] = node >= 0 ? termCost[node] : 0;
      anyCost |= arcCost[k] != 0 && tails[k] != heads[k];
    }
    costs = anyCost;
    int[] degree = new int[n];
    for (int k = 0; k < m; k++) {
      if (tails[k] != heads[k]) {
        degree[tails[k]]++;
        degree[heads[k]]++;
      }
    }
    arcsAt = new int[n][];
    for (int v = 0; v < n; v++) {
      arcsAt[v] = new int[degree[v]];
    }
    int[] fill = new int[n];
    for (int k = 0; k < m; k++) {
      if (tails[k] != heads[k]) {
        arcsAt[tails[k]][fill[tails[k]]++] = k;
        arcsAt[heads[k]][fill[heads[k]]++] = k;
      }
    }
    List<Integer> cs = new ArrayList<>();
    for (int v = 1; v < n; v++) {
      if (degree[v] > 0) {
        cs.add(v);
      }
    }
    customers = cs.stream().mapToInt(Integer::intValue).toArray();
    owned = owners(literalNode, conVars, varCons, varCount);
    used = new boolean[m];
    routeOf = new int[n];
    Arrays.fill(routeOf, -1);
  }

  /** The variables other than arcs that belong to each node. */
  private int[][] owners(int[] literalNode, int[][] conVars, int[][] varCons, int varCount) {
    int[] arcOfNode = new int[varCons.length];
    Arrays.fill(arcOfNode, -1);
    for (int k = 0; k < literalNode.length; k++) {
      if (literalNode[k] >= 0) {
        arcOfNode[literalNode[k]] = k;
      }
    }
    List<List<Integer>> lists = new ArrayList<>();
    for (int v = 0; v < n; v++) {
      lists.add(new ArrayList<>());
    }
    int[] count = new int[n];
    int[] touched = new int[n];
    for (int x = 0; x < varCount; x++) {
      if (arcOfNode[x] >= 0) {
        continue;
      }
      int arcs = 0;
      int t = 0;
      for (int c : varCons[x]) {
        for (int u : conVars[c]) {
          int k = arcOfNode[u];
          if (k < 0) {
            continue;
          }
          arcs++;
          if (count[tails[k]]++ == 0) {
            touched[t++] = tails[k];
          }
          if (heads[k] != tails[k] && count[heads[k]]++ == 0) {
            touched[t++] = heads[k];
          }
        }
      }
      int best = -1;
      for (int j = 0; j < t; j++) {
        int v = touched[j];
        if (best < 0 || count[v] > count[best]) {
          best = v;
        }
      }
      if (best >= 0 && 2 * count[best] >= arcs) {
        lists.get(best).add(x);
      }
      for (int j = 0; j < t; j++) {
        count[touched[j]] = 0;
      }
    }
    int[][] result = new int[n][];
    for (int v = 0; v < n; v++) {
      result[v] = lists.get(v).stream().mapToInt(Integer::intValue).toArray();
    }
    return result;
  }

  /**
   * Returns whether this structure has the same literals as the given routes.
   *
   * @param other the routes.
   * @return true when the literals are the same variables, in the same order.
   */
  boolean sameAs(Routes other) {
    if (other.literals.length != literals.length) {
      return false;
    }
    for (int k = 0; k < literals.length; k++) {
      if (other.literals[k] != literals[k]) {
        return false;
      }
    }
    return true;
  }

  /**
   * Returns the number of customers.
   *
   * @return the nodes other than the depot that have arcs.
   */
  int customers() {
    return customers.length;
  }

  /** Records the routes of the best solution; the literals are all fixed. */
  void solution() {
    for (int k = 0; k < literals.length; k++) {
      used[k] = literals[k].singleton() && literals[k].value() == 1;
    }
    routes = null;
  }

  /** The routes of the best solution, followed from the depot along the arcs at 1. */
  private void readRoutes() {
    if (routes != null) {
      return;
    }
    int[] next = new int[n];
    Arrays.fill(next, -1);
    List<Integer> starts = new ArrayList<>();
    for (int k = 0; k < tails.length; k++) {
      if (used[k] && tails[k] != heads[k]) {
        if (tails[k] == 0) {
          starts.add(heads[k]);
        } else {
          next[tails[k]] = heads[k];
        }
      }
    }
    Arrays.fill(routeOf, -1);
    List<int[]> rs = new ArrayList<>();
    for (int s : starts) {
      List<Integer> route = new ArrayList<>();
      int v = s;
      // a node is visited once, so a broken solution cannot loop
      while (v > 0 && routeOf[v] < 0) {
        routeOf[v] = rs.size();
        route.add(v);
        v = next[v];
      }
      if (!route.isEmpty()) {
        rs.add(route.stream().mapToInt(Integer::intValue).toArray());
      }
    }
    routes = rs.toArray(new int[0][]);
  }

  /**
   * Route removal: the customers of a random route and of the routes nearest to it (by the cheapest
   * arc from the customers removed so far), at least two routes when there are two.
   *
   * @param share the share of the customers to remove.
   * @param random the source of randomness.
   * @return the removed customers.
   */
  boolean[] routeRemoval(double share, Random random) {
    readRoutes();
    boolean[] removed = new boolean[n];
    if (routes.length == 0) {
      return removed;
    }
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
      if (count >= target && (routesChosen >= 2 || routes.length < 2)) {
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
    if (costs) {
      for (int[] route : routes) {
        for (int v : route) {
          if (!removed[v]) {
            continue;
          }
          for (int k : arcsAt[v]) {
            int w = tails[k] == v ? heads[k] : tails[k];
            int rw = w > 0 ? routeOf[w] : -1;
            if (rw >= 0 && !chosen[rw]) {
              distance[rw] = Math.min(distance[rw], arcCost[k]);
            }
          }
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
    if (!costs || distance[open.get(0)] == Long.MAX_VALUE) {
      return open.get(random.nextInt(open.size()));
    }
    return open.get(rank(open.size(), ROUTE_RANDOMNESS, random));
  }

  /**
   * Shaw removal: from a random customer, the customers related to those removed so far, each next
   * one near a random removed customer (by the cost of the arc between them) or, without costs,
   * next to it on its route.
   *
   * @param share the share of the customers to remove.
   * @param random the source of randomness.
   * @return the removed customers.
   */
  boolean[] relatedRemoval(double share, Random random) {
    readRoutes();
    boolean[] removed = new boolean[n];
    int target = Math.max(2, (int) Math.round(share * customers.length));
    int[] list = new int[customers.length];
    int count = 0;
    int seed = customers[random.nextInt(customers.length)];
    removed[seed] = true;
    list[count++] = seed;
    // the candidates near a removed customer, each once at the cheaper of its two arcs
    long[] distance = new long[n];
    int[] position = new int[n];
    Arrays.fill(position, -1);
    Integer[] candidates = new Integer[n];
    while (count < target && count < customers.length) {
      int from = list[random.nextInt(count)];
      int size = 0;
      for (int k : arcsAt[from]) {
        int w = tails[k] == from ? heads[k] : tails[k];
        if (w > 0 && !removed[w] && (costs || used[k])) {
          if (position[w] < 0) {
            position[w] = size;
            candidates[size++] = w;
            distance[w] = arcCost[k];
          } else {
            distance[w] = Math.min(distance[w], arcCost[k]);
          }
        }
      }
      int pick;
      if (size == 0) {
        pick = randomCustomer(removed, random);
      } else {
        Arrays.sort(candidates, 0, size, (a, b) -> Long.compare(distance[a], distance[b]));
        pick = candidates[rank(size, SHAW, random)];
        for (int j = 0; j < size; j++) {
          position[candidates[j]] = -1;
        }
      }
      if (pick < 0) {
        break;
      }
      if (!removed[pick]) {
        removed[pick] = true;
        list[count++] = pick;
      }
    }
    return removed;
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

  /**
   * Marks the variables that removing the customers relaxes: the arcs with an end among them, and
   * the variables of the customers of the routes they are on and of the depot.
   *
   * @param removed the removed customers.
   * @param relax the variables to relax, marked here.
   */
  void relax(boolean[] removed, boolean[] relax) {
    readRoutes();
    for (int k = 0; k < tails.length; k++) {
      if (arcVar[k] >= 0 && (removed[tails[k]] || removed[heads[k]])) {
        relax[arcVar[k]] = true;
      }
    }
    boolean[] touched = new boolean[routes.length];
    for (int v = 1; v < n; v++) {
      if (removed[v]) {
        mark(owned[v], relax);
        if (routeOf[v] >= 0) {
          touched[routeOf[v]] = true;
        }
      }
    }
    for (int r = 0; r < routes.length; r++) {
      if (touched[r]) {
        for (int v : routes[r]) {
          mark(owned[v], relax);
        }
      }
    }
    mark(owned[0], relax);
  }

  private static void mark(int[] vars, boolean[] relax) {
    for (int x : vars) {
      relax[x] = true;
    }
  }

  /**
   * The routes of the best solution, for tests.
   *
   * @return the routes, each the list of its customers in order.
   */
  int[][] routes() {
    readRoutes();
    return routes.clone();
  }
}
