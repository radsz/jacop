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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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
final class RouteNeighbourhoods extends RouteStructure {

  private final int[] tails;
  private final int[] heads;
  // the index of each arc's literal among the variables of the neighbourhoods, or -1
  private final int[] arcVar;
  private final IntVar[] literals;
  // the cost of each arc in the objective, 0 when unknown
  private final long[] arcCost;
  // arcs at each node (both directions), other than self loops
  private final int[][] arcsAt;
  // the variables other than arcs that belong to each node
  private final int[][] owned;

  // the values of the literals in the best solution
  private final boolean[] used;

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
    super(nodeCount(routes));
    this.tails = routes.tails.clone();
    this.heads = routes.heads.clone();
    this.literals = routes.literals.clone();
    int m = tails.length;
    arcVar = new int[m];
    arcCost = new long[m];
    boolean anyCost = false;
    for (int k = 0; k < m; k++) {
      int node = literalNode[k];
      arcVar[k] = node >= 0 && node < varCount ? node : -1;
      arcCost[k] = node >= 0 ? termCost[node] : 0;
      anyCost |= arcCost[k] != 0 && tails[k] != heads[k];
    }
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
    if (anyCost) {
      // each neighbour once, at the cheaper of the two arcs
      List<List<long[]>> costs = new ArrayList<>();
      for (int v = 0; v < n; v++) {
        Map<Integer, Long> best = new HashMap<>();
        for (int k : arcsAt[v]) {
          int w = tails[k] == v ? heads[k] : tails[k];
          best.merge(w, arcCost[k], Math::min);
        }
        List<long[]> c = new ArrayList<>();
        best.forEach((w, cost) -> c.add(new long[] {w, cost}));
        costs.add(c);
      }
      setNear(costs, Integer.MAX_VALUE);
    }
  }

  private static int nodeCount(Routes routes) {
    int nodes = 0;
    for (int k = 0; k < routes.tails.length; k++) {
      nodes = Math.max(nodes, Math.max(routes.tails[k], routes.heads[k]) + 1);
    }
    return nodes;
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

  /** Records the routes of the best solution; the literals are all fixed. */
  @Override
  void solution() {
    for (int k = 0; k < literals.length; k++) {
      used[k] = literals[k].singleton() && literals[k].value() == 1;
    }
    routes = null;
  }

  /** The routes of the best solution, followed from the depot along the arcs at 1. */
  @Override
  void readRoutes() {
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
   * Marks the variables that removing the customers relaxes: the arcs with an end among them, and
   * the variables of the customers of the routes they are on and of the depot.
   *
   * @param removed the removed customers.
   * @param relax the variables to relax, marked here.
   */
  @Override
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
}
