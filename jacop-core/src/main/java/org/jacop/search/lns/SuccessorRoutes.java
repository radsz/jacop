/*
 * SuccessorRoutes.java
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
import org.jacop.core.IntVar;

/**
 * Vehicle routes written as the successor variables of a circuit (a giant tour): node i is followed
 * by node x[i]. The links fixed at the root, such as the end depot of one vehicle followed by the
 * start depot of the next, split the tour into routes; their nodes are the depots and the other
 * nodes are the customers. Without fixed links the whole tour is one route. With a subcircuit, a
 * node that is its own successor is a customer on no route.
 *
 * <p>Removing a set S of customers relaxes the successor of every node of S and of the node before
 * each of them, so the parts of the routes outside S stay and the run joins them again through S.
 * The neighbourhoods relax the other variables of the model themselves (loads, times and vehicles
 * follow from the successors).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SuccessorRoutes extends RouteStructure {

  private final IntVar[] successors;
  private final int offset;
  // the index of each successor among the variables of the neighbourhoods, or -1
  private final int[] varIndex;
  private final boolean[] depot;
  private final int[] next;

  /**
   * Builds the routes of one circuit.
   *
   * @param successors the successor variables, node i (from 0) followed by node x[i] - offset.
   * @param offset the number of the first node.
   * @param varIndex the index of each successor among the variables of the neighbourhoods, or -1.
   * @param cost the cost of travelling from each node to each other node, or null when unknown; a
   *     row may be null.
   * @param keep how many of the nearest customers each node keeps for Shaw removal.
   */
  SuccessorRoutes(IntVar[] successors, int offset, int[] varIndex, long[][] cost, int keep) {
    super(successors.length);
    this.successors = successors.clone();
    this.offset = offset;
    this.varIndex = varIndex.clone();
    depot = new boolean[n];
    for (int v = 0; v < n; v++) {
      IntVar x = successors[v];
      if (x.singleton() && x.value() - offset != v) {
        depot[v] = true;
        int w = x.value() - offset;
        if (w >= 0 && w < n) {
          depot[w] = true;
        }
      }
    }
    List<Integer> cs = new ArrayList<>();
    for (int v = 0; v < n; v++) {
      if (!depot[v]) {
        cs.add(v);
      }
    }
    customers = cs.stream().mapToInt(Integer::intValue).toArray();
    next = new int[n];
    if (cost != null) {
      List<List<long[]>> costs = new ArrayList<>();
      for (int v = 0; v < n; v++) {
        List<long[]> c = new ArrayList<>();
        for (int w : customers) {
          if (w != v) {
            long d = Math.min(at(cost, v, w), at(cost, w, v));
            if (d != Long.MAX_VALUE) {
              c.add(new long[] {w, d});
            }
          }
        }
        costs.add(c);
      }
      setNear(costs, keep);
    }
  }

  private static long at(long[][] cost, int v, int w) {
    return cost[v] == null ? Long.MAX_VALUE : cost[v][w];
  }

  /**
   * Returns the number of nodes of the circuit.
   *
   * @return the number of successor variables.
   */
  int size() {
    return n;
  }

  /**
   * Returns the successor variables.
   *
   * @return the variables, by node.
   */
  IntVar[] successors() {
    return successors.clone();
  }

  @Override
  void solution() {
    for (int v = 0; v < n; v++) {
      next[v] = successors[v].singleton() ? successors[v].value() - offset : v;
    }
    routes = null;
  }

  @Override
  void readRoutes() {
    if (routes != null) {
      return;
    }
    Arrays.fill(routeOf, -1);
    boolean[] seen = new boolean[n];
    List<int[]> rs = new ArrayList<>();
    // each circuit of the solution, from a depot when it has one
    int[] order = new int[n];
    int m = 0;
    for (int v = 0; v < n; v++) {
      if (depot[v]) {
        order[m++] = v;
      }
    }
    for (int v = 0; v < n; v++) {
      if (!depot[v]) {
        order[m++] = v;
      }
    }
    for (int start : order) {
      if (seen[start] || next[start] == start) {
        continue;
      }
      List<Integer> route = new ArrayList<>();
      int v = start;
      while (v >= 0 && v < n && !seen[v]) {
        seen[v] = true;
        if (depot[v]) {
          close(route, rs);
        } else {
          route.add(v);
        }
        v = next[v];
      }
      close(route, rs);
    }
    routes = rs.toArray(new int[0][]);
  }

  private void close(List<Integer> route, List<int[]> rs) {
    if (route.isEmpty()) {
      return;
    }
    for (int v : route) {
      routeOf[v] = rs.size();
    }
    rs.add(route.stream().mapToInt(Integer::intValue).toArray());
    route.clear();
  }

  @Override
  void relax(boolean[] removed, boolean[] relax) {
    for (int v = 0; v < n; v++) {
      int w = next[v];
      if (varIndex[v] >= 0 && (removed[v] || w >= 0 && w < n && removed[w])) {
        relax[varIndex[v]] = true;
      }
    }
  }
}
