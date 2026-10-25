/*
 * GraphSemantics.java
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

/**
 * Plain-Java reference semantics of the MiniZinc graph globals, written from the MiniZinc library
 * decompositions (std/fzn_dreachable_int.mzn, fzn_dtree_int.mzn, fzn_dpath_int.mzn and the
 * undirected versions) rather than from the propagators, for the brute-force tests. Nodes are
 * 0-based; ns and es are 0/1 values.
 */
final class GraphSemantics {

  private GraphSemantics() {}

  static boolean subgraph(int[] from, int[] to, int[] ns, int[] es) {
    for (int e = 0; e < es.length; e++) {
      if (es[e] == 1 && (ns[from[e]] == 0 || ns[to[e]] == 0)) {
        return false;
      }
    }
    return true;
  }

  private static boolean isNode(int[] ns, int r) {
    return r >= 0 && r < ns.length && ns[r] == 1;
  }

  /** Every selected node is reached from r through selected edges. */
  static boolean reachesAll(int[] from, int[] to, int[] ns, int[] es, int r, boolean directed) {
    int n = ns.length;
    boolean[] seen = new boolean[n];
    seen[r] = true;
    boolean changed = true;
    while (changed) {
      changed = false;
      for (int e = 0; e < es.length; e++) {
        if (es[e] == 1) {
          if (seen[from[e]] && !seen[to[e]]) {
            seen[to[e]] = true;
            changed = true;
          }
          if (!directed && seen[to[e]] && !seen[from[e]]) {
            seen[from[e]] = true;
            changed = true;
          }
        }
      }
    }
    for (int v = 0; v < n; v++) {
      if (ns[v] == 1 && !seen[v]) {
        return false;
      }
    }
    return true;
  }

  /** MiniZinc reachable and dreachable. */
  static boolean reachable(int[] from, int[] to, int[] ns, int[] es, int r, boolean directed) {
    return isNode(ns, r) && subgraph(from, to, ns, es) && reachesAll(from, to, ns, es, r, directed);
  }

  /** MiniZinc connected and dconnected: reachable from some root. */
  static boolean connected(int[] from, int[] to, int[] ns, int[] es, boolean directed) {
    for (int r = 0; r < ns.length; r++) {
      if (reachable(from, to, ns, es, r, directed)) {
        return true;
      }
    }
    return false;
  }

  /**
   * MiniZinc dtree, condition by condition: a parent for each selected node but the root, every
   * selected edge is the parent edge of its head, distances grow along parent edges (so no edge
   * enters the root and parent chains end at the root), and sum(es) = sum(ns) - 1.
   */
  static boolean dtree(int[] from, int[] to, int[] ns, int[] es, int r) {
    if (!isNode(ns, r) || !subgraph(from, to, ns, es)) {
      return false;
    }
    int n = ns.length;
    int[] parent = new int[n];
    java.util.Arrays.fill(parent, -1);
    int edges = 0;
    for (int e = 0; e < es.length; e++) {
      if (es[e] == 1) {
        edges++;
        if (to[e] == r || (parent[to[e]] >= 0 && parent[to[e]] != from[e])) {
          return false;
        }
        parent[to[e]] = from[e];
      }
    }
    int nodes = 0;
    for (int v = 0; v < n; v++) {
      if (ns[v] == 1) {
        nodes++;
        if (v != r && parent[v] < 0) {
          return false;
        }
        // the parent chain reaches the root within n steps (distances are 0..n-1)
        int u = v;
        int steps = 0;
        while (u >= 0 && u != r && steps < n) {
          u = parent[u];
          steps++;
        }
        if (u != r) {
          return false;
        }
      }
    }
    return edges == nodes - 1;
  }

  /** MiniZinc tree: a connected acyclic subgraph containing r. */
  static boolean tree(int[] from, int[] to, int[] ns, int[] es, int r) {
    if (!isNode(ns, r) || !subgraph(from, to, ns, es)) {
      return false;
    }
    int edges = 0;
    for (int e = 0; e < es.length; e++) {
      if (es[e] == 1) {
        if (from[e] == to[e]) {
          return false;
        }
        edges++;
      }
    }
    int nodes = 0;
    for (int v : ns) {
      nodes += v;
    }
    return edges == nodes - 1 && reachesAll(from, to, ns, es, r, false);
  }

  /** MiniZinc dpath: dtree from s and dtree of the reversed graph from t. */
  static boolean dpath(int[] from, int[] to, int[] ns, int[] es, int s, int t) {
    return dtree(from, to, ns, es, s) && dtree(to, from, ns, es, t);
  }

  /** MiniZinc path: walking from s along unused selected edges ends at t having used them all. */
  static boolean path(int[] from, int[] to, int[] ns, int[] es, int s, int t) {
    if (!isNode(ns, s) || !isNode(ns, t) || !subgraph(from, to, ns, es)) {
      return false;
    }
    int n = ns.length;
    boolean[] used = new boolean[es.length];
    boolean[] visited = new boolean[n];
    int current = s;
    visited[s] = true;
    int usedCount = 0;
    while (current != t) {
      int next = -1;
      int count = 0;
      for (int e = 0; e < es.length; e++) {
        if (es[e] == 1 && !used[e] && (from[e] == current || to[e] == current)) {
          count++;
          next = e;
        }
      }
      if (count != 1) {
        return false;
      }
      used[next] = true;
      usedCount++;
      int w = from[next] == current ? to[next] : from[next];
      if (w == current || visited[w]) {
        return false;
      }
      visited[w] = true;
      current = w;
    }
    int edges = 0;
    for (int e : es) {
      edges += e;
    }
    for (int v = 0; v < n; v++) {
      if (ns[v] == 1 && !visited[v]) {
        return false;
      }
    }
    return edges == usedCount;
  }
}
