/*
 * SymmetricMatching.java
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
package org.jacop.constraints;

import java.util.Arrays;

/**
 * Perfect matchings of the graph of a symmetric all different constraint, found with Edmonds'
 * blossom algorithm. Vertex i (0 to n-1) is variable i; an edge {i, j} means x[i] = j and x[j] = i.
 * A fixed point x[i] = i is an edge from i to its copy; the copies are joined to each other, and to
 * one extra vertex when needed to make the number of vertices even, so that the copies left over
 * pair among themselves. A solution is then a perfect matching. Only the variables that may be
 * fixed points in the graph built last have copies.
 *
 * <p>When a search for an augmenting path from a free vertex fails, its tree is a Tutte barrier:
 * the inner vertices S, and the outer vertices grouped by blossom into |S| + 1 odd sets with no
 * edge between two sets or to a vertex outside S and the tree. Explanations read it with {@link
 * #outer}, {@link #inner} and {@link #blossom}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SymmetricMatching {

  /** The number of variables. */
  final int n;

  /** The copy vertex of each variable, or -1 when it may not be a fixed point. */
  final int[] copyOf;

  /** The variable of each copy vertex (n and above), -1 for the extra vertex and variables. */
  final int[] original;

  /** The number of vertices. */
  int vertices;

  private final int firstCopy;
  private final int[] adjStart;
  private int[] adj;

  /** The matching: the mate of each vertex, or -1. */
  final int[] mate;

  private final int[] alt;
  private final int[] parent;
  private final int[] base;
  private final int[] queue;
  private final boolean[] used;
  private final int[] inBlossom;
  private final int[] onPath;
  private int blossomStamp;
  private int pathStamp;
  private final boolean[] removed;
  private final int[] degree;
  private boolean[] edge;

  /**
   * It creates the graph's vertices.
   *
   * @param n the number of variables
   */
  SymmetricMatching(int n) {
    this.n = n;
    copyOf = new int[n];
    firstCopy = n;
    int vertices = 2 * n + 1;
    original = new int[vertices];
    mate = new int[vertices];
    alt = new int[vertices];
    parent = new int[vertices];
    base = new int[vertices];
    queue = new int[vertices];
    used = new boolean[vertices];
    inBlossom = new int[vertices];
    onPath = new int[vertices];
    removed = new boolean[vertices];
    degree = new int[vertices];
    adjStart = new int[vertices + 1];
    Arrays.fill(mate, -1);
  }

  /**
   * Builds the edges: {i, j} when both edge[i * n + j] and edge[j * n + i] hold, and {i, copy of i}
   * when edge[i * n + i] holds.
   *
   * @param edge the values of the variables, x[i] may be j when edge[i * n + j]
   */
  void build(boolean[] edge) {
    this.edge = edge;
    Arrays.fill(original, -1);
    int copies = 0;
    for (int i = 0; i < n; i++) {
      copyOf[i] = edge[i * n + i] ? n + copies++ : -1;
      if (copyOf[i] >= 0) {
        original[copyOf[i]] = i;
      }
    }
    vertices = n + copies + ((n + copies) & 1);
    Arrays.fill(degree, 0);
    int extra = vertices - firstCopy;
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (edge[i * n + j] && edge[j * n + i]) {
          degree[i]++;
          degree[j]++;
        }
      }
      if (copyOf[i] >= 0) {
        degree[i]++;
        degree[copyOf[i]]++;
      }
    }
    for (int c = firstCopy; c < vertices; c++) {
      degree[c] += extra - 1;
    }
    for (int v = 0; v < vertices; v++) {
      adjStart[v + 1] = adjStart[v] + degree[v];
    }
    if (adj == null || adj.length < adjStart[vertices]) {
      adj = new int[adjStart[vertices]];
    }
    // degree now counts the edges filled in
    int[] fill = degree;
    System.arraycopy(adjStart, 0, fill, 0, vertices);
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (edge[i * n + j] && edge[j * n + i]) {
          adj[fill[i]++] = j;
          adj[fill[j]++] = i;
        }
      }
      if (copyOf[i] >= 0) {
        adj[fill[i]++] = copyOf[i];
        adj[fill[copyOf[i]]++] = i;
      }
    }
    for (int c = firstCopy; c < vertices; c++) {
      for (int d = firstCopy; d < vertices; d++) {
        if (c != d) {
          adj[fill[c]++] = d;
        }
      }
    }
  }

  /**
   * Finds a maximum matching, starting from the edges of the last matching that are still in the
   * graph.
   *
   * @return the first vertex left free, or -1 when the matching is perfect
   */
  int maximum() {
    // a pair is kept when both ends still are vertices with the edge between them (copies may
    // have been renumbered)
    for (int v = 0; v < vertices; v++) {
      int w = mate[v];
      if (w < 0 || w >= vertices || mate[w] != v || !hasEdge(Math.min(v, w), Math.max(v, w))) {
        mate[v] = -1;
      }
    }
    for (int v = 0; v < vertices; v++) {
      if (mate[v] < 0) {
        for (int k = adjStart[v]; k < adjStart[v + 1]; k++) {
          int w = adj[k];
          if (mate[w] < 0) {
            mate[v] = w;
            mate[w] = v;
            break;
          }
        }
      }
    }
    int free = -1;
    for (int v = 0; v < vertices; v++) {
      if (mate[v] < 0) {
        int end = augmentingPath(v, mate);
        if (end >= 0) {
          augment(end, mate);
        } else if (free < 0) {
          free = v;
        }
      }
    }
    return free;
  }

  /**
   * Leaves the barrier of a failed search from a free vertex of the maximum matching.
   *
   * @param free a vertex the matching leaves free
   */
  void barrier(int free) {
    int end = augmentingPath(free, mate);
    assert end < 0 : "the matching is not maximum";
  }

  /**
   * Tells whether edge {u, w} is in some perfect matching, given that {@link #mate} is perfect:
   * when the matching of the graph without u and w, which leaves their mates free, has an
   * augmenting path between them. When it is not, the failed search is left as a barrier of the
   * graph without u and w.
   *
   * @param u a vertex
   * @param w a vertex
   * @return the perfect matching with the edge (owned by this object, valid until the next call),
   *     or null
   */
  int[] withEdge(int u, int w) {
    if (mate[u] == w) {
      return mate;
    }
    System.arraycopy(mate, 0, alt, 0, vertices);
    int mu = alt[u];
    int mw = alt[w];
    alt[mu] = -1;
    alt[mw] = -1;
    alt[u] = -1;
    alt[w] = -1;
    removed[u] = true;
    removed[w] = true;
    int end = augmentingPath(mu, alt);
    removed[u] = false;
    removed[w] = false;
    if (end < 0) {
      return null;
    }
    augment(end, alt);
    alt[u] = w;
    alt[w] = u;
    return alt;
  }

  /**
   * Searches the graph without vertex u from u's mate, which the perfect matching {@link #mate}
   * less edge {u, mate} leaves as the only free vertex. The search cannot augment, and its outer
   * vertices are those some maximum matching of the graph without u leaves free (Gallai-Edmonds):
   * exactly the neighbours v of u for which edge {u, v} is in some perfect matching.
   *
   * @param u the vertex
   */
  void searchWithout(int u) {
    System.arraycopy(mate, 0, alt, 0, vertices);
    int mu = alt[u];
    alt[mu] = -1;
    alt[u] = -1;
    removed[u] = true;
    int end = augmentingPath(mu, alt);
    removed[u] = false;
    assert end < 0 : "the matching is not perfect";
  }

  /**
   * Tells whether a vertex was an outer vertex of the last failed search.
   *
   * @param v the vertex
   * @return true for outer vertices
   */
  boolean outer(int v) {
    return used[v];
  }

  /**
   * Tells whether a vertex was an inner vertex (in the barrier set) of the last failed search.
   *
   * @param v the vertex
   * @return true for inner vertices
   */
  boolean inner(int v) {
    return !used[v] && parent[v] >= 0;
  }

  /**
   * Returns the blossom of an outer vertex of the last failed search.
   *
   * @param v the vertex
   * @return its base
   */
  int blossom(int v) {
    return base[v];
  }

  /**
   * Tells whether edge {v, w} may be missing in the barrier of the last failed search: w is neither
   * inner, nor in the blossom of outer vertex v, nor removed.
   *
   * @param v an outer vertex
   * @param w another vertex
   * @param u1 a removed vertex, or -1
   * @param u2 a removed vertex, or -1
   * @return true when the barrier needs the edge to be missing
   */
  boolean separated(int v, int w, int u1, int u2) {
    return w != u1 && w != u2 && !inner(w) && !(used[w] && base[w] == base[v]);
  }

  private boolean hasEdge(int v, int w) {
    if (v >= n) {
      return true;
    }
    if (w >= n) {
      return original[w] == v;
    }
    return edge[v * n + w] && edge[w * n + v];
  }

  private void augment(int end, int[] mt) {
    int v = end;
    while (v >= 0) {
      int pv = parent[v];
      int next = mt[pv];
      mt[v] = pv;
      mt[pv] = v;
      v = next;
    }
  }

  private int lowestCommonAncestor(int a, int b, int[] mt) {
    int stamp = ++pathStamp;
    while (true) {
      a = base[a];
      onPath[a] = stamp;
      if (mt[a] < 0) {
        break;
      }
      a = parent[mt[a]];
    }
    while (true) {
      b = base[b];
      if (onPath[b] == stamp) {
        return b;
      }
      b = parent[mt[b]];
    }
  }

  private void markPath(int v, int b, int child, int[] mt) {
    while (base[v] != b) {
      inBlossom[base[v]] = blossomStamp;
      inBlossom[base[mt[v]]] = blossomStamp;
      parent[v] = child;
      child = mt[v];
      v = parent[mt[v]];
    }
  }

  // Edmonds' search from a free root; returns the free vertex reached, or -1
  private int augmentingPath(int root, int[] mt) {
    Arrays.fill(used, false);
    Arrays.fill(parent, -1);
    for (int v = 0; v < vertices; v++) {
      base[v] = v;
    }
    used[root] = true;
    int head = 0;
    int tail = 0;
    queue[tail++] = root;
    while (head < tail) {
      int v = queue[head++];
      for (int k = adjStart[v]; k < adjStart[v + 1]; k++) {
        int to = adj[k];
        if (removed[to] || base[v] == base[to] || mt[v] == to) {
          continue;
        }
        if (to == root || mt[to] >= 0 && parent[mt[to]] >= 0) {
          int b = lowestCommonAncestor(v, to, mt);
          blossomStamp++;
          markPath(v, b, to, mt);
          markPath(to, b, v, mt);
          for (int i = 0; i < vertices; i++) {
            if (inBlossom[base[i]] == blossomStamp) {
              base[i] = b;
              if (!used[i]) {
                used[i] = true;
                queue[tail++] = i;
              }
            }
          }
        } else if (parent[to] < 0) {
          parent[to] = v;
          if (mt[to] < 0) {
            return to;
          }
          used[mt[to]] = true;
          queue[tail++] = mt[to];
        }
      }
    }
    return -1;
  }
}
