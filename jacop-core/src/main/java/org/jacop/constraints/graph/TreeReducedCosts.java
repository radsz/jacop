/*
 * TreeReducedCosts.java
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

package org.jacop.constraints.graph;

import java.util.Arrays;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Reduced-cost filtering of the edge Booleans of a spanning tree bound, shared by {@link
 * SpanningTreeBound} and {@link ColouredSpanningTreeBound}, and the union-find they use. Given a
 * minimum spanning tree of weight lower and the largest weight upper a tree may have, an edge out
 * of the tree is removed when swapping it for the heaviest free edge on its tree path exceeds
 * upper, and a free tree edge is fixed when its cheapest replacement does (Régin, CPAIOR 2008;
 * Régin et al., CPAIOR 2010).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class TreeReducedCosts {

  private final int n;
  // the tree rooted at node 0: treeParent[v] is the node above v, reached by edge treeEdge[v]
  private final int[] treeParent;
  private final int[] treeEdge;
  private final int[] depth;
  private final int[] adjStart;
  private final int[] adjEdge;
  private final int[] queue;
  private final long[] replacement;

  TreeReducedCosts(int n, int m) {
    this.n = n;
    treeParent = new int[n];
    treeEdge = new int[n];
    depth = new int[n];
    adjStart = new int[n + 1];
    adjEdge = new int[2 * Math.max(n - 1, 0)];
    queue = new int[n];
    replacement = new long[m];
  }

  /**
   * It filters the edges by reduced costs on the tree in inTree.
   *
   * @param store the store.
   * @param es the edge Booleans.
   * @param tail the first node of each edge, from 0.
   * @param head the second node of each edge, from 0.
   * @param inTree the edges of the tree.
   * @param weight the weight of each edge.
   * @param lower the weight of the tree.
   * @param upper the largest weight a tree may have.
   */
  void filter(
      Store store,
      IntVar[] es,
      int[] tail,
      int[] head,
      boolean[] inTree,
      long[] weight,
      long lower,
      long upper) {
    int m = es.length;
    Arrays.fill(adjStart, 0);
    int treeSize = 0;
    for (int e = 0; e < m; e++) {
      if (inTree[e]) {
        adjStart[tail[e] + 1]++;
        adjStart[head[e] + 1]++;
        treeSize++;
      }
    }
    if (treeSize != n - 1) {
      // not a spanning tree, nothing to filter
      return;
    }
    for (int v = 0; v < n; v++) {
      adjStart[v + 1] += adjStart[v];
    }
    int[] fill = Arrays.copyOf(adjStart, n);
    for (int e = 0; e < m; e++) {
      if (inTree[e]) {
        adjEdge[fill[tail[e]]++] = e;
        adjEdge[fill[head[e]]++] = e;
      }
    }
    root(tail, head);

    Arrays.fill(replacement, Long.MAX_VALUE);
    for (int e = 0; e < m; e++) {
      if (inTree[e] || es[e].max() == 0 || tail[e] == head[e]) {
        continue;
      }
      // walk the tree path between the nodes of e
      int u = tail[e];
      int v = head[e];
      long heaviest = Long.MIN_VALUE;
      while (u != v) {
        if (depth[u] < depth[v]) {
          int t = u;
          u = v;
          v = t;
        }
        int f = treeEdge[u];
        if (es[f].min() == 0 && weight[f] > heaviest) {
          heaviest = weight[f];
        }
        if (weight[e] < replacement[f]) {
          replacement[f] = weight[e];
        }
        u = treeParent[u];
      }
      if (heaviest == Long.MIN_VALUE || lower - heaviest + weight[e] > upper) {
        es[e].domain.in(store.level, es[e], 0, 0);
      }
    }
    for (int e = 0; e < m; e++) {
      if (inTree[e]
          && es[e].min() == 0
          && (replacement[e] == Long.MAX_VALUE || lower - weight[e] + replacement[e] > upper)) {
        es[e].domain.in(store.level, es[e], 1, 1);
      }
    }
  }

  // breadth-first search from node 0 over the tree edges in adjStart and adjEdge
  private void root(int[] tail, int[] head) {
    Arrays.fill(treeParent, -1);
    treeParent[0] = 0;
    treeEdge[0] = -1;
    depth[0] = 0;
    int qh = 0;
    int qt = 0;
    queue[qt++] = 0;
    while (qh < qt) {
      int v = queue[qh++];
      for (int i = adjStart[v]; i < adjStart[v + 1]; i++) {
        int e = adjEdge[i];
        int w = tail[e] == v ? head[e] : tail[e];
        if (treeParent[w] < 0) {
          treeParent[w] = v;
          treeEdge[w] = e;
          depth[w] = depth[v] + 1;
          queue[qt++] = w;
        }
      }
    }
  }

  /**
   * It joins the sets of a and b.
   *
   * @param parent the union-find forest.
   * @param a a node.
   * @param b a node.
   * @return false if a and b were in the same set.
   */
  static boolean union(int[] parent, int a, int b) {
    int ra = find(parent, a);
    int rb = find(parent, b);
    if (ra == rb) {
      return false;
    }
    parent[ra] = rb;
    return true;
  }

  /**
   * It finds the root of the set of v, compressing the path.
   *
   * @param parent the union-find forest.
   * @param v a node.
   * @return the root.
   */
  static int find(int[] parent, int v) {
    int r = v;
    while (parent[r] != r) {
      r = parent[r];
    }
    while (parent[v] != r) {
      int next = parent[v];
      parent[v] = r;
      v = next;
    }
    return r;
  }
}
