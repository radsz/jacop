/*
 * SpanningTreeBound.java
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
import java.util.Comparator;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Cost bound of a spanning tree of an undirected graph: the selected edges must form a spanning
 * tree of all nodes and {@code cost >= sum(w[e] * es[e])} is bounded from below by the minimum
 * spanning tree that contains the selected edges. Used by {@link WeightedSpanningTree} together
 * with the tree itself and the exact cost sum.
 *
 * <p>Following Régin, Rousseau, Rueher and van Hoeve (The weighted spanning tree constraint
 * revisited, CPAIOR 2010) it also filters edges with the cost's upper bound: an edge outside the
 * minimum tree is removed when the best tree containing it (the minimum tree with the heaviest
 * unselected edge on the tree path between its nodes replaced by it) costs more than the bound, and
 * a tree edge is selected when the best tree without it (the cheapest edge outside the tree whose
 * tree path crosses it put in its place) costs more than the bound, or there is no such edge.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class SpanningTreeBound extends Constraint
    implements SatisfiedPresent, Copyable<SpanningTreeBound> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final int[] from;
  final int[] to;
  final int[] weights;
  final IntVar[] es;
  final IntVar cost;
  final int base;
  final int n;

  private final int m;
  private final int[] tail;
  private final int[] head;
  // edges by increasing weight
  private final int[] order;

  private final int[] parent;
  private final boolean[] inTree;
  // the tree rooted at node 0: treeParent[v] is the node above v, reached by edge treeEdge[v]
  private final int[] treeParent;
  private final int[] treeEdge;
  private final int[] depth;
  private final int[] adjStart;
  private final int[] adjEdge;
  private final int[] queue;
  private final long[] replacement;

  /**
   * It constructs the bound.
   *
   * @param n the number of nodes.
   * @param from the first node of each edge, a node number from base.
   * @param to the second node of each edge, a node number from base.
   * @param weights the weight of each edge.
   * @param es the Boolean of each edge.
   * @param cost bounded from below by the weight of the selected edges.
   * @param base the number of the first node.
   */
  public SpanningTreeBound(
      int n, int[] from, int[] to, int[] weights, IntVar[] es, IntVar cost, int base) {
    checkInputForNullness("es", es);
    checkInputForNullness(new String[] {"cost"}, new Object[] {cost});
    if (from.length != es.length || to.length != es.length || weights.length != es.length) {
      throw new IllegalArgumentException(
          "SpanningTreeBound: from, to, weights and es must have the same length");
    }
    this.m = es.length;
    for (int e = 0; e < m; e++) {
      if (from[e] < base || from[e] >= base + n || to[e] < base || to[e] >= base + n) {
        throw new IllegalArgumentException(
            "SpanningTreeBound: edge " + e + " has a node outside " + base + ".." + (base + n - 1));
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 2;
    this.n = n;
    this.from = Arrays.copyOf(from, m);
    this.to = Arrays.copyOf(to, m);
    this.weights = Arrays.copyOf(weights, m);
    this.es = Arrays.copyOf(es, m);
    this.cost = cost;
    this.base = base;

    tail = new int[m];
    head = new int[m];
    adjStart = new int[n + 1];
    for (int e = 0; e < m; e++) {
      tail[e] = from[e] - base;
      head[e] = to[e] - base;
    }
    order =
        IntStream.range(0, m)
            .boxed()
            .sorted(Comparator.comparingInt(e -> weights[e]))
            .mapToInt(Integer::intValue)
            .toArray();
    parent = new int[n];
    inTree = new boolean[m];
    treeParent = new int[n];
    treeEdge = new int[n];
    depth = new int[n];
    adjEdge = new int[2 * Math.max(n - 1, 0)];
    queue = new int[n];
    replacement = new long[m];

    setScope(es, new IntVar[] {cost});
  }

  @Override
  public void consistency(Store store) {

    if (n == 0) {
      return;
    }

    // Kruskal with the selected edges first
    for (int v = 0; v < n; v++) {
      parent[v] = v;
    }
    Arrays.fill(inTree, false);
    long lower = 0;
    int treeSize = 0;
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 1) {
        if (!union(tail[e], head[e])) {
          throw Store.failException;
        }
        inTree[e] = true;
        lower += weights[e];
        treeSize++;
      }
    }
    for (int e : order) {
      if (es[e].min() == 0 && es[e].max() == 1 && union(tail[e], head[e])) {
        inTree[e] = true;
        lower += weights[e];
        treeSize++;
      }
    }
    if (treeSize != n - 1) {
      throw Store.failException;
    }
    if (lower > cost.max()) {
      throw Store.failException;
    }
    cost.domain.inMin(store.level, cost, (int) lower);

    filterEdges(store, lower, cost.max());
  }

  private boolean union(int a, int b) {
    int ra = find(a);
    int rb = find(b);
    if (ra == rb) {
      return false;
    }
    parent[ra] = rb;
    return true;
  }

  private int find(int v) {
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

  private void filterEdges(Store store, long lower, long upper) {

    // root the tree at node 0
    Arrays.fill(adjStart, 0);
    for (int e = 0; e < m; e++) {
      if (inTree[e]) {
        adjStart[tail[e] + 1]++;
        adjStart[head[e] + 1]++;
      }
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
        if (es[f].min() == 0 && weights[f] > heaviest) {
          heaviest = weights[f];
        }
        if (weights[e] < replacement[f]) {
          replacement[f] = weights[e];
        }
        u = treeParent[u];
      }
      if (heaviest == Long.MIN_VALUE || lower - heaviest + weights[e] > upper) {
        es[e].domain.in(store.level, es[e], 0, 0);
      }
    }
    for (int e = 0; e < m; e++) {
      if (inTree[e]
          && es[e].min() == 0
          && (replacement[e] == Long.MAX_VALUE || lower - weights[e] + replacement[e] > upper)) {
        es[e].domain.in(store.level, es[e], 1, 1);
      }
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton()) {
      return false;
    }
    long sum = 0;
    int selected = 0;
    for (int v = 0; v < n; v++) {
      parent[v] = v;
    }
    for (int e = 0; e < m; e++) {
      if (!es[e].singleton()) {
        return false;
      }
      if (es[e].value() == 1) {
        if (!union(tail[e], head[e])) {
          return false;
        }
        sum += weights[e];
        selected++;
      }
    }
    return selected == Math.max(n - 1, 0) && cost.value() >= sum;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : SpanningTreeBound(").append(n).append(", ");
    result.append(Arrays.toString(from)).append(", ").append(Arrays.toString(to)).append(", ");
    result.append(Arrays.toString(weights)).append(", ");
    appendArrayToString(result, es);
    result.append(", ").append(cost).append(", ").append(base).append(")");
    return result.toString();
  }

  @Override
  public SpanningTreeBound copy(VarMap map) {
    return new SpanningTreeBound(n, from, to, weights, map.get(es), map.get(cost), base);
  }
}
