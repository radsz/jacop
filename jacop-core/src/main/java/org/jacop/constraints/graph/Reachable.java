/*
 * Reachable.java
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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.util.DominatorTree;

/**
 * Reachable constraint on a subgraph of a given graph. The graph has nodes {@code base .. base +
 * ns.length - 1} and edges {@code from[e] -> to[e]}; the subgraph has the nodes whose Boolean
 * {@code ns[i]} is 1 and the edges whose Boolean {@code es[e]} is 1. The constraint holds when
 * every selected edge has both its nodes selected, the root is selected and every selected node can
 * be reached from the root through selected edges (followed in their direction when the graph is
 * directed). This is MiniZinc's {@code reachable} and {@code dreachable}.
 *
 * <p>Without a root variable the root is any selected node, so the subgraph is non-empty and
 * connected (MiniZinc's {@code connected}), or in a directed graph has a node that reaches all the
 * others (MiniZinc's {@code dconnected}, whose decomposition is a reachable with a free root).
 *
 * <p>With {@code acyclic} the selected edges must also form a forest of the undirected graph: an
 * edge whose nodes are already joined by selected edges, and every self-loop, is removed. {@link
 * Tree} uses it.
 *
 * <p>Propagation, recomputed in time linear in the graph at each call: nodes that the root cannot
 * reach through possible edges are removed; nodes and edges that dominate a selected node (every
 * path from the root to it goes through them, found with a dominator tree over the graph with a
 * vertex in the middle of each edge) are selected. With a root variable whose value is not known
 * yet, a value is removed when that node cannot reach every selected node, and nodes that no
 * remaining root reaches are removed.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Reachable extends Constraint implements SatisfiedPresent, Copyable<Reachable> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The tail of each edge, as a node number. */
  final int[] from;

  /** The head of each edge, as a node number. */
  final int[] to;

  /** The root node number, or null when any selected node may be the root. */
  final IntVar root;

  // the root is also one of the node or edge variables
  private final boolean rootAliased;

  /** The Boolean of each node; ns[i] is node base + i. */
  final IntVar[] ns;

  /** The Boolean of each edge. */
  final IntVar[] es;

  /** The number of the first node. */
  final int base;

  /** Whether the edges are followed only in their direction. */
  final boolean directed;

  /** Whether the selected edges must form a forest. */
  final boolean acyclic;

  private final int n;
  private final int m;

  // edges by node: those leaving a node (directed) or touching it (undirected) are
  // adjEdge[adjStart[v] .. adjStart[v + 1] - 1]
  private final int[] adjStart;
  private final int[] adjEdge;

  // tail and head of each edge as 0-based node indexes
  private final int[] tail;
  private final int[] head;

  private final int[] visited;
  private int visitStamp;
  private final int[] stack;
  private final int[] valid;
  private int validStamp;
  private final int[] dominated;
  private int dominatedStamp;
  private final int[] parent;

  private DominatorTree dominators;

  /**
   * It constructs a reachable constraint.
   *
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param root the root node number, or null for any selected node.
   * @param ns the Boolean of each node; ns[i] is node base + i.
   * @param es the Boolean of each edge.
   * @param base the number of the first node.
   * @param directed true for a directed graph.
   */
  public Reachable(
      int[] from, int[] to, IntVar root, IntVar[] ns, IntVar[] es, int base, boolean directed) {
    this(from, to, root, ns, es, base, directed, false);
  }

  /**
   * It constructs a reachable constraint on nodes numbered from 0.
   *
   * @param from the tail of each edge.
   * @param to the head of each edge.
   * @param root the root node, or null for any selected node.
   * @param ns the Boolean of each node.
   * @param es the Boolean of each edge.
   * @param directed true for a directed graph.
   */
  public Reachable(int[] from, int[] to, IntVar root, IntVar[] ns, IntVar[] es, boolean directed) {
    this(from, to, root, ns, es, 0, directed, false);
  }

  Reachable(
      int[] from,
      int[] to,
      IntVar root,
      IntVar[] ns,
      IntVar[] es,
      int base,
      boolean directed,
      boolean acyclic) {

    checkInputForNullness("ns", ns);
    checkInputForNullness("es", es);
    checkInputForNullness("from", from);
    checkInputForNullness("to", to);
    if (from.length != es.length || to.length != es.length) {
      throw new IllegalArgumentException(
          "Reachable: from, to and es must have the same length, got "
              + from.length
              + ", "
              + to.length
              + " and "
              + es.length);
    }
    this.n = ns.length;
    this.m = es.length;
    for (int e = 0; e < m; e++) {
      if (from[e] < base || from[e] >= base + n || to[e] < base || to[e] >= base + n) {
        throw new IllegalArgumentException(
            "Reachable: edge " + e + " has a node outside " + base + ".." + (base + n - 1));
      }
    }
    for (IntVar v : ns) {
      checkBoolean("ns", v);
    }
    for (IntVar v : es) {
      checkBoolean("es", v);
    }

    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 2;
    this.from = Arrays.copyOf(from, m);
    this.to = Arrays.copyOf(to, m);
    this.root = root;
    this.ns = Arrays.copyOf(ns, n);
    this.es = Arrays.copyOf(es, m);
    this.base = base;
    this.directed = directed;
    this.acyclic = acyclic;

    tail = new int[m];
    head = new int[m];
    adjStart = new int[n + 1];
    for (int e = 0; e < m; e++) {
      tail[e] = from[e] - base;
      head[e] = to[e] - base;
      adjStart[tail[e] + 1]++;
      if (!directed && head[e] != tail[e]) {
        adjStart[head[e] + 1]++;
      }
    }
    for (int v = 0; v < n; v++) {
      adjStart[v + 1] += adjStart[v];
    }
    adjEdge = new int[adjStart[n]];
    int[] fill = Arrays.copyOf(adjStart, n);
    for (int e = 0; e < m; e++) {
      adjEdge[fill[tail[e]]++] = e;
      if (!directed && head[e] != tail[e]) {
        adjEdge[fill[head[e]]++] = e;
      }
    }

    visited = new int[n];
    stack = new int[n];
    valid = new int[n];
    dominated = new int[n + m];
    parent = new int[n];

    rootAliased =
        root != null
            && (Arrays.stream(ns).anyMatch(v -> v == root)
                || Arrays.stream(es).anyMatch(v -> v == root));

    if (root == null) {
      setScope(ns, es);
    } else {
      setScope(ns, es, new IntVar[] {root});
    }
  }

  private static void checkBoolean(String name, IntVar v) {
    if (v.min() < 0 || v.max() > 1) {
      throw new IllegalArgumentException(
          "Reachable: " + name + " must be 0/1 variables, got " + v.domain);
    }
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      propagateSubgraph(store);
      if (acyclic) {
        propagateAcyclic(store);
      }

      int r = fixedRoot(store);
      if (r >= 0) {
        removeUnreachable(store, r);
        selectDominators(store, r);
      } else if (directed) {
        propagateRootCandidates(store);
      } else {
        propagateNonEmpty(store);
      }

    } while (store.propagationHasOccurred);
  }

  // a selected edge selects its nodes and an edge with a removed node is removed
  private void propagateSubgraph(Store store) {
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 1) {
        setTrue(store, ns[tail[e]]);
        setTrue(store, ns[head[e]]);
      } else if (es[e].max() == 1 && (ns[tail[e]].max() == 0 || ns[head[e]].max() == 0)) {
        setFalse(store, es[e]);
      }
    }
  }

  // the selected edges form a forest; an edge inside a tree of selected edges is removed
  private void propagateAcyclic(Store store) {
    for (int v = 0; v < n; v++) {
      parent[v] = v;
    }
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 1) {
        int a = find(tail[e]);
        int b = find(head[e]);
        if (a == b) {
          throw Store.failException;
        }
        parent[a] = b;
      }
    }
    for (int e = 0; e < m; e++) {
      if (es[e].max() == 1 && es[e].min() == 0 && find(tail[e]) == find(head[e])) {
        setFalse(store, es[e]);
      }
    }
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

  /*
   * Restricts the root to nodes that may be selected and returns the node every selected node must
   * be reached from: the root when it is known, otherwise in an undirected graph any selected node
   * (all nodes of a connected subgraph reach each other). Returns -1 when there is no such node.
   */
  private int fixedRoot(Store store) {
    if (root != null) {
      root.domain.in(store.level, root, base, base + n - 1);
      if (!root.singleton()) {
        for (int v = 0; v < n; v++) {
          if (ns[v].max() == 0 && root.domain.contains(base + v)) {
            root.domain.inComplement(store.level, root, base + v);
          }
        }
      }
      if (root.singleton()) {
        int r = root.value() - base;
        setTrue(store, ns[r]);
        return r;
      }
    }
    if (!directed) {
      for (int v = 0; v < n; v++) {
        if (ns[v].min() == 1) {
          return v;
        }
      }
    }
    return -1;
  }

  private void removeUnreachable(Store store, int r) {
    visitStamp++;
    search(r, -1);
    for (int v = 0; v < n; v++) {
      if (visited[v] != visitStamp && ns[v].max() == 1) {
        setFalse(store, ns[v]);
      }
    }
  }

  /*
   * Depth-first search over the possible edges from start, marking reached nodes with visitStamp.
   * It returns early, with true, when it meets a node marked valid with stop.
   */
  private boolean search(int start, int stop) {
    int top = 0;
    stack[top++] = start;
    visited[start] = visitStamp;
    while (top > 0) {
      int v = stack[--top];
      if (stop >= 0 && valid[v] == stop) {
        return true;
      }
      for (int i = adjStart[v]; i < adjStart[v + 1]; i++) {
        int e = adjEdge[i];
        if (es[e].max() == 0) {
          continue;
        }
        int w = tail[e] == v ? head[e] : tail[e];
        if (visited[w] != visitStamp && ns[w].max() == 1) {
          visited[w] = visitStamp;
          stack[top++] = w;
        }
      }
    }
    return false;
  }

  /*
   * Selects the nodes and edges that every path from r to a selected node goes through. Each
   * possible edge e becomes a vertex n + e between its nodes, so dominating edges show up as
   * dominating vertices.
   */
  private void selectDominators(Store store, int r) {

    boolean needed = false;
    for (int v = 0; v < n && !needed; v++) {
      needed = v != r && ns[v].min() == 1;
    }
    if (!needed) {
      return;
    }

    if (dominators == null) {
      dominators = new DominatorTree(n + m);
    }
    DominatorTree d = dominators;
    d.clear();
    for (int e = 0; e < m; e++) {
      int u = tail[e];
      int w = head[e];
      if (u == w || es[e].max() == 0 || ns[u].max() == 0 || ns[w].max() == 0) {
        continue;
      }
      d.addArc(u, n + e);
      d.addArc(n + e, w);
      if (!directed) {
        d.addArc(w, n + e);
        d.addArc(n + e, u);
      }
    }
    d.computeReachable(r);

    dominatedStamp++;
    for (int v = 0; v < n; v++) {
      if (v == r || ns[v].min() == 0) {
        continue;
      }
      if (!d.reached(v)) {
        throw Store.failException;
      }
      int x = d.immediateDominator(v);
      while (x != r && dominated[x] != dominatedStamp) {
        dominated[x] = dominatedStamp;
        x = d.immediateDominator(x);
      }
    }
    for (int x = 0; x < n + m; x++) {
      if (dominated[x] == dominatedStamp) {
        setTrue(store, x < n ? ns[x] : es[x - n]);
      }
    }
  }

  /*
   * Directed graph whose root is not known yet. A candidate root is valid when it reaches every
   * selected node; a node reaching a valid candidate is valid too. Invalid values are removed from
   * the root and nodes that no valid candidate reaches are removed.
   */
  private void propagateRootCandidates(Store store) {

    int selected = 0;
    for (int v = 0; v < n; v++) {
      if (ns[v].min() == 1) {
        selected++;
      }
    }

    validStamp++;
    int validCount = 0;
    int lastValid = -1;
    for (int c = 0; c < n; c++) {
      if (!isCandidate(c)) {
        continue;
      }
      boolean ok;
      if (selected == 0) {
        ok = true;
      } else {
        visitStamp++;
        ok = search(c, validStamp);
        if (!ok) {
          int reached = 0;
          for (int v = 0; v < n; v++) {
            if (visited[v] == visitStamp && ns[v].min() == 1) {
              reached++;
            }
          }
          ok = reached == selected;
        }
      }
      if (ok) {
        valid[c] = validStamp;
        validCount++;
        lastValid = c;
      } else if (root != null) {
        root.domain.inComplement(store.level, root, base + c);
        if (rootAliased) {
          // the root is also a node or edge variable, so the count of selected nodes may be stale;
          // consistency() runs this again
          return;
        }
      }
    }

    if (validCount == 0) {
      throw Store.failException;
    }
    if (root == null && selected == 0) {
      // every possible node is a candidate, so nothing is unreachable; the subgraph is non-empty
      if (validCount == 1) {
        setTrue(store, ns[lastValid]);
      }
      return;
    }

    // nodes that no valid candidate reaches cannot be selected
    visitStamp++;
    for (int c = 0; c < n; c++) {
      if (valid[c] == validStamp && visited[c] != visitStamp) {
        search(c, -1);
      }
    }
    for (int v = 0; v < n; v++) {
      if (visited[v] != visitStamp && ns[v].max() == 1) {
        setFalse(store, ns[v]);
      }
    }

    if (validCount == 1) {
      // the only possible root
      setTrue(store, ns[lastValid]);
      selectDominators(store, lastValid);
    }
  }

  private boolean isCandidate(int v) {
    return ns[v].max() == 1 && (root == null || root.domain.contains(base + v));
  }

  // undirected graph without a selected node: the subgraph still has at least one node
  private void propagateNonEmpty(Store store) {
    int possible = 0;
    int last = -1;
    for (int v = 0; v < n; v++) {
      if (isCandidate(v)) {
        possible++;
        last = v;
      }
    }
    if (possible == 0) {
      throw Store.failException;
    }
    if (possible == 1) {
      setTrue(store, ns[last]);
    }
  }

  private static void setTrue(Store store, IntVar v) {
    if (v.min() == 0) {
      v.domain.in(store.level, v, 1, 1);
    }
  }

  private static void setFalse(Store store, IntVar v) {
    if (v.max() == 1) {
      v.domain.in(store.level, v, 0, 0);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {

    for (IntVar v : ns) {
      if (!v.singleton()) {
        return false;
      }
    }
    for (IntVar v : es) {
      if (!v.singleton()) {
        return false;
      }
    }
    if (root != null && !root.singleton()) {
      return false;
    }
    return holds();
  }

  /** Checks the relation on a complete assignment of the variables. */
  private boolean holds() {
    for (int e = 0; e < m; e++) {
      if (es[e].value() == 1 && (ns[tail[e]].value() == 0 || ns[head[e]].value() == 0)) {
        return false;
      }
    }
    if (acyclic) {
      for (int v = 0; v < n; v++) {
        parent[v] = v;
      }
      for (int e = 0; e < m; e++) {
        if (es[e].value() == 1) {
          int a = find(tail[e]);
          int b = find(head[e]);
          if (a == b) {
            return false;
          }
          parent[a] = b;
        }
      }
    }
    if (root != null) {
      int r = root.value() - base;
      return r >= 0 && r < n && ns[r].value() == 1 && reachesAllSelected(r);
    }
    for (int r = 0; r < n; r++) {
      if (ns[r].value() == 1) {
        if (reachesAllSelected(r)) {
          return true;
        }
        if (!directed) {
          return false;
        }
      }
    }
    return false;
  }

  private boolean reachesAllSelected(int r) {
    visitStamp++;
    search(r, -1);
    for (int v = 0; v < n; v++) {
      if (ns[v].value() == 1 && visited[v] != visitStamp) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(directed ? " : DReachable(" : " : Reachable(");
    result.append(Arrays.toString(from)).append(", ").append(Arrays.toString(to)).append(", ");
    result.append(root).append(", ");
    appendArrayToString(result, ns);
    result.append(", ");
    appendArrayToString(result, es);
    result.append(", ").append(base);
    if (acyclic) {
      result.append(", acyclic");
    }
    result.append(")");
    return result.toString();
  }

  @Override
  public Reachable copy(VarMap map) {
    return new Reachable(
        from,
        to,
        root == null ? null : map.get(root),
        map.get(ns),
        map.get(es),
        base,
        directed,
        acyclic);
  }
}
