/*
 * SteinerBound.java
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
import org.jacop.core.Var;

/**
 * Cost bound of a Steiner tree with non-negative weights: the selected nodes and edges form a tree
 * (rooted at {@code root} with every edge pointing away from it in a directed graph) and {@code
 * cost >= sum(w[e] * es[e])} is bounded from below by the dual ascent of Wong (A dual ascent
 * approach for Steiner tree problems on a directed graph, Mathematical Programming 1984) on the
 * directed cut relaxation. The terminals are the nodes whose Booleans are 1 and the end nodes of
 * the selected edges.
 *
 * <p>An undirected edge is a pair of opposite arcs and the tree is rooted at one of the terminals.
 * A directed tree whose root is not fixed is rooted at a virtual node with an arc of cost 0 to
 * every possible root. The selected edges cost 0 and their weights are added to the bound. Every
 * set W of nodes that holds a terminal and not the root is entered by an arc of the tree, so the
 * dual ascent raises y(W) by the cheapest reduced cost of an arc into W, where W is the set of
 * nodes that reach a terminal through arcs of reduced cost 0, until every terminal is reached from
 * the root. Any tree x then costs at least {@code lower + sum(rc(a), a in x)} with {@code rc(a) >=
 * 0}, so with d(v), the shortest path from the root over the reduced costs, it filters
 *
 * <ul>
 *   <li>a node v with {@code lower + d(v) > max(cost)}: the tree path from the root to v costs at
 *       least d(v);
 *   <li>an edge none of whose arcs u-&gt;v has {@code lower + d(u) + rc(u, v) <= max(cost)}.
 * </ul>
 *
 * <p>This is the node and edge elimination by reduced costs of Polzin and Vahdati Daneshmand
 * (Improved algorithms for the Steiner problem in networks, Discrete Applied Mathematics 2001)
 * without the tests that assume that leaves are terminals, which do not hold for every solution of
 * the constraint. Used by {@link Steiner} together with the tree itself and the exact cost sum.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class SteinerBound extends Constraint implements SatisfiedPresent, Copyable<SteinerBound> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  static final long INF = Long.MAX_VALUE / 4;

  final int[] from;
  final int[] to;
  final int[] weights;
  final IntVar root;
  final IntVar[] ns;
  final IntVar[] es;
  final IntVar cost;
  final int base;
  final boolean directed;

  private final int n;
  private final int m;
  // arcs: an undirected edge e is arcs 2e and 2e + 1, a directed edge e is arc e; then the arc from
  // the virtual node n to each node v
  private final int arcs;
  private final int[] arcTail;
  private final int[] arcHead;
  private final int[] arcEdge;
  private final int[] inStart;
  private final int[] inArc;
  private final int[] outStart;
  private final int[] outArc;

  private final boolean[] available;
  private final long[] reduced;
  private final boolean[] terminal;
  private final int[] active;
  private final int[] componentSize;
  private final int[] mark;
  private int stamp;
  private final int[] component;
  private final long[] distance;
  private final int[] heap;
  private final long[] heapKey;

  /**
   * It constructs the bound.
   *
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param weights the weight of each edge, not negative.
   * @param root the root node of a directed tree; null for an undirected one.
   * @param ns the Boolean of each node; ns[i] is node base + i.
   * @param es the Boolean of each edge.
   * @param cost bounded from below by the weight of the selected edges.
   * @param base the number of the first node.
   * @param directed true for a directed graph.
   */
  public SteinerBound(
      int[] from,
      int[] to,
      int[] weights,
      IntVar root,
      IntVar[] ns,
      IntVar[] es,
      IntVar cost,
      int base,
      boolean directed) {
    checkInputForNullness("ns", ns);
    checkInputForNullness("es", es);
    checkInputForNullness(new String[] {"cost"}, new Object[] {cost});
    if (directed && root == null) {
      throw new IllegalArgumentException("SteinerBound: a directed tree needs a root");
    }
    if (from.length != es.length || to.length != es.length || weights.length != es.length) {
      throw new IllegalArgumentException(
          "SteinerBound: from, to, weights and es must have the same length");
    }
    this.n = ns.length;
    this.m = es.length;
    for (int e = 0; e < m; e++) {
      if (from[e] < base || from[e] >= base + n || to[e] < base || to[e] >= base + n) {
        throw new IllegalArgumentException(
            "SteinerBound: edge " + e + " has a node outside " + base + ".." + (base + n - 1));
      }
      if (weights[e] < 0) {
        throw new IllegalArgumentException("SteinerBound: edge " + e + " has a negative weight");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 2;
    this.from = Arrays.copyOf(from, m);
    this.to = Arrays.copyOf(to, m);
    this.weights = Arrays.copyOf(weights, m);
    this.root = directed ? root : null;
    this.ns = Arrays.copyOf(ns, n);
    this.es = Arrays.copyOf(es, m);
    this.cost = cost;
    this.base = base;
    this.directed = directed;

    int edgeArcs = directed ? m : 2 * m;
    arcs = edgeArcs + (directed ? n : 0);
    arcTail = new int[arcs];
    arcHead = new int[arcs];
    arcEdge = new int[arcs];
    for (int e = 0; e < m; e++) {
      int u = from[e] - base;
      int v = to[e] - base;
      if (directed) {
        setArc(e, u, v, e);
      } else {
        setArc(2 * e, u, v, e);
        setArc(2 * e + 1, v, u, e);
      }
    }
    for (int v = 0; v < arcs - edgeArcs; v++) {
      setArc(edgeArcs + v, n, v, -1);
    }
    inStart = new int[n + 2];
    inArc = new int[arcs];
    outStart = new int[n + 2];
    outArc = new int[arcs];
    for (int a = 0; a < arcs; a++) {
      inStart[arcHead[a] + 1]++;
      outStart[arcTail[a] + 1]++;
    }
    for (int v = 0; v <= n; v++) {
      inStart[v + 1] += inStart[v];
      outStart[v + 1] += outStart[v];
    }
    int[] inFill = Arrays.copyOf(inStart, n + 1);
    int[] outFill = Arrays.copyOf(outStart, n + 1);
    for (int a = 0; a < arcs; a++) {
      inArc[inFill[arcHead[a]]++] = a;
      outArc[outFill[arcTail[a]]++] = a;
    }

    available = new boolean[arcs];
    reduced = new long[arcs];
    terminal = new boolean[n + 1];
    active = new int[n];
    componentSize = new int[n];
    mark = new int[n + 1];
    component = new int[n + 1];
    distance = new long[n + 1];
    heap = new int[arcs + 1];
    heapKey = new long[arcs + 1];

    if (this.root == null) {
      setScope(ns, es, new IntVar[] {cost});
    } else {
      setScope(ns, es, new IntVar[] {this.root, cost});
    }
  }

  private void setArc(int a, int tail, int head, int edge) {
    arcTail[a] = tail;
    arcHead[a] = head;
    arcEdge[a] = edge;
  }

  @Override
  public int getConsistencyPruningEvent(Var var) {
    if (var == root && consistencyPruningEvents == null) {
      return IntDomain.ANY;
    }
    return super.getConsistencyPruningEvent(var);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {

    long selected = 0;
    Arrays.fill(terminal, false);
    for (int v = 0; v < n; v++) {
      terminal[v] = ns[v].min() == 1;
    }
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 1) {
        selected += weights[e];
        terminal[from[e] - base] = true;
        terminal[to[e] - base] = true;
      }
    }

    int rootNode = rootNode();
    if (rootNode < 0) {
      return;
    }
    terminal[rootNode] = false;

    for (int a = 0; a < arcs; a++) {
      int e = arcEdge[a];
      int u = arcTail[a];
      int v = arcHead[a];
      if (e < 0) {
        available[a] = ns[v].max() == 1 && root.domain.contains(v + base);
        reduced[a] = 0;
      } else {
        available[a] = es[e].max() == 1 && u != v && ns[u].max() == 1 && ns[v].max() == 1;
        reduced[a] = es[e].min() == 1 ? 0 : weights[e];
      }
    }

    long budget = (long) cost.max() - selected;
    if (budget < 0) {
      throw Store.failException;
    }
    long lower = dualAscent(rootNode, budget);
    cost.domain.inMin(store.level, cost, (int) Math.min(selected + lower, Integer.MAX_VALUE));

    shortestPaths(rootNode);
    long slack = budget - lower;
    for (int v = 0; v < n; v++) {
      if (!ns[v].singleton() && distance[v] > slack) {
        ns[v].domain.in(store.level, ns[v], 0, 0);
      }
    }
    for (int e = 0; e < m; e++) {
      if (es[e].singleton()) {
        continue;
      }
      boolean usable =
          directed ? usable(e, slack) : usable(2 * e, slack) || usable(2 * e + 1, slack);
      if (!usable) {
        es[e].domain.in(store.level, es[e], 0, 0);
      }
    }
  }

  // the root of the arborescence: the fixed root, the virtual node or the first terminal; -1 when
  // an undirected tree has no terminal
  private int rootNode() {
    if (directed) {
      return root.singleton() ? root.value() - base : n;
    }
    for (int v = 0; v < n; v++) {
      if (terminal[v]) {
        return v;
      }
    }
    return -1;
  }

  private boolean usable(int a, long slack) {
    return available[a]
        && distance[arcTail[a]] <= slack
        && distance[arcTail[a]] + reduced[a] <= slack;
  }

  private long dualAscent(int rootNode, long budget) {

    int count = 0;
    for (int v = 0; v < n; v++) {
      if (terminal[v]) {
        active[count] = v;
        componentSize[count] = 1;
        count++;
      }
    }

    long lower = 0;
    while (count > 0) {
      int pick = 0;
      for (int i = 1; i < count; i++) {
        if (componentSize[i] < componentSize[pick]) {
          pick = i;
        }
      }
      int size = growComponent(active[pick], rootNode);
      if (size < 0) {
        // the root reaches this terminal through arcs of reduced cost 0
        count--;
        active[pick] = active[count];
        componentSize[pick] = componentSize[count];
        continue;
      }
      if (size > componentSize[pick]) {
        componentSize[pick] = size;
        if (!smallest(pick, count)) {
          continue;
        }
      }

      long delta = INF;
      for (int i = 0; i < size; i++) {
        int v = component[i];
        for (int j = inStart[v]; j < inStart[v + 1]; j++) {
          int a = inArc[j];
          if (available[a] && mark[arcTail[a]] != stamp && reduced[a] < delta) {
            delta = reduced[a];
          }
        }
      }
      if (delta == INF) {
        // no arc enters a set with a terminal and without the root
        throw Store.failException;
      }
      lower += delta;
      if (lower > budget) {
        throw Store.failException;
      }
      for (int i = 0; i < size; i++) {
        int v = component[i];
        for (int j = inStart[v]; j < inStart[v + 1]; j++) {
          int a = inArc[j];
          if (available[a] && mark[arcTail[a]] != stamp) {
            reduced[a] -= delta;
          }
        }
      }
    }
    return lower;
  }

  private boolean smallest(int pick, int count) {
    for (int i = 0; i < count; i++) {
      if (componentSize[i] < componentSize[pick]) {
        return false;
      }
    }
    return true;
  }

  // the nodes that reach t through available arcs of reduced cost 0 into component, marked with a
  // new stamp; -1 when the root is among them
  private int growComponent(int t, int rootNode) {
    stamp++;
    int size = 0;
    component[size++] = t;
    mark[t] = stamp;
    for (int i = 0; i < size; i++) {
      int v = component[i];
      for (int j = inStart[v]; j < inStart[v + 1]; j++) {
        int a = inArc[j];
        int u = arcTail[a];
        if (available[a] && reduced[a] == 0 && mark[u] != stamp) {
          if (u == rootNode) {
            return -1;
          }
          mark[u] = stamp;
          component[size++] = u;
        }
      }
    }
    return size;
  }

  // Dijkstra from the root over the available arcs with their reduced costs
  private void shortestPaths(int rootNode) {
    Arrays.fill(distance, INF);
    distance[rootNode] = 0;
    int size = 0;
    heap[size] = rootNode;
    heapKey[size++] = 0;
    while (size > 0) {
      int v = heap[0];
      long d = heapKey[0];
      size--;
      if (size > 0) {
        siftDown(heap[size], heapKey[size], size);
      }
      if (d > distance[v]) {
        continue;
      }
      for (int j = outStart[v]; j < outStart[v + 1]; j++) {
        int a = outArc[j];
        int w = arcHead[a];
        long nd = d + reduced[a];
        if (available[a] && nd < distance[w]) {
          distance[w] = nd;
          siftUp(w, nd, size++);
        }
      }
    }
  }

  private void siftUp(int v, long key, int i) {
    while (i > 0) {
      int p = (i - 1) >> 1;
      if (heapKey[p] <= key) {
        break;
      }
      heap[i] = heap[p];
      heapKey[i] = heapKey[p];
      i = p;
    }
    heap[i] = v;
    heapKey[i] = key;
  }

  private void siftDown(int v, long key, int size) {
    int i = 0;
    while (true) {
      int c = 2 * i + 1;
      if (c >= size) {
        break;
      }
      if (c + 1 < size && heapKey[c + 1] < heapKey[c]) {
        c++;
      }
      if (heapKey[c] >= key) {
        break;
      }
      heap[i] = heap[c];
      heapKey[i] = heapKey[c];
      i = c;
    }
    heap[i] = v;
    heapKey[i] = key;
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton()) {
      return false;
    }
    long sum = 0;
    for (int e = 0; e < m; e++) {
      if (!es[e].singleton()) {
        return false;
      }
      if (es[e].value() == 1) {
        sum += weights[e];
      }
    }
    return cost.value() >= sum;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : SteinerBound(");
    result.append(Arrays.toString(from)).append(", ").append(Arrays.toString(to)).append(", ");
    result.append(Arrays.toString(weights)).append(", ").append(root).append(", ");
    appendArrayToString(result, ns);
    result.append(", ");
    appendArrayToString(result, es);
    result.append(", ").append(cost).append(", ").append(base).append(", ").append(directed);
    result.append(")");
    return result.toString();
  }

  @Override
  public SteinerBound copy(VarMap map) {
    return new SteinerBound(
        from,
        to,
        weights,
        root == null ? null : map.get(root),
        map.get(ns),
        map.get(es),
        map.get(cost),
        base,
        directed);
  }
}
