/*
 * ArborescenceBound.java
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
 * Cost bound of a spanning arborescence of a directed graph: the selected edges must form a tree
 * that spans all nodes, rooted at {@code root} with every edge pointing away from it, and {@code
 * cost >= sum(w[e] * es[e])} is bounded from below by the minimum arborescence that contains the
 * selected edges. Used by {@link WeightedSpanningTree} together with the tree itself and the exact
 * cost sum.
 *
 * <p>The bound is Edmonds' minimum arborescence, computed with its linear programming dual. A
 * virtual node with a zero-weight edge to every node in the domain of the root stands for the
 * unknown root, so one computation serves all roots. The dual gives a reduced cost {@code rc(e) >=
 * 0} for every edge and any arborescence {@code x} costs at least {@code lower + sum(rc(e), e in
 * x)}. Following Houndji, Schaus, Hounkonnou and Wolsey (A new filtering algorithm for the minimum
 * weighted arborescence constraint, CPAIOR 2017) this filters
 *
 * <ul>
 *   <li>an edge i-&gt;j with {@code lower + rc(i, j) > max(cost)}; when j lies above i in the
 *       minimum arborescence, the edge closes a cycle with its tree path from j down to i, so some
 *       node k on that path also changes its entering edge and {@code rc(i, j)} is raised by the
 *       cheapest such change (a simple form of the paper's improved reduced costs that needs only
 *       the tree and the second cheapest entering edge of each node);
 *   <li>a value r of the root when the virtual edge to r is too expensive in the same way;
 *   <li>an edge into j (or the root value j) that is selected when every other way into j is too
 *       expensive.
 * </ul>
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ArborescenceBound extends Constraint
    implements SatisfiedPresent, Copyable<ArborescenceBound> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final long INF = Long.MAX_VALUE / 4;

  final int n;
  final int[] from;
  final int[] to;
  final int[] weights;
  final IntVar root;
  final IntVar[] es;
  final IntVar cost;
  final int base;

  private final int m;
  // edges 0..m-1 are the graph's, edge m + v goes from the virtual node n to node v
  private final int[] tail;
  private final int[] head;
  private final boolean[] candidate;
  private final long[] reduced;

  // components of Edmonds' contraction: 0..n are the nodes (n is the virtual root), the rest are
  // contracted cycles
  private final int[] find;
  private final int[] parentComponent;
  private final int[] firstChild;
  private final int[] nextSibling;
  private final int[] chosen;
  private final long[] minimum;
  private final boolean[] needs;
  private final int[] mark;
  private final int[] stack;

  // the minimum arborescence: the edge entering each node, the depth and the node above it
  private final int[] inEdge;
  private final int[] depth;
  private final int[] above;
  // the two cheapest reduced costs into each node, the edge of the cheapest, and the cheapest one
  // other than inEdge
  private final long[] first;
  private final long[] second;
  private final int[] firstEdge;
  private final long[] alternative;

  /**
   * It constructs the bound.
   *
   * @param n the number of nodes.
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param weights the weight of each edge.
   * @param root the root of the tree.
   * @param es the Boolean of each edge.
   * @param cost bounded from below by the weight of the selected edges.
   * @param base the number of the first node.
   */
  public ArborescenceBound(
      int n, int[] from, int[] to, int[] weights, IntVar root, IntVar[] es, IntVar cost, int base) {
    checkInputForNullness("es", es);
    checkInputForNullness(new String[] {"root", "cost"}, new Object[] {root, cost});
    if (from.length != es.length || to.length != es.length || weights.length != es.length) {
      throw new IllegalArgumentException(
          "ArborescenceBound: from, to, weights and es must have the same length");
    }
    this.m = es.length;
    for (int e = 0; e < m; e++) {
      if (from[e] < base || from[e] >= base + n || to[e] < base || to[e] >= base + n) {
        throw new IllegalArgumentException(
            "ArborescenceBound: edge " + e + " has a node outside " + base + ".." + (base + n - 1));
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 2;
    this.n = n;
    this.from = Arrays.copyOf(from, m);
    this.to = Arrays.copyOf(to, m);
    this.weights = Arrays.copyOf(weights, m);
    this.root = root;
    this.es = Arrays.copyOf(es, m);
    this.cost = cost;
    this.base = base;

    tail = new int[m + n];
    head = new int[m + n];
    for (int e = 0; e < m; e++) {
      tail[e] = from[e] - base;
      head[e] = to[e] - base;
    }
    for (int v = 0; v < n; v++) {
      tail[m + v] = n;
      head[m + v] = v;
    }
    candidate = new boolean[m + n];
    reduced = new long[m + n];

    int components = 2 * (n + 1);
    find = new int[components];
    parentComponent = new int[components];
    firstChild = new int[components];
    nextSibling = new int[components];
    chosen = new int[components];
    minimum = new long[components];
    needs = new boolean[components];
    mark = new int[components];
    stack = new int[components];

    inEdge = new int[n + 1];
    depth = new int[n + 1];
    above = new int[n + 1];
    first = new long[n];
    second = new long[n];
    firstEdge = new int[n];
    alternative = new long[n];

    setScope(es, new IntVar[] {root, cost});
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

    if (n == 0) {
      return;
    }

    selectCandidates();
    long lower = minimumArborescence();
    if (lower > cost.max()) {
      throw Store.failException;
    }
    cost.domain.inMin(store.level, cost, (int) Math.max(lower, Integer.MIN_VALUE));

    long slack = cost.max() - lower;
    treeOrder();
    cheapestEntries();

    for (int e = 0; e < m + n; e++) {
      if (!candidate[e]) {
        continue;
      }
      int j = head[e];
      boolean free = e < m ? !es[e].singleton() : !root.singleton();
      if (!free) {
        continue;
      }
      if (inEdge[j] != e && reduced[e] + cycleCost(e, slack) > slack) {
        remove(store, e);
        continue;
      }
      long other = firstEdge[j] == e ? second[j] : first[j];
      if (other > slack) {
        select(store, e);
      }
    }
  }

  // the edges an arborescence rooted at some value of root may use, given the selected edges
  private void selectCandidates() {
    Arrays.fill(candidate, false);
    Arrays.fill(inEdge, -1);
    int fixedRoot = root.singleton() ? root.value() - base : -1;
    // inEdge holds the selected edge entering each node for now
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 1) {
        int j = head[e];
        if (inEdge[j] >= 0 || j == fixedRoot || tail[e] == j) {
          throw Store.failException;
        }
        inEdge[j] = e;
      }
    }
    for (int e = 0; e < m; e++) {
      int j = head[e];
      candidate[e] =
          es[e].max() == 1 && tail[e] != j && j != fixedRoot && (inEdge[j] < 0 || inEdge[j] == e);
    }
    for (int v = 0; v < n; v++) {
      candidate[m + v] = inEdge[v] < 0 && root.domain.contains(v + base);
    }
  }

  private int findComponent(int c) {
    int r = c;
    while (find[r] != r) {
      r = find[r];
    }
    while (find[c] != r) {
      int next = find[c];
      find[c] = r;
      c = next;
    }
    return r;
  }

  /**
   * Edmonds' algorithm in its dual form: every component without an entering edge takes its
   * cheapest entering edge and that weight is subtracted from all edges entering it; cycles of
   * chosen edges are contracted until none is left. It sets the reduced costs and inEdge and
   * returns the weight of the minimum arborescence.
   */
  private long minimumArborescence() {
    int components = n + 1;
    for (int c = 0; c < find.length; c++) {
      find[c] = c;
      parentComponent[c] = -1;
      firstChild[c] = -1;
      nextSibling[c] = -1;
      chosen[c] = -1;
    }
    for (int e = 0; e < m + n; e++) {
      reduced[e] = e < m ? weights[e] : 0;
    }
    long lower = 0;
    boolean contracted = true;
    while (contracted) {
      // the cheapest entering edge of every component that has none
      for (int c = 0; c < components; c++) {
        needs[c] = c != n && find[c] == c && chosen[c] < 0;
        minimum[c] = INF;
      }
      for (int e = 0; e < m + n; e++) {
        if (!candidate[e]) {
          continue;
        }
        int c = findComponent(head[e]);
        if (needs[c] && findComponent(tail[e]) != c && reduced[e] < minimum[c]) {
          minimum[c] = reduced[e];
        }
      }
      for (int c = 0; c < components; c++) {
        if (needs[c]) {
          if (minimum[c] == INF) {
            throw Store.failException;
          }
          lower += minimum[c];
        }
      }
      for (int e = 0; e < m + n; e++) {
        if (!candidate[e]) {
          continue;
        }
        int c = findComponent(head[e]);
        if (needs[c] && findComponent(tail[e]) != c) {
          reduced[e] -= minimum[c];
          if (reduced[e] == 0 && chosen[c] < 0) {
            chosen[c] = e;
          }
        }
      }

      // contract the cycles of chosen edges
      contracted = false;
      for (int c = 0; c < components; c++) {
        mark[c] = -1;
      }
      int top = components;
      for (int c = 0; c < top; c++) {
        if (find[c] != c || mark[c] != -1) {
          continue;
        }
        // follow chosen edges backwards from c until the virtual root or a marked component
        int d = c;
        while (d != n && mark[d] == -1) {
          mark[d] = c;
          d = findComponent(tail[chosen[d]]);
        }
        if (d == n || mark[d] != c) {
          continue;
        }
        // d is on a new cycle
        int cycle = components++;
        int k = d;
        do {
          int next = findComponent(tail[chosen[k]]);
          parentComponent[k] = cycle;
          nextSibling[k] = firstChild[cycle];
          firstChild[cycle] = k;
          k = next;
        } while (k != d);
        for (int child = firstChild[cycle]; child >= 0; child = nextSibling[child]) {
          find[child] = cycle;
        }
        mark[cycle] = c;
        contracted = true;
      }
    }

    // expand: each component's entering edge enters the child that holds its head
    Arrays.fill(inEdge, -1);
    int size = 0;
    for (int c = 0; c < components; c++) {
      if (find[c] == c && c != n) {
        stack[size++] = c;
        minimum[c] = chosen[c];
      }
    }
    while (size > 0) {
      int c = stack[--size];
      int e = (int) minimum[c];
      if (c < n) {
        inEdge[c] = e;
        continue;
      }
      int holder = head[e];
      while (parentComponent[holder] != c) {
        holder = parentComponent[holder];
      }
      for (int child = firstChild[c]; child >= 0; child = nextSibling[child]) {
        minimum[child] = child == holder ? e : chosen[child];
        stack[size++] = child;
      }
    }
    return lower;
  }

  // depth and parent of every node in the minimum arborescence
  private void treeOrder() {
    Arrays.fill(depth, -1);
    depth[n] = 0;
    above[n] = -1;
    for (int v = 0; v < n; v++) {
      int size = 0;
      int u = v;
      while (depth[u] < 0) {
        stack[size++] = u;
        u = tail[inEdge[u]];
      }
      while (size > 0) {
        int w = stack[--size];
        above[w] = tail[inEdge[w]];
        depth[w] = depth[above[w]] + 1;
      }
    }
  }

  private void cheapestEntries() {
    Arrays.fill(first, INF);
    Arrays.fill(second, INF);
    Arrays.fill(firstEdge, -1);
    Arrays.fill(alternative, INF);
    for (int e = 0; e < m + n; e++) {
      if (!candidate[e]) {
        continue;
      }
      int j = head[e];
      long r = reduced[e];
      if (r < first[j]) {
        second[j] = first[j];
        first[j] = r;
        firstEdge[j] = e;
      } else if (r < second[j]) {
        second[j] = r;
      }
      if (e != inEdge[j] && r < alternative[j]) {
        alternative[j] = r;
      }
    }
  }

  /**
   * The extra cost of edge i-&gt;j when j lies above i: some node strictly below j on the tree path
   * to i must take another entering edge. It returns 0 otherwise, and stops early once the extra
   * cost exceeds the slack.
   */
  private long cycleCost(int e, long slack) {
    int i = tail[e];
    int j = head[e];
    if (i == n || depth[i] <= depth[j]) {
      return 0;
    }
    long cheapest = INF;
    int u = i;
    while (depth[u] > depth[j]) {
      cheapest = Math.min(cheapest, alternative[u]);
      u = above[u];
    }
    return u == j ? Math.min(cheapest, slack + 1) : 0;
  }

  private void remove(Store store, int e) {
    if (e < m) {
      es[e].domain.in(store.level, es[e], 0, 0);
    } else {
      root.domain.inComplement(store.level, root, head[e] + base);
    }
  }

  private void select(Store store, int e) {
    if (e < m) {
      es[e].domain.in(store.level, es[e], 1, 1);
    } else {
      root.domain.in(store.level, root, head[e] + base, head[e] + base);
    }
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton() || !root.singleton()) {
      return false;
    }
    int r = root.value() - base;
    if (r < 0 || r >= n) {
      return false;
    }
    long sum = 0;
    Arrays.fill(above, -1);
    for (int e = 0; e < m; e++) {
      if (!es[e].singleton()) {
        return false;
      }
      if (es[e].value() == 1) {
        int j = head[e];
        if (above[j] >= 0 || j == r) {
          return false;
        }
        above[j] = tail[e];
        sum += weights[e];
      }
    }
    // every node reaches the root through the selected edges
    for (int v = 0; v < n; v++) {
      int u = v;
      int steps = 0;
      while (u != r) {
        if (above[u] < 0 || ++steps > n) {
          return false;
        }
        u = above[u];
      }
    }
    return cost.value() >= sum;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ArborescenceBound(").append(n).append(", ");
    result.append(Arrays.toString(from)).append(", ").append(Arrays.toString(to)).append(", ");
    result.append(Arrays.toString(weights)).append(", ").append(root).append(", ");
    appendArrayToString(result, es);
    result.append(", ").append(cost).append(", ").append(base).append(")");
    return result.toString();
  }

  @Override
  public ArborescenceBound copy(VarMap map) {
    return new ArborescenceBound(
        n, from, to, weights, map.get(root), map.get(es), map.get(cost), base);
  }
}
