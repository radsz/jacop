/*
 * PathCostBound.java
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
import java.util.PriorityQueue;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Cost bound of a path from s to t: {@code cost >= sum(w[e] * es[e])} where the selected edges form
 * a path from s to t. Used by {@link BoundedPath} together with the path itself and the exact cost
 * sum. It needs non-negative weights and does nothing otherwise.
 *
 * <p>When s and t are known it computes shortest distances from s and to t over the possible edges
 * (Dijkstra). The cost is at least the distance from s to t and at least the weight of the selected
 * edges; an edge u-v is removed when the shortest path from s through it to t, ds(u) + w + dt(v),
 * is longer than the cost's upper bound, and a node when ds(v) + dt(v) is. This is the bounding
 * part of the bounded path propagator of de Uña, Gange, Schachte and Stuckey (CP 2016), without
 * explanations.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class PathCostBound extends Constraint implements SatisfiedPresent, Copyable<PathCostBound> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final long INF = Long.MAX_VALUE / 4;

  final int[] from;
  final int[] to;
  final int[] weights;
  final IntVar s;
  final IntVar t;
  final IntVar[] ns;
  final IntVar[] es;
  final IntVar cost;
  final int base;
  final boolean directed;

  private final int n;
  private final int m;
  private final int[] tail;
  private final int[] head;
  private final boolean nonNegative;

  // edges leaving (out) and entering (in) each node; both lists hold every edge when undirected
  private final int[] outStart;
  private final int[] outEdge;
  private final int[] inStart;
  private final int[] inEdge;
  private final long[] fromS;
  private final long[] toT;

  /**
   * It constructs the bound.
   *
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param weights the weight of each edge.
   * @param s the first node of the path.
   * @param t the last node of the path.
   * @param ns the Boolean of each node; ns[i] is node base + i.
   * @param es the Boolean of each edge.
   * @param cost bounded from below by the weight of the selected edges.
   * @param base the number of the first node.
   * @param directed true for a directed graph.
   */
  PathCostBound(
      int[] from,
      int[] to,
      int[] weights,
      IntVar s,
      IntVar t,
      IntVar[] ns,
      IntVar[] es,
      IntVar cost,
      int base,
      boolean directed) {
    checkInputForNullness("ns", ns);
    checkInputForNullness("es", es);
    checkInputForNullness(new String[] {"s", "t", "cost"}, new Object[] {s, t, cost});
    if (from.length != es.length || to.length != es.length || weights.length != es.length) {
      throw new IllegalArgumentException(
          "PathCostBound: from, to, weights and es must have the same length");
    }
    this.n = ns.length;
    this.m = es.length;
    for (int e = 0; e < m; e++) {
      if (from[e] < base || from[e] >= base + n || to[e] < base || to[e] >= base + n) {
        throw new IllegalArgumentException(
            "PathCostBound: edge " + e + " has a node outside " + base + ".." + (base + n - 1));
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 2;
    this.from = Arrays.copyOf(from, m);
    this.to = Arrays.copyOf(to, m);
    this.weights = Arrays.copyOf(weights, m);
    this.s = s;
    this.t = t;
    this.ns = Arrays.copyOf(ns, n);
    this.es = Arrays.copyOf(es, m);
    this.cost = cost;
    this.base = base;
    this.directed = directed;
    this.nonNegative = Arrays.stream(weights).allMatch(w -> w >= 0);

    tail = new int[m];
    head = new int[m];
    for (int e = 0; e < m; e++) {
      tail[e] = from[e] - base;
      head[e] = to[e] - base;
    }
    outStart = new int[n + 1];
    inStart = new int[n + 1];
    for (int e = 0; e < m; e++) {
      outStart[tail[e] + 1]++;
      inStart[head[e] + 1]++;
      if (!directed) {
        outStart[head[e] + 1]++;
        inStart[tail[e] + 1]++;
      }
    }
    for (int v = 0; v < n; v++) {
      outStart[v + 1] += outStart[v];
      inStart[v + 1] += inStart[v];
    }
    outEdge = new int[outStart[n]];
    inEdge = new int[inStart[n]];
    int[] outFill = Arrays.copyOf(outStart, n);
    int[] inFill = Arrays.copyOf(inStart, n);
    for (int e = 0; e < m; e++) {
      outEdge[outFill[tail[e]]++] = e;
      inEdge[inFill[head[e]]++] = e;
      if (!directed) {
        outEdge[outFill[head[e]]++] = e;
        inEdge[inFill[tail[e]]++] = e;
      }
    }
    fromS = new long[n];
    toT = new long[n];

    setScope(ns, es, new IntVar[] {s, t, cost});
  }

  @Override
  public void consistency(Store store) {

    if (!nonNegative) {
      return;
    }

    long selected = 0;
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 1) {
        selected += weights[e];
      }
    }
    long lower = selected;

    if (s.singleton() && t.singleton()) {
      int source = s.value() - base;
      int target = t.value() - base;
      if (source < 0 || source >= n || target < 0 || target >= n) {
        throw Store.failException;
      }
      shortest(source, fromS, outStart, outEdge, true);
      shortest(target, toT, inStart, inEdge, false);
      if (fromS[target] >= INF) {
        throw Store.failException;
      }
      lower = Math.max(lower, fromS[target]);
      long upper = cost.max();
      for (int v = 0; v < n; v++) {
        if (ns[v].max() == 1 && fromS[v] + toT[v] > upper) {
          ns[v].domain.in(store.level, ns[v], 0, 0);
        }
      }
      for (int e = 0; e < m; e++) {
        if (es[e].max() == 1 && es[e].min() == 0) {
          long through = fromS[tail[e]] + weights[e] + toT[head[e]];
          if (!directed) {
            through = Math.min(through, fromS[head[e]] + weights[e] + toT[tail[e]]);
          }
          if (through > upper) {
            es[e].domain.in(store.level, es[e], 0, 0);
          }
        }
      }
    }

    if (lower > cost.max()) {
      throw Store.failException;
    }
    cost.domain.inMin(store.level, cost, (int) lower);
  }

  // Dijkstra over the possible edges; forward follows the edges, backward goes against them
  private void shortest(int start, long[] dist, int[] start0, int[] edges, boolean forward) {
    Arrays.fill(dist, INF);
    if (ns[start].max() == 0) {
      return;
    }
    dist[start] = 0;
    PriorityQueue<long[]> queue = new PriorityQueue<>((a, b) -> Long.compare(a[0], b[0]));
    queue.add(new long[] {0, start});
    while (!queue.isEmpty()) {
      long[] top = queue.poll();
      int v = (int) top[1];
      if (top[0] > dist[v]) {
        continue;
      }
      for (int i = start0[v]; i < start0[v + 1]; i++) {
        int e = edges[i];
        if (es[e].max() == 0) {
          continue;
        }
        int w;
        if (directed) {
          w = forward ? head[e] : tail[e];
        } else {
          w = tail[e] == v ? head[e] : tail[e];
        }
        if (ns[w].max() == 0) {
          continue;
        }
        long d = dist[v] + weights[e];
        if (d < dist[w]) {
          dist[w] = d;
          queue.add(new long[] {d, w});
        }
      }
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
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
      sum += (long) es[e].value() * weights[e];
    }
    // the path itself is checked by Path; with negative weights nothing is bounded
    return !nonNegative || cost.value() >= sum;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(directed ? " : DPathCostBound(" : " : PathCostBound(");
    result.append(Arrays.toString(from)).append(", ").append(Arrays.toString(to)).append(", ");
    result.append(Arrays.toString(weights)).append(", ");
    result.append(s).append(", ").append(t).append(", ");
    appendArrayToString(result, ns);
    result.append(", ");
    appendArrayToString(result, es);
    result.append(", ").append(cost).append(", ").append(base).append(")");
    return result.toString();
  }

  @Override
  public PathCostBound copy(VarMap map) {
    return new PathCostBound(
        from,
        to,
        weights,
        map.get(s),
        map.get(t),
        map.get(ns),
        map.get(es),
        map.get(cost),
        base,
        directed);
  }
}
