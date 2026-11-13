/*
 * BoundedFlow.java
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
 * A feasible circulation with lower and upper bounds on the arcs, and the flow values each arc can
 * take in some feasible circulation. It is the filtering engine of the flow-based cardinality
 * constraints ({@link Same}, {@link UsedBy}, {@link SymmetricCardinality}, {@link
 * CardinalityMatrix}).
 *
 * <p>A feasible circulation is found by the standard reduction to a maximum flow (Ford and
 * Fulkerson, "Flows in Networks", 1962): the lower bounds are sent at once and the excesses they
 * leave are routed from a super source to a super sink by Dinic's algorithm. Two feasible
 * circulations differ by a circulation of the residual graph, which is a sum of cycles, so an arc
 * can carry another flow value in some feasible circulation if and only if its two ends are in the
 * same strongly connected component of the residual graph (Régin, AAAI 1994 and 1996). For arcs
 * with a wider range the exact smallest and largest flows are found by pushing flow around the
 * residual cycles through the arc.
 *
 * <p>The arcs are added again before every computation; the arrays grow as needed and are reused.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class BoundedFlow {

  /** A bound that no flow reaches. */
  static final int INFINITE = Integer.MAX_VALUE / 4;

  private int nodes;
  private int arcs;
  private int[] from = new int[16];
  private int[] to = new int[16];
  private int[] lower = new int[16];
  private int[] upper = new int[16];
  private int[] flow = new int[16];

  // the residual graph of the max-flow problem: two half arcs per arc, plus the arcs of the super
  // source and sink; half arc 2a goes forward and 2a + 1 backward
  private int[] head = new int[32];
  private int[] cap = new int[32];
  private int[] nextOut = new int[32];
  private int[] firstOut = new int[8];
  private int[] level = new int[8];
  private int[] iter = new int[8];
  private int[] queue = new int[8];
  private int[] excess = new int[8];
  private int halfArcs;

  // strongly connected components of the residual graph of the circulation
  private int[] component = new int[8];
  private int[] index = new int[8];
  private int[] lowLink = new int[8];
  private int[] stack = new int[8];
  private boolean[] onStack = new boolean[8];
  private int[] callNode = new int[8];
  private int[] callArc = new int[8];

  /**
   * Starts a new network.
   *
   * @param nodes the number of nodes, numbered from 0
   */
  void reset(int nodes) {
    this.nodes = nodes;
    this.arcs = 0;
  }

  /**
   * Adds an arc.
   *
   * @param u its tail
   * @param w its head
   * @param lo the least flow on it
   * @param up the most flow on it, at least lo
   * @return the index of the arc
   */
  int addArc(int u, int w, int lo, int up) {
    if (arcs == from.length) {
      int size = 2 * arcs;
      from = Arrays.copyOf(from, size);
      to = Arrays.copyOf(to, size);
      lower = Arrays.copyOf(lower, size);
      upper = Arrays.copyOf(upper, size);
      flow = Arrays.copyOf(flow, size);
    }
    from[arcs] = u;
    to[arcs] = w;
    lower[arcs] = lo;
    upper[arcs] = up;
    return arcs++;
  }

  /**
   * The flow on an arc in the circulation found last.
   *
   * @param a the arc
   * @return its flow
   */
  int flow(int a) {
    return flow[a];
  }

  /**
   * Finds a feasible circulation and the components of its residual graph.
   *
   * @return false if there is no feasible circulation
   */
  boolean solve() {
    int s = nodes;
    int t = nodes + 1;
    int total = nodes + 2;
    ensureNodes(total);
    Arrays.fill(firstOut, 0, total, -1);
    Arrays.fill(excess, 0, total, 0);
    halfArcs = 0;
    ensureHalfArcs(2 * arcs + 2 * nodes);
    for (int a = 0; a < arcs; a++) {
      if (lower[a] > upper[a]) {
        return false;
      }
      addHalf(from[a], to[a], upper[a] - lower[a]);
      addHalf(to[a], from[a], 0);
      excess[to[a]] += lower[a];
      excess[from[a]] -= lower[a];
    }
    int needed = 0;
    for (int v = 0; v < nodes; v++) {
      if (excess[v] > 0) {
        addHalf(s, v, excess[v]);
        addHalf(v, s, 0);
        needed += excess[v];
      } else if (excess[v] < 0) {
        addHalf(v, t, -excess[v]);
        addHalf(t, v, 0);
      }
    }
    if (maxFlow(s, t, total) < needed) {
      return false;
    }
    for (int a = 0; a < arcs; a++) {
      flow[a] = lower[a] + cap[2 * a + 1];
    }
    components();
    return true;
  }

  /**
   * Whether an arc can carry another flow in some feasible circulation.
   *
   * @param a the arc
   * @return true if its flow is not the same in all feasible circulations
   */
  boolean variable(int a) {
    return component[from[a]] == component[to[a]] && lower[a] < upper[a];
  }

  /**
   * The largest flow an arc carries in some feasible circulation. It may change the circulation
   * found last (it stays feasible), but not the components, which are of every circulation.
   *
   * @param a the arc
   * @return its largest flow
   */
  int maxFlowOn(int a) {
    if (!variable(a)) {
      return flow[a];
    }
    // send flow from to[a] back to from[a] in the residual graph without a's own half arcs
    int extra = pushAround(to[a], from[a], 2 * a, upper[a] - flow[a]);
    cap[2 * a] -= extra;
    cap[2 * a + 1] += extra;
    flow[a] += extra;
    return flow[a];
  }

  /**
   * The smallest flow an arc carries in some feasible circulation. Like {@link #maxFlowOn(int)} it
   * may change the circulation.
   *
   * @param a the arc
   * @return its smallest flow
   */
  int minFlowOn(int a) {
    if (!variable(a)) {
      return flow[a];
    }
    int less = pushAround(from[a], to[a], 2 * a, flow[a] - lower[a]);
    cap[2 * a] += less;
    cap[2 * a + 1] -= less;
    flow[a] -= less;
    return flow[a];
  }

  // augments up to limit units from u to w over the arcs of the network, without arc skip's halves
  private int pushAround(int u, int w, int skip, int limit) {
    int total = nodes;
    int pushed = 0;
    int[] parent = iter;
    while (pushed < limit) {
      Arrays.fill(parent, 0, total, -1);
      int qh = 0;
      int qt = 0;
      queue[qt++] = u;
      parent[u] = -2;
      while (qh < qt && parent[w] == -1) {
        int v = queue[qh++];
        for (int e = firstOut[v]; e >= 0; e = nextOut[e]) {
          int h = head[e];
          if (cap[e] > 0 && h < total && parent[h] == -1 && (e >> 1) != (skip >> 1)) {
            parent[h] = e;
            queue[qt++] = h;
          }
        }
      }
      if (parent[w] == -1) {
        break;
      }
      int amount = limit - pushed;
      for (int v = w; v != u; v = head[parent[v] ^ 1]) {
        amount = Math.min(amount, cap[parent[v]]);
      }
      for (int v = w; v != u; v = head[parent[v] ^ 1]) {
        cap[parent[v]] -= amount;
        cap[parent[v] ^ 1] += amount;
      }
      pushed += amount;
    }
    for (int b = 0; b < arcs; b++) {
      flow[b] = lower[b] + cap[2 * b + 1];
    }
    return pushed;
  }

  private void addHalf(int u, int w, int c) {
    head[halfArcs] = w;
    cap[halfArcs] = c;
    nextOut[halfArcs] = firstOut[u];
    firstOut[u] = halfArcs++;
  }

  // Dinic's algorithm
  private int maxFlow(int s, int t, int total) {
    int result = 0;
    while (bfs(s, t, total)) {
      System.arraycopy(firstOut, 0, iter, 0, total);
      int f;
      while ((f = dfs(s, t, INFINITE)) > 0) {
        result += f;
      }
    }
    return result;
  }

  private boolean bfs(int s, int t, int total) {
    Arrays.fill(level, 0, total, -1);
    int qh = 0;
    int qt = 0;
    queue[qt++] = s;
    level[s] = 0;
    while (qh < qt) {
      int v = queue[qh++];
      for (int e = firstOut[v]; e >= 0; e = nextOut[e]) {
        if (cap[e] > 0 && level[head[e]] < 0) {
          level[head[e]] = level[v] + 1;
          queue[qt++] = head[e];
        }
      }
    }
    return level[t] >= 0;
  }

  // a blocking-flow search, iterative to stay safe on long paths
  private int dfs(int s, int t, int limit) {
    int[] path = callArc;
    int depth = 0;
    int v = s;
    while (true) {
      if (v == t) {
        int amount = limit;
        for (int i = 0; i < depth; i++) {
          amount = Math.min(amount, cap[path[i]]);
        }
        for (int i = 0; i < depth; i++) {
          cap[path[i]] -= amount;
          cap[path[i] ^ 1] += amount;
        }
        return amount;
      }
      boolean advanced = false;
      for (; iter[v] >= 0; iter[v] = nextOut[iter[v]]) {
        int e = iter[v];
        int h = head[e];
        if (cap[e] > 0 && level[h] == level[v] + 1) {
          path[depth++] = e;
          v = h;
          advanced = true;
          break;
        }
      }
      if (!advanced) {
        if (depth == 0) {
          return 0;
        }
        level[v] = -1;
        int e = path[--depth];
        v = head[e ^ 1];
        iter[v] = nextOut[iter[v]];
      }
    }
  }

  // Tarjan's algorithm on the residual graph of the original nodes, iterative
  private void components() {
    int counter = 0;
    int top = 0;
    int comps = 0;
    Arrays.fill(index, 0, nodes, -1);
    Arrays.fill(onStack, 0, nodes, false);
    for (int root = 0; root < nodes; root++) {
      if (index[root] >= 0) {
        continue;
      }
      int depth = 0;
      callNode[0] = root;
      callArc[0] = firstOut[root];
      index[root] = lowLink[root] = counter++;
      stack[top++] = root;
      onStack[root] = true;
      while (depth >= 0) {
        int v = callNode[depth];
        int e = callArc[depth];
        if (e >= 0) {
          callArc[depth] = nextOut[e];
          int h = head[e];
          if (cap[e] <= 0 || h >= nodes) {
            continue;
          }
          if (index[h] < 0) {
            index[h] = lowLink[h] = counter++;
            stack[top++] = h;
            onStack[h] = true;
            depth++;
            callNode[depth] = h;
            callArc[depth] = firstOut[h];
          } else if (onStack[h]) {
            lowLink[v] = Math.min(lowLink[v], index[h]);
          }
        } else {
          if (lowLink[v] == index[v]) {
            int w;
            do {
              w = stack[--top];
              onStack[w] = false;
              component[w] = comps;
            } while (w != v);
            comps++;
          }
          depth--;
          if (depth >= 0) {
            int p = callNode[depth];
            lowLink[p] = Math.min(lowLink[p], lowLink[v]);
          }
        }
      }
    }
  }

  private void ensureNodes(int total) {
    if (firstOut.length < total) {
      int size = Math.max(total, 2 * firstOut.length);
      firstOut = new int[size];
      level = new int[size];
      iter = new int[size];
      queue = new int[size];
      excess = new int[size];
      component = new int[size];
      index = new int[size];
      lowLink = new int[size];
      stack = new int[size];
      onStack = new boolean[size];
      callNode = new int[size];
    }
    if (callArc.length < Math.max(total, 2 * arcs + 2 * nodes)) {
      callArc = new int[Math.max(total, 2 * arcs + 2 * nodes)];
    }
  }

  private void ensureHalfArcs(int count) {
    if (head.length < count) {
      int size = Math.max(count, 2 * head.length);
      head = new int[size];
      cap = new int[size];
      nextOut = new int[size];
    }
  }
}
