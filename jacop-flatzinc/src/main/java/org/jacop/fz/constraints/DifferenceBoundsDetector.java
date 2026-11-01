/*
 * DifferenceBoundsDetector.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.constraints;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It tightens the bounds of the variables of the difference constraints x - y &lt;= c of a model
 * (int_lin_le and int_lin_eq on [1, -1], int_le, int_lt) to their shortest-path bounds, before any
 * constraint is posted, and finds a negative cycle among them. Bounds propagation reaches the same
 * bounds, but on a cycle of negative weight it only moves them by the weight of the cycle each time
 * round, so with wide domains it may run for hours before the model fails (2009 prop_stress: a
 * cycle of weight -1 through 80,000 constraints over 0..160000). Bellman-Ford with a queue (SPFA)
 * finds the cycle after at most as many rounds as there are variables, and in the other models it
 * computes the bounds propagation would compute anyway.
 *
 * <p>The work is bounded; the bounds found when the budget runs out are still sound, so they are
 * kept. Setting the system property {@code org.jacop.fz.differenceBounds} to false turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class DifferenceBoundsDetector implements ParserTreeConstants {

  /** The most edge relaxations of each of the two passes (property jacop.fz.differenceBudget). */
  static final long BUDGET = Long.getLong("jacop.fz.differenceBudget", 200_000_000L);

  private final Support support;

  private final Map<IntVar, Integer> index = new IdentityHashMap<>();
  private final List<IntVar> vars = new ArrayList<>();

  // edge k: x[from[k]] - x[to[k]] <= weight[k]
  private int[] from = new int[16];
  private int[] to = new int[16];
  private long[] weight = new long[16];
  private int edges;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public DifferenceBoundsDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.differenceBounds is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.differenceBounds"));
  }

  /**
   * It reads the difference constraints of the model and tightens the bounds of their variables.
   *
   * @param astTree the root of the parsed model.
   * @throws FailException when the difference constraints have no solution in the domains.
   */
  public void detect(SimpleNode astTree) {
    Support.forEachConstraint(astTree, this::collect);
    if (edges == 0) {
      return;
    }
    int n = vars.size();
    long[] upper = new long[n];
    long[] lower = new long[n];
    for (int i = 0; i < n; i++) {
      upper[i] = vars.get(i).max();
      lower[i] = vars.get(i).min();
    }
    // upper bounds: x[u] <= x[v] + c; lower bounds: x[v] >= x[u] - c, the same edges reversed
    boolean upperChanged = shortestPaths(upper, from, to, 1);
    boolean lowerChanged = shortestPaths(lower, to, from, -1);
    if (!upperChanged && !lowerChanged) {
      return;
    }
    Store store = support.store;
    for (int i = 0; i < n; i++) {
      IntVar x = vars.get(i);
      if (lower[i] > upper[i]) {
        throw Store.failException;
      }
      if (lower[i] > x.min() || upper[i] < x.max()) {
        x.domain.in(store.level, x, (int) lower[i], (int) upper[i]);
      }
    }
  }

  /**
   * Relaxes d[head[k]] by sign * (sign * d[tail[k]] + weight[k]) in SPFA order. With sign 1 it
   * lowers upper bounds; with sign -1, on the reversed edges, it raises lower bounds.
   *
   * @return whether a bound changed
   * @throws FailException on a cycle of negative weight
   */
  private boolean shortestPaths(long[] d, int[] head, int[] tail, int sign) {
    int n = d.length;
    // the edges leaving each tail node
    int[] start = new int[n + 1];
    for (int k = 0; k < edges; k++) {
      start[tail[k] + 1]++;
    }
    for (int i = 0; i < n; i++) {
      start[i + 1] += start[i];
    }
    int[] out = new int[edges];
    int[] fill = start.clone();
    for (int k = 0; k < edges; k++) {
      out[fill[tail[k]]++] = k;
    }

    // number of edges of the path that gave d[i]: more than n means a cycle of negative weight
    int[] length = new int[n];
    // the node whose bound gave d[i], or -1: a cycle of these has negative weight (Tarjan), and it
    // shows up long before a path gets n edges
    int[] parent = new int[n];
    Arrays.fill(parent, -1);
    boolean[] queued = new boolean[n];
    ArrayDeque<Integer> queue = new ArrayDeque<>();
    for (int i = 0; i < n; i++) {
      queue.add(i);
      queued[i] = true;
    }
    boolean changed = false;
    long work = 0;
    int polls = 0;
    while (!queue.isEmpty()) {
      int v = queue.poll();
      queued[v] = false;
      for (int e = start[v]; e < start[v + 1]; e++) {
        int k = out[e];
        int u = head[k];
        // sign 1: d[u] <= d[v] + w; sign -1: d[u] >= d[v] - w
        long bound = d[v] + sign * weight[k];
        if (sign * bound < sign * d[u]) {
          d[u] = bound;
          changed = true;
          length[u] = length[v] + 1;
          parent[u] = v;
          if (length[u] > n) {
            throw Store.failException;
          }
          if (!queued[u]) {
            queued[u] = true;
            queue.add(u);
          }
        }
      }
      work += start[v + 1] - start[v];
      if (++polls % n == 0 && hasCycle(parent)) {
        throw Store.failException;
      }
      if (work > BUDGET || (polls & 0xFFFF) == 0 && support.options.timeOutPassed()) {
        // every bound found so far follows from the constraints
        return changed;
      }
    }
    return changed;
  }

  // whether the parent pointers make a cycle, in O(n)
  static boolean hasCycle(int[] parent) {
    int n = parent.length;
    // 0: not seen, 1: on the current walk, 2: done
    byte[] state = new byte[n];
    for (int i = 0; i < n; i++) {
      int v = i;
      while (v >= 0 && state[v] == 0) {
        state[v] = 1;
        v = parent[v];
      }
      if (v >= 0 && state[v] == 1) {
        return true;
      }
      for (v = i; v >= 0 && state[v] == 1; v = parent[v]) {
        state[v] = 2;
      }
    }
    return false;
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_lin_le" -> linear(node, false);
      case "int_lin_eq" -> linear(node, true);
      case "int_le" -> edge(var(node, 0), var(node, 1), 0);
      case "int_lt" -> edge(var(node, 0), var(node, 1), -1);
      default -> {
        // not a difference constraint
      }
    }
  }

  // a[0] * x[0] + a[1] * x[1] <= c (or = c) with {a[0], a[1]} = {1, -1}
  private void linear(ASTConstElem node, boolean equation) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (a == null || a.length != 2 || a[0] != -a[1] || Math.abs(a[0]) != 1) {
      return;
    }
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (x.length != 2) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    IntVar plus = a[0] == 1 ? x[0] : x[1];
    IntVar minus = a[0] == 1 ? x[1] : x[0];
    edge(plus, minus, c);
    if (equation) {
      edge(minus, plus, -c);
    }
  }

  private IntVar var(ASTConstElem node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  // x - y <= c
  private void edge(IntVar x, IntVar y, long c) {
    if (x == y) {
      if (c < 0) {
        throw Store.failException;
      }
      return;
    }
    if (edges == from.length) {
      from = Arrays.copyOf(from, 2 * edges);
      to = Arrays.copyOf(to, 2 * edges);
      weight = Arrays.copyOf(weight, 2 * edges);
    }
    from[edges] = node(x);
    to[edges] = node(y);
    weight[edges] = c;
    edges++;
  }

  private int node(IntVar x) {
    return index.computeIfAbsent(
        x,
        v -> {
          vars.add(v);
          return vars.size() - 1;
        });
  }
}
