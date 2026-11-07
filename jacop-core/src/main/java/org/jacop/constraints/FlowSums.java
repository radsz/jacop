/*
 * FlowSums.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Sums over the edges of a bipartite graph: each edge e carries an integer x[e], and each node v of
 * either side has the sum of the x of its edges within a range, {@code min_v <= sum_{e at v} x[e]
 * <= max_v}, and, when it has a total variable, equal to {@code total_v + offset_v}. An edge may
 * have no node on one side. These are the rows and columns of an integer matrix with bounded row
 * and column sums, and the games and teams of a competition: each game is a left node whose edges,
 * one per team that plays it, carry the points the team gets from the game, the game's range holds
 * the points a game gives out (2 or 3 for a 3-1-0 rule, exactly 1 for a tournament with one point
 * per game) and each team is a right node whose total is its final score less its points so far.
 *
 * <p>The constraint propagates the network flow relaxation of these sums, with every variable
 * between its bounds (holes are ignored): a source feeds each left node within its range, each edge
 * is an arc from its left node to its right node with the bounds of x[e], each right node feeds a
 * sink within its range, and the sink returns the flow to the source. By Hoffman's circulation
 * theorem (A. J. Hoffman, "Some recent applications of the theory of linear inequalities to
 * extremal combinatorial analysis", Proc. Symposia in Applied Mathematics 10, 1960) the sums have a
 * solution within the bounds exactly when for every set X of nodes the lower bounds of the arcs
 * entering X do not exceed the upper bounds of the arcs leaving it. For a 0/1 matrix with fixed row
 * and column sums this is the Gale-Ryser theorem (D. Gale, "A theorem on flows in networks",
 * Pacific J. Math. 7, 1957; H. J. Ryser, "Combinatorial properties of matrices of zeros and ones",
 * Canadian J. Math. 9, 1957); for the score sequences of a round robin tournament it is Landau's
 * theorem (H. G. Landau, "On dominance relations and the structure of animal societies III: the
 * condition for a score structure", Bull. Math. Biophysics 15, 1953); and asking for the most
 * points a team can still reach while the others stay within their bounds is the elimination
 * question of B. L. Schwartz ("Possible winners in partially completed tournaments", SIAM Review
 * 8(3), 1966). Under the 3-1-0 rule that question is NP-complete (W. Kern and D. Paulusma, "The new
 * FIFA rules are hard: complexity aspects of sports competitions", Discrete Applied Math. 108(3),
 * 2001); the flow relaxation, which lets a game also give 2-0 or 2-1, is what this constraint
 * decides.
 *
 * <p>Each call repairs the flow of the previous call into a feasible flow of the current bounds by
 * augmenting paths (Dinic's blocking flows: E. A. Dinic, "Algorithm for solution of a problem of
 * maximum flow in networks with power estimation", Soviet Math. Doklady 11, 1970) and fails when
 * none exists. Then:
 *
 * <ul>
 *   <li>each total is narrowed to the least and the greatest flow its node can carry, found by
 *       pushing flow round the residual network through the node's arc (bounds(Z) consistency of
 *       the totals for the relaxation);
 *   <li>an edge whose flow is at one of its bounds, and whose two nodes are in different strongly
 *       connected components of the residual network, cannot leave that bound in any flow, so its
 *       variable is fixed to it, as in the flow based filtering of J.-C. R&eacute;gin ("Generalized
 *       arc consistency for global cardinality constraint", AAAI 1996).
 * </ul>
 *
 * <p>Under lazy clause generation each deduction, and each failure, is explained by a violated
 * Hoffman condition: the bounds before the atom, with the atom negated, have no flow, and the
 * minimum cut found by the augmenting paths names the bounds of the arcs crossing it, which are the
 * reason. The slack of the cut weakens them where the trail allows.
 *
 * <p>A redundant instance ({@link #setRedundant(boolean)}) switches itself off when it prunes or
 * fails too rarely to pay for its flows.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class FlowSums extends Constraint
    implements SatisfiedPresent, Explainable, Copyable<FlowSums> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * A node of the graph: the sum of its edges is within [min, max] and, with a total variable,
   * equal to total + offset.
   *
   * @param total the total, or null
   * @param offset the sum of the edges less the total
   * @param min the least sum (Integer.MIN_VALUE for none)
   * @param max the greatest sum (Integer.MAX_VALUE for none)
   */
  public record Node(IntVar total, int offset, int min, int max) {

    /**
     * A node whose sum is total + offset.
     *
     * @param total the total
     * @param offset the sum less the total
     * @return the node
     */
    public static Node of(IntVar total, int offset) {
      return new Node(total, offset, Integer.MIN_VALUE, Integer.MAX_VALUE);
    }

    /**
     * A node whose sum is within a range.
     *
     * @param min the least sum
     * @param max the greatest sum
     * @return the node
     */
    public static Node of(int min, int max) {
      return new Node(null, 0, min, max);
    }
  }

  // calls per window of the switch-off rule, and the deductions per window below which it stops
  private static final int WINDOW = 10_000;
  private static final int MIN_DEDUCTIONS = 10;

  // an unbounded side of an arc: far above any sum of int bounds, and far from overflow
  private static final long BIG = 1L << 60;

  /** The edge variables. */
  final IntVar[] x;

  /** The left node of each edge, -1 for none. */
  final int[] left;

  /** The right node of each edge, -1 for none. */
  final int[] right;

  final Node[] leftNodes;
  final Node[] rightNodes;

  // the network: node 0 is the source, 1 the sink, then the left and the right nodes
  private final int nodes;
  private final int arcs;
  private final int[] from;
  private final int[] to;
  // the variable of each arc (an edge variable or a total), its offset and its constant bounds
  private final IntVar[] arcVar;
  private final long[] arcOffset;
  private final long[] arcMin;
  private final long[] arcMax;

  // adjacency: for each node, codes 2 * arc (leaving) or 2 * arc + 1 (entering)
  private final int[] adjStart;
  private final int[] adj;

  // the arcs of the totals, whose bounds are narrowed exactly
  private final int[] totalArcs;

  // the arcs of each variable
  private final Map<IntVar, int[]> arcsOf = new IdentityHashMap<>();

  // the bounds and the flow of the current call, kept as the start of the next one
  private final long[] lo;
  private final long[] hi;
  private final long[] flow;

  // scratch for the explanations
  private final long[] elo;
  private final long[] ehi;
  private final long[] eflow;
  private final long[] rootLo;
  private final long[] rootHi;

  // the max-flow work arrays
  private final long[] supply;
  private final long[] demand;
  private final int[] level;
  private final int[] iter;
  private final int[] queue;
  private final int[] comp;
  private final int[] low;
  private final int[] order;
  private final int[] stack;
  private final int[] callStack;
  private final int[] callIter;
  private final boolean[] onStack;
  private final boolean[] cutForward;
  private final boolean[] cutBackward;

  // what is pruned: "all" (default), "totals" or "none" (failures only); for experiments
  private static final String PRUNE = System.getProperty("jacop.flowSums.prune", "all");

  // whether it fails when there is no flow, or leaves that to other constraints; for experiments
  private static final boolean FAIL = !"false".equals(System.getProperty("jacop.flowSums.fail"));

  private static final boolean DEBUG = Boolean.getBoolean("jacop.flowSums.debug");
  private int debugCount;

  private boolean redundant;
  private boolean off;
  private long windowCalls;
  private long windowStart;

  /** Statistics: the failures found. */
  public long failures;

  /** Statistics: the bounds narrowed. */
  public long prunings;

  /**
   * It constructs the constraint.
   *
   * @param x the edge variables
   * @param left the left node of each edge, -1 for none
   * @param right the right node of each edge, -1 for none
   * @param leftNodes the left nodes
   * @param rightNodes the right nodes
   */
  public FlowSums(IntVar[] x, int[] left, int[] right, Node[] leftNodes, Node[] rightNodes) {
    checkInputForNullness("x", x);
    if (left == null || right == null || leftNodes == null || rightNodes == null) {
      throw new IllegalArgumentException("FlowSums: null argument.");
    }
    if (left.length != x.length || right.length != x.length) {
      throw new IllegalArgumentException("FlowSums needs both nodes of every edge.");
    }
    this.numberId = idNumber.incrementAndGet();
    this.x = Arrays.copyOf(x, x.length);
    this.left = Arrays.copyOf(left, left.length);
    this.right = Arrays.copyOf(right, right.length);
    this.leftNodes = Arrays.copyOf(leftNodes, leftNodes.length);
    this.rightNodes = Arrays.copyOf(rightNodes, rightNodes.length);

    int nl = leftNodes.length;
    int nr = rightNodes.length;
    nodes = 2 + nl + nr;
    arcs = x.length + nl + nr + 1;
    from = new int[arcs];
    to = new int[arcs];
    arcVar = new IntVar[arcs];
    arcOffset = new long[arcs];
    arcMin = new long[arcs];
    arcMax = new long[arcs];
    List<IntVar> scope = new ArrayList<>();
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (int e = 0; e < x.length; e++) {
      if (left[e] < -1 || left[e] >= nl || right[e] < -1 || right[e] >= nr) {
        throw new IllegalArgumentException("FlowSums: edge " + e + " has no such node.");
      }
      if (left[e] < 0 && right[e] < 0) {
        throw new IllegalArgumentException("FlowSums: edge " + e + " has no node.");
      }
      from[e] = left[e] >= 0 ? 2 + left[e] : 0;
      to[e] = right[e] >= 0 ? 2 + nl + right[e] : 1;
      arcVar[e] = x[e];
      arcMin[e] = -BIG;
      arcMax[e] = BIG;
      addVariable(x[e], seen, scope);
    }
    int a = x.length;
    List<Integer> totals = new ArrayList<>();
    for (int i = 0; i < nl + nr; i++, a++) {
      Node node = i < nl ? leftNodes[i] : rightNodes[i - nl];
      if (node == null) {
        throw new IllegalArgumentException("FlowSums: null node.");
      }
      from[a] = i < nl ? 0 : 2 + i;
      to[a] = i < nl ? 2 + i : 1;
      arcVar[a] = node.total();
      arcOffset[a] = node.offset();
      arcMin[a] = node.min() == Integer.MIN_VALUE ? -BIG : node.min();
      arcMax[a] = node.max() == Integer.MAX_VALUE ? BIG : node.max();
      if (node.total() != null) {
        addVariable(node.total(), seen, scope);
        totals.add(a);
      }
    }
    // the sink returns the flow to the source
    from[a] = 1;
    to[a] = 0;
    arcMin[a] = -BIG;
    arcMax[a] = BIG;
    totalArcs = totals.stream().mapToInt(Integer::intValue).toArray();
    for (int k = 0; k < arcs; k++) {
      if (arcVar[k] != null) {
        arcsOf.put(arcVar[k], new int[] {k});
      }
    }

    int[] degree = new int[nodes + 1];
    for (int k = 0; k < arcs; k++) {
      degree[from[k]]++;
      degree[to[k]]++;
    }
    adjStart = new int[nodes + 1];
    for (int v = 0; v < nodes; v++) {
      adjStart[v + 1] = adjStart[v] + degree[v];
    }
    adj = new int[adjStart[nodes]];
    int[] fill = Arrays.copyOf(adjStart, nodes);
    for (int k = 0; k < arcs; k++) {
      adj[fill[from[k]]++] = 2 * k;
      adj[fill[to[k]]++] = 2 * k + 1;
    }

    lo = new long[arcs];
    hi = new long[arcs];
    flow = new long[arcs];
    elo = new long[arcs];
    ehi = new long[arcs];
    eflow = new long[arcs];
    rootLo = new long[arcs];
    rootHi = new long[arcs];
    supply = new long[nodes];
    demand = new long[nodes];
    level = new int[nodes];
    iter = new int[nodes];
    queue = new int[nodes];
    comp = new int[nodes];
    low = new int[nodes];
    order = new int[nodes];
    stack = new int[nodes];
    callStack = new int[nodes];
    callIter = new int[nodes];
    onStack = new boolean[nodes];
    cutForward = new boolean[nodes];
    cutBackward = new boolean[nodes];

    this.queueIndex = Integer.getInteger("jacop.flowSums.queue", 3);
    setScope(scope.toArray(new IntVar[0]));
  }

  private static void addVariable(IntVar v, Map<IntVar, Boolean> seen, List<IntVar> scope) {
    if (v == null) {
      throw new IllegalArgumentException("FlowSums: null variable.");
    }
    if (seen.put(v, Boolean.TRUE) != null) {
      throw new IllegalArgumentException("FlowSums: variable " + v + " is used twice.");
    }
    scope.add(v);
  }

  /**
   * It tells the constraint that other constraints of the model imply it, so it may stop
   * propagating when it prunes too rarely: fewer than ten failures or narrowed bounds in ten
   * thousand calls.
   *
   * @param redundant true if other constraints imply the constraint
   */
  public void setRedundant(boolean redundant) {
    this.redundant = redundant;
  }

  /**
   * It tells whether a redundant instance has switched itself off.
   *
   * @return true if it no longer propagates
   */
  public boolean isOff() {
    return off;
  }

  /**
   * It returns the number of edges.
   *
   * @return the number of edges
   */
  public int numberOfEdges() {
    return x.length;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  // ---- bounds of the arcs

  // the bounds of arc a for the variable bounds vmin and vmax
  private long arcLow(int a, long vmin) {
    return arcVar[a] == null ? arcMin[a] : Math.max(arcMin[a], vmin + arcOffset[a]);
  }

  private long arcHigh(int a, long vmax) {
    return arcVar[a] == null ? arcMax[a] : Math.min(arcMax[a], vmax + arcOffset[a]);
  }

  private void readBounds() {
    for (int a = 0; a < arcs; a++) {
      IntVar v = arcVar[a];
      lo[a] = arcLow(a, v == null ? 0 : v.min());
      hi[a] = arcHigh(a, v == null ? 0 : v.max());
    }
  }

  // ---- flows

  private long residual(int code, long[] f, long[] l, long[] h) {
    int a = code >> 1;
    return (code & 1) == 0 ? h[a] - f[a] : f[a] - l[a];
  }

  private int other(int code) {
    int a = code >> 1;
    return (code & 1) == 0 ? to[a] : from[a];
  }

  // breadth first levels from the nodes with supply; true when a node with demand is reached
  private boolean levels(long[] f, long[] l, long[] h, int excluded) {
    Arrays.fill(level, -1);
    int head = 0;
    int tail = 0;
    for (int v = 0; v < nodes; v++) {
      if (supply[v] > 0) {
        level[v] = 0;
        queue[tail++] = v;
      }
    }
    boolean reached = false;
    while (head < tail) {
      int v = queue[head++];
      if (demand[v] > 0) {
        reached = true;
      }
      for (int k = adjStart[v]; k < adjStart[v + 1]; k++) {
        int code = adj[k];
        if ((code >> 1) == excluded || residual(code, f, l, h) <= 0) {
          continue;
        }
        int w = other(code);
        if (level[w] < 0) {
          level[w] = level[v] + 1;
          queue[tail++] = w;
        }
      }
    }
    return reached;
  }

  // sends at most amount from v along the level graph to a node with demand
  private long send(int v, long amount, long[] f, long[] l, long[] h, int excluded) {
    if (demand[v] > 0) {
      long d = Math.min(amount, demand[v]);
      demand[v] -= d;
      return d;
    }
    for (; iter[v] < adjStart[v + 1]; iter[v]++) {
      int code = adj[iter[v]];
      if ((code >> 1) == excluded) {
        continue;
      }
      int w = other(code);
      if (level[w] != level[v] + 1) {
        continue;
      }
      long r = residual(code, f, l, h);
      if (r <= 0) {
        continue;
      }
      long d = send(w, Math.min(amount, r), f, l, h, excluded);
      if (d > 0) {
        int a = code >> 1;
        f[a] += (code & 1) == 0 ? d : -d;
        return d;
      }
    }
    return 0;
  }

  // moves the supplies to the demands by blocking flows; afterwards level marks, when supply is
  // left, the nodes reachable from it, none of which has demand
  private void maxFlow(long[] f, long[] l, long[] h, int excluded) {
    while (levels(f, l, h, excluded)) {
      for (int v = 0; v < nodes; v++) {
        iter[v] = adjStart[v];
      }
      for (int s = 0; s < nodes; s++) {
        while (supply[s] > 0) {
          long d = send(s, supply[s], f, l, h, excluded);
          if (d == 0) {
            break;
          }
          supply[s] -= d;
        }
      }
    }
  }

  // makes f a flow within l and h; false, with the cut in level, when there is none
  private boolean route(long[] f, long[] l, long[] h) {
    Arrays.fill(supply, 0);
    for (int a = 0; a < arcs; a++) {
      if (l[a] > h[a]) {
        return false;
      }
      if (f[a] < l[a]) {
        f[a] = l[a];
      } else if (f[a] > h[a]) {
        f[a] = h[a];
      }
      supply[to[a]] += f[a];
      supply[from[a]] -= f[a];
    }
    boolean balanced = true;
    for (int v = 0; v < nodes; v++) {
      if (supply[v] < 0) {
        demand[v] = -supply[v];
        supply[v] = 0;
        balanced = false;
      } else {
        demand[v] = 0;
      }
    }
    if (balanced) {
      return true;
    }
    maxFlow(f, l, h, -1);
    for (int v = 0; v < nodes; v++) {
      if (supply[v] > 0) {
        return false;
      }
    }
    return true;
  }

  // pushes as much flow as it can, at most limit, round the residual network through arc a, up
  // (more flow on a) or down; returns the amount
  private long push(int a, boolean up, long limit) {
    if (limit <= 0) {
      return 0;
    }
    Arrays.fill(supply, 0);
    Arrays.fill(demand, 0);
    int s = up ? to[a] : from[a];
    int t = up ? from[a] : to[a];
    supply[s] = limit;
    demand[t] = limit;
    maxFlow(flow, lo, hi, a);
    long moved = limit - supply[s];
    flow[a] += up ? moved : -moved;
    return moved;
  }

  // ---- strongly connected components of the residual network (Tarjan, iterative)

  private void components() {
    Arrays.fill(order, -1);
    Arrays.fill(onStack, false);
    int counter = 0;
    int top = 0;
    int components = 0;
    for (int root = 0; root < nodes; root++) {
      if (order[root] >= 0) {
        continue;
      }
      int depth = 0;
      callStack[0] = root;
      callIter[0] = adjStart[root];
      order[root] = low[root] = counter++;
      stack[top++] = root;
      onStack[root] = true;
      while (depth >= 0) {
        int v = callStack[depth];
        if (callIter[depth] < adjStart[v + 1]) {
          int code = adj[callIter[depth]++];
          if (residual(code, flow, lo, hi) <= 0) {
            continue;
          }
          int w = other(code);
          if (order[w] < 0) {
            order[w] = low[w] = counter++;
            stack[top++] = w;
            onStack[w] = true;
            depth++;
            callStack[depth] = w;
            callIter[depth] = adjStart[w];
          } else if (onStack[w]) {
            low[v] = Math.min(low[v], order[w]);
          }
        } else {
          if (low[v] == order[v]) {
            int w;
            do {
              w = stack[--top];
              onStack[w] = false;
              comp[w] = components;
            } while (w != v);
            components++;
          }
          depth--;
          if (depth >= 0) {
            int u = callStack[depth];
            low[u] = Math.min(low[u], low[v]);
          }
        }
      }
    }
  }

  // ---- propagation

  @Override
  public void consistency(Store store) {
    if (off) {
      return;
    }
    if (redundant && ++windowCalls == WINDOW) {
      if (failures + prunings - windowStart < MIN_DEDUCTIONS) {
        off = true;
        return;
      }
      windowCalls = 0;
      windowStart = failures + prunings;
    }
    boolean changed;
    do {
      changed = false;
      readBounds();
      if (!route(flow, lo, hi)) {
        failures++;
        if (!FAIL) {
          // another constraint (the linear relaxation) is left to find it
          return;
        }
        throw Store.failException;
      }
      if ("none".equals(PRUNE)) {
        return;
      }
      for (int a : "scc".equals(PRUNE) ? new int[0] : totalArcs) {
        long max = flow[a] + push(a, true, hi[a] - flow[a]);
        long min = flow[a] - push(a, false, flow[a] - lo[a]);
        // also where a constant bound of the node is tighter than the total's
        IntVar v = arcVar[a];
        int vmin = (int) Math.max(v.min(), min - arcOffset[a]);
        int vmax = (int) Math.min(v.max(), max - arcOffset[a]);
        if (vmin > v.min() || vmax < v.max()) {
          prunings++;
          changed = true;
          v.domain.in(store.level, v, vmin, vmax);
          lo[a] = arcLow(a, v.min());
          hi[a] = arcHigh(a, v.max());
        }
      }
      if (changed) {
        continue;
      }
      if (!"all".equals(PRUNE)) {
        return;
      }
      components();
      if ("scc".equals(PRUNE)) {
        for (int a : totalArcs) {
          if (lo[a] == hi[a] || comp[from[a]] == comp[to[a]]) {
            continue;
          }
          IntVar v = arcVar[a];
          if (flow[a] == lo[a] && lo[a] - arcOffset[a] < v.max()) {
            prunings++;
            changed = true;
            v.domain.in(store.level, v, v.min(), (int) (lo[a] - arcOffset[a]));
          } else if (flow[a] == hi[a] && hi[a] - arcOffset[a] > v.min()) {
            prunings++;
            changed = true;
            v.domain.in(store.level, v, (int) (hi[a] - arcOffset[a]), v.max());
          }
        }
      }
      for (int e = 0; e < x.length; e++) {
        if (lo[e] == hi[e] || comp[from[e]] == comp[to[e]]) {
          continue;
        }
        IntVar v = x[e];
        if (flow[e] == lo[e]) {
          prunings++;
          changed = true;
          v.domain.in(store.level, v, v.min(), (int) lo[e]);
        } else if (flow[e] == hi[e]) {
          prunings++;
          changed = true;
          v.domain.in(store.level, v, (int) hi[e], v.max());
        }
      }
    } while (changed);
  }

  @Override
  public boolean satisfied() {
    for (IntVar v : x) {
      if (!v.singleton()) {
        return false;
      }
    }
    long[] sums = new long[leftNodes.length + rightNodes.length];
    for (int e = 0; e < x.length; e++) {
      if (left[e] >= 0) {
        sums[left[e]] += x[e].value();
      }
      if (right[e] >= 0) {
        sums[leftNodes.length + right[e]] += x[e].value();
      }
    }
    for (int i = 0; i < sums.length; i++) {
      Node node = i < leftNodes.length ? leftNodes[i] : rightNodes[i - leftNodes.length];
      if (sums[i] < node.min() || sums[i] > node.max()) {
        return false;
      }
      if (node.total() != null
          && (!node.total().singleton()
              || sums[i] != node.total().value() + (long) node.offset())) {
        return false;
      }
    }
    return true;
  }

  // ---- explanations

  // the bounds before a position, tightened to values of the initial domains; the atom of
  // variable y, if any, negated: y <= value - 1 for a lower bound (ge), y >= value + 1 otherwise
  private boolean boundsBefore(AtomicTrail trail, int position, IntVar y, boolean ge, long value) {
    for (int a = 0; a < arcs; a++) {
      IntVar v = arcVar[a];
      if (v == null) {
        elo[a] = arcMin[a];
        ehi[a] = arcMax[a];
        rootLo[a] = elo[a];
        rootHi[a] = ehi[a];
        continue;
      }
      long vmin = trail.minBefore(v, position);
      long vmax = trail.maxBefore(v, position);
      if (v == y) {
        if (ge) {
          vmax = Math.min(vmax, value - 1);
        } else {
          vmin = Math.max(vmin, value + 1);
        }
      }
      if (vmin > vmax) {
        return false;
      }
      IntDomain root = trail.rootDomain(v);
      if (vmin > root.max() || vmax < root.min()) {
        return false;
      }
      rootLo[a] = arcLow(a, root.min());
      rootHi[a] = arcHigh(a, root.max());
      vmin = up(root, vmin);
      vmax = down(root, vmax);
      if (vmin > vmax) {
        return false;
      }
      elo[a] = arcLow(a, vmin);
      ehi[a] = arcHigh(a, vmax);
    }
    return true;
  }

  // the least value of the domain of at least v (v within the domain's bounds)
  private static long up(IntDomain d, long v) {
    if (v <= d.min()) {
      return d.min();
    }
    return d.contains((int) v) ? v : d.nextValue((int) v);
  }

  private static long down(IntDomain d, long v) {
    if (v >= d.max()) {
      return d.max();
    }
    return d.contains((int) v) ? v : d.previousValue((int) v);
  }

  // the reason of the cut in level: the lower bounds entering it and the upper bounds leaving it,
  // weakened by its slack; skip is the variable of the negated atom on side ge
  private boolean cutReason(
      AtomicTrail trail, int position, IntVar y, boolean ge, boolean[] inCut, EntryList out) {
    // an arc with empty bounds is its own reason
    for (int a = 0; a < arcs; a++) {
      if (elo[a] > ehi[a]) {
        IntVar v = arcVar[a];
        if (v == null) {
          return false;
        }
        if (elo[a] > arcMin[a] && !(v == y && !ge)) {
          trail.addLowerBound(v, position, out);
        }
        if (ehi[a] < arcMax[a] && !(v == y && ge)) {
          trail.addUpperBound(v, position, out);
        }
        return true;
      }
    }
    long entering = 0;
    long leaving = 0;
    for (int a = 0; a < arcs; a++) {
      boolean in = inCut[to[a]];
      boolean out0 = inCut[from[a]];
      if (in && !out0) {
        if (elo[a] <= -BIG) {
          return false;
        }
        entering += elo[a];
      } else if (out0 && !in) {
        if (ehi[a] >= BIG) {
          return false;
        }
        leaving += ehi[a];
      }
    }
    long slack = entering - leaving - 1;
    if (slack < 0) {
      return false;
    }
    for (int a = 0; a < arcs; a++) {
      IntVar v = arcVar[a];
      if (v == null) {
        continue;
      }
      boolean in = inCut[to[a]];
      boolean out0 = inCut[from[a]];
      if (in && !out0) {
        // a lower bound of v; the negated atom when v is y and it was an upper bound
        if (elo[a] <= arcMin[a] || (v == y && !ge)) {
          continue;
        }
        long need = elo[a] - slack;
        if (need <= arcMin[a]) {
          slack -= elo[a] - arcMin[a];
          continue;
        }
        long limit = Math.min(need - arcOffset[a], trail.minBefore(v, position));
        long got = trail.addBoundReaching(v, position, true, limit, out);
        long used = Math.max(arcMin[a], up(trail.rootDomain(v), got) + arcOffset[a]);
        slack -= elo[a] - Math.min(elo[a], used);
      } else if (out0 && !in) {
        if (ehi[a] >= arcMax[a] || (v == y && ge)) {
          continue;
        }
        long need = ehi[a] + slack;
        if (need >= arcMax[a]) {
          slack -= arcMax[a] - ehi[a];
          continue;
        }
        long limit = Math.max(need - arcOffset[a], trail.maxBefore(v, position));
        long got = trail.addBoundReaching(v, position, false, limit, out);
        long used = Math.min(arcMax[a], down(trail.rootDomain(v), got) + arcOffset[a]);
        slack -= Math.max(ehi[a], used) - ehi[a];
      }
    }
    return true;
  }

  private boolean explainAt(
      AtomicTrail trail, int position, IntVar y, boolean ge, long value, EntryList out) {
    if (!boundsBefore(trail, position, y, ge, value)) {
      // the negated atom contradicts the bounds of y itself
      return false;
    }
    System.arraycopy(flow, 0, eflow, 0, arcs);
    if (route(eflow, elo, ehi)) {
      return false;
    }
    // two violated sets: the nodes the supply left over reaches, and the complement of those that
    // reach the demand left over; the one with fewer bounds that take part
    for (int v = 0; v < nodes; v++) {
      cutForward[v] = level[v] >= 0;
    }
    reaching();
    boolean[] cut =
        literals(cutForward, y, ge) <= literals(cutBackward, y, ge) ? cutForward : cutBackward;
    int before = literals(cut, y, ge);
    shrink(cut, y, ge);
    if (DEBUG && debugCount++ < 30) {
      StringBuilder b = new StringBuilder("FlowSums cut: lits " + before + " -> ");
      b.append(literals(cut, y, ge))
          .append(" y=")
          .append(y)
          .append(ge ? " ge " : " le ")
          .append(value);
      int nl = leftNodes.length;
      int inL = 0;
      int inR = 0;
      for (int v = 2; v < nodes; v++) {
        if (cut[v]) {
          if (v < 2 + nl) {
            inL++;
          } else {
            inR++;
          }
        }
      }
      b.append(" S=").append(cut[0]).append(" T=").append(cut[1]);
      b.append(" left=").append(inL).append(" right=").append(inR).append(" :");
      for (int a = 0; a < arcs; a++) {
        if (takes(a, cut[from[a]], cut[to[a]], y, ge)) {
          boolean entering = cut[to[a]];
          b.append(' ').append(arcVar[a].id()).append(entering ? ">=" : "<=");
          b.append(entering ? elo[a] - arcOffset[a] : ehi[a] - arcOffset[a]);
          b.append(a < x.length ? "e" : "t");
        }
      }
      System.out.println(b);
    }
    return cutReason(trail, position, y, ge, cut, out);
  }

  // the part of arc a in a cut's condition (lower bound entering, minus upper bound leaving): 0
  // when it does not cross, Long.MIN_VALUE when its bound is unbounded
  private long part(int a, boolean fromIn, boolean toIn) {
    if (toIn && !fromIn) {
      return elo[a] <= -BIG ? Long.MIN_VALUE : elo[a];
    }
    if (fromIn && !toIn) {
      return ehi[a] >= BIG ? Long.MIN_VALUE : -ehi[a];
    }
    return 0;
  }

  // whether arc a puts a bound of its variable in the reason
  private boolean takes(int a, boolean fromIn, boolean toIn, IntVar y, boolean ge) {
    IntVar v = arcVar[a];
    if (v == null) {
      return false;
    }
    if (toIn && !fromIn) {
      return elo[a] > rootLo[a] && !(v == y && !ge);
    }
    if (fromIn && !toIn) {
      return ehi[a] < rootHi[a] && !(v == y && ge);
    }
    return false;
  }

  // moves single nodes in or out of the violated set while it stays violated and takes fewer
  // bounds: a smaller reason than the cut the flow happened to stop at
  private void shrink(boolean[] inCut, IntVar y, boolean ge) {
    long sum = 0;
    for (int a = 0; a < arcs; a++) {
      long p = part(a, inCut[from[a]], inCut[to[a]]);
      if (p == Long.MIN_VALUE) {
        return;
      }
      sum += p;
    }
    if (sum <= 0) {
      return;
    }
    for (int pass = 0; pass < 4; pass++) {
      boolean improved = false;
      for (int v = 0; v < nodes; v++) {
        long delta = 0;
        int literalDelta = 0;
        boolean unbounded = false;
        for (int k = adjStart[v]; k < adjStart[v + 1] && !unbounded; k++) {
          int a = adj[k] >> 1;
          boolean fi = inCut[from[a]];
          boolean ti = inCut[to[a]];
          // toggled: v is one end of a (not both, arcs join different nodes)
          boolean nfi = from[a] == v ? !fi : fi;
          boolean nti = to[a] == v ? !ti : ti;
          long now = part(a, nfi, nti);
          if (now == Long.MIN_VALUE) {
            unbounded = true;
            continue;
          }
          delta += now - part(a, fi, ti);
          literalDelta += (takes(a, nfi, nti, y, ge) ? 1 : 0) - (takes(a, fi, ti, y, ge) ? 1 : 0);
        }
        if (unbounded || sum + delta <= 0) {
          continue;
        }
        if (literalDelta < 0 || (literalDelta == 0 && delta > 0)) {
          inCut[v] = !inCut[v];
          sum += delta;
          improved = true;
        }
      }
      if (!improved) {
        break;
      }
    }
  }

  // cutBackward: the nodes that cannot reach a node with demand in the residual network of eflow
  private void reaching() {
    Arrays.fill(cutBackward, true);
    int head = 0;
    int tail = 0;
    for (int v = 0; v < nodes; v++) {
      if (demand[v] > 0) {
        cutBackward[v] = false;
        queue[tail++] = v;
      }
    }
    while (head < tail) {
      int w = queue[head++];
      for (int k = adjStart[w]; k < adjStart[w + 1]; k++) {
        int code = adj[k];
        int u = other(code);
        // the residual arc from u to w is the opposite direction of code
        if (cutBackward[u] && residual(code ^ 1, eflow, elo, ehi) > 0) {
          cutBackward[u] = false;
          queue[tail++] = u;
        }
      }
    }
  }

  // the bounds of variables a cut's reason takes, before weakening
  private int literals(boolean[] inCut, IntVar y, boolean ge) {
    int count = 0;
    for (int a = 0; a < arcs; a++) {
      IntVar v = arcVar[a];
      if (v == null) {
        continue;
      }
      boolean in = inCut[to[a]];
      boolean out0 = inCut[from[a]];
      if (in && !out0 && elo[a] > rootLo[a] && !(v == y && !ge)) {
        count++;
      } else if (out0 && !in && ehi[a] < rootHi[a] && !(v == y && ge)) {
        count++;
      }
    }
    return count;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (kind != AtomicTrail.GE && kind != AtomicTrail.LE) {
      return false;
    }
    IntVar y = trail.variable(entry);
    if (!arcsOf.containsKey(y)) {
      return false;
    }
    return explainAt(trail, entry, y, kind == AtomicTrail.GE, trail.value(entry), out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return explainAt(trail, trail.size(), null, true, 0, out);
  }

  @Override
  public boolean checksReasons() {
    return true;
  }

  @Override
  public FlowSums copy(VarMap map) {
    Node[] l = new Node[leftNodes.length];
    for (int i = 0; i < l.length; i++) {
      l[i] = copy(leftNodes[i], map);
    }
    Node[] r = new Node[rightNodes.length];
    for (int i = 0; i < r.length; i++) {
      r[i] = copy(rightNodes[i], map);
    }
    FlowSums c = new FlowSums(map.get(x), left, right, l, r);
    c.setRedundant(redundant);
    return c;
  }

  private static Node copy(Node n, VarMap map) {
    return new Node(n.total() == null ? null : map.get(n.total()), n.offset(), n.min(), n.max());
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id()).append(" : FlowSums([");
    for (int e = 0; e < x.length; e++) {
      if (e > 0) {
        result.append(", ");
      }
      result.append(x[e]).append(':').append(left[e]).append('-').append(right[e]);
    }
    result.append("], ").append(Arrays.toString(leftNodes));
    result.append(", ").append(Arrays.toString(rightNodes)).append(")");
    return result.toString();
  }
}
