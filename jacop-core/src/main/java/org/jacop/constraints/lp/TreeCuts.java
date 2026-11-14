/*
 * TreeCuts.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import org.jacop.api.VarMap;
import org.jacop.constraints.graph.Reachable;
import org.jacop.core.IntVar;

/**
 * Generalized subtour elimination cuts of a forest of selected edges over selected nodes (the
 * acyclic {@link Reachable} of {@link org.jacop.constraints.graph.Tree} and {@link
 * org.jacop.constraints.graph.Path}): for every set S of nodes and every node k of S,
 *
 * <pre>
 *   sum(e inside S) y[e] &lt;= sum(i in S, i != k) x[i]
 * </pre>
 *
 * <p>where x are the node Booleans and y the edge Booleans. They hold because the selected edges
 * inside S form a forest over the selected nodes of S, which has fewer edges than nodes, and an
 * edge is selected only with both its nodes. These are the inequalities of the prize-collecting
 * Steiner tree polytope of Lucena and Resende, "Strong lower bounds for the prize collecting
 * Steiner problem in graphs", Discrete Applied Mathematics 141 (2004) 277-294, and of the subtour
 * elimination of Padberg and Wolsey, "Trees and cuts", Annals of Discrete Mathematics 17 (1983)
 * 511-517. A most violated cut for a given k is a maximum weight closure (Picard, "Maximal closure
 * of a graph and applications to combinatorial problems", Management Science 22 (1976) 1268-1272),
 * found here with one maximum flow.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class TreeCuts {

  // the least violation of a cut
  private static final double MIN_VIOLATION = 1e-4;
  // values below it count as 0 in the flow network
  private static final double EPS = 1e-9;
  // the most maximum flows of one separation; each costs about the size of the support graph
  private static final int MAX_FLOWS = 200;

  private final IntVar[] nodes;
  private final IntVar[] edges;
  private final int[] tail;
  private final int[] head;

  /** A cut {@code sum y[edges] - sum x[nodes] <= 0}, over indexes of the node and edge Booleans. */
  public static final class Cut {
    private final int[] cutNodes;
    private final int[] cutEdges;
    private final double efficacy;

    Cut(int[] cutNodes, int[] cutEdges, double efficacy) {
      this.cutNodes = cutNodes;
      this.cutEdges = cutEdges;
      this.efficacy = efficacy;
    }

    /**
     * The nodes with weight -1: those of S other than k.
     *
     * @return indexes into the node Booleans
     */
    public int[] nodes() {
      return cutNodes;
    }

    /**
     * The edges with weight 1: those with both nodes in S.
     *
     * @return indexes into the edge Booleans
     */
    public int[] edges() {
      return cutEdges;
    }

    /**
     * The violation of the cut divided by the norm of its weights.
     *
     * @return the efficacy
     */
    public double efficacy() {
      return efficacy;
    }
  }

  /**
   * It returns the cuts of an acyclic {@link Reachable}, or null for any other constraint.
   *
   * @param c a constraint
   * @return the cuts, or null
   */
  public static TreeCuts of(Object c) {
    if (c instanceof Reachable r && r.acyclic() && r.edges().length > 1) {
      return new TreeCuts(r.nodes(), r.edges(), r.tails(), r.heads());
    }
    return null;
  }

  TreeCuts(IntVar[] nodes, IntVar[] edges, int[] tail, int[] head) {
    this.nodes = nodes;
    this.edges = edges;
    this.tail = tail;
    this.head = head;
  }

  /**
   * The node Booleans followed by the edge Booleans, the order of the values of {@link #separate}.
   *
   * @return a new array
   */
  public IntVar[] literals() {
    IntVar[] all = Arrays.copyOf(nodes, nodes.length + edges.length);
    System.arraycopy(edges, 0, all, nodes.length, edges.length);
    return all;
  }

  /**
   * The number of node Booleans; the edge Booleans follow them in {@link #literals}.
   *
   * @return the number of nodes
   */
  public int nodeCount() {
    return nodes.length;
  }

  /**
   * It returns the cuts over the copies of the variables.
   *
   * @param map the copies
   * @return the cuts of the copy
   */
  public TreeCuts copy(VarMap map) {
    IntVar[] n = new IntVar[nodes.length];
    for (int i = 0; i < n.length; i++) {
      n[i] = map.get(nodes[i]);
    }
    IntVar[] e = new IntVar[edges.length];
    for (int i = 0; i < e.length; i++) {
      e[i] = map.get(edges[i]);
    }
    return new TreeCuts(n, e, tail, head);
  }

  /**
   * It returns violated cuts, the most effective first: for nodes k in decreasing order of their
   * value, a most violated cut of the sets that contain k, skipping the nodes of the sets found
   * before.
   *
   * @param value the values of the node Booleans followed by those of the edge Booleans
   * @param limit the most cuts returned
   * @return the violated cuts
   */
  public List<Cut> separate(double[] value, int limit) {
    int n = nodes.length;
    int m = edges.length;
    // the support graph: the edges of positive value between two different nodes
    int[] support = new int[m];
    int s = 0;
    for (int e = 0; e < m; e++) {
      if (value[n + e] > EPS && tail[e] != head[e]) {
        support[s++] = e;
      }
    }
    List<Cut> cuts = new ArrayList<>();
    if (s == 0) {
      return cuts;
    }
    support = Arrays.copyOf(support, s);
    boolean[] touched = new boolean[n];
    for (int e : support) {
      touched[tail[e]] = true;
      touched[head[e]] = true;
    }
    Integer[] order = new Integer[n];
    int candidates = 0;
    for (int i = 0; i < n; i++) {
      if (touched[i] && value[i] > EPS) {
        order[candidates++] = i;
      }
    }
    Integer[] ks = Arrays.copyOf(order, candidates);
    Arrays.sort(ks, Comparator.comparingDouble((Integer i) -> -value[i]));
    // the nodes of the sets found are not tried as k again: their cuts would mostly repeat those
    // sets (st70 of surface-based-tsp reaches the optimum with 800 cuts this way, and stays 50
    // below it with 2,450 cuts when every node is tried)
    boolean[] covered = new boolean[n];
    int flows = 0;
    for (int k : ks) {
      if (cuts.size() >= limit || flows >= MAX_FLOWS) {
        break;
      }
      if (covered[k]) {
        continue;
      }
      flows++;
      boolean[] inS = closure(k, support, value);
      if (inS == null) {
        continue;
      }
      Cut cut = cut(k, inS, value);
      if (cut != null) {
        cuts.add(cut);
        for (int i = 0; i < n; i++) {
          covered[i] |= inS[i];
        }
      }
    }
    cuts.sort(Comparator.comparingDouble((Cut c) -> -c.efficacy));
    return cuts;
  }

  // the set S of a maximum weight closure that contains k: each support edge is worth its value
  // and needs both its nodes, each node other than k costs its value; null when only {k}
  private boolean[] closure(int k, int[] support, double[] value) {
    int n = nodes.length;
    int s = support.length;
    // network: 0 source, 1 sink, 2..2+s edges, 2+s.. nodes
    Flow g = new Flow(2 + s + n);
    for (int a = 0; a < s; a++) {
      int e = support[a];
      g.arc(0, 2 + a, value[n + e]);
      g.arc(2 + a, 2 + s + tail[e], Double.POSITIVE_INFINITY);
      g.arc(2 + a, 2 + s + head[e], Double.POSITIVE_INFINITY);
    }
    for (int i = 0; i < n; i++) {
      if (i == k) {
        g.arc(0, 2 + s + i, Double.POSITIVE_INFINITY);
      } else if (value[i] > EPS) {
        g.arc(2 + s + i, 1, value[i]);
      }
    }
    g.maxFlow(0, 1);
    boolean[] reach = g.sourceSide(0);
    boolean[] inS = new boolean[n];
    int size = 0;
    for (int i = 0; i < n; i++) {
      if (reach[2 + s + i]) {
        inS[i] = true;
        size++;
      }
    }
    return size < 2 ? null : inS;
  }

  // the cut of S and k, or null when it is not violated enough
  private Cut cut(int k, boolean[] inS, double[] value) {
    int n = nodes.length;
    double lhs = 0;
    List<Integer> inside = new ArrayList<>();
    for (int e = 0; e < edges.length; e++) {
      if (tail[e] != head[e] && inS[tail[e]] && inS[head[e]]) {
        inside.add(e);
        lhs += value[n + e];
      }
    }
    List<Integer> rest = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      if (inS[i] && i != k) {
        rest.add(i);
        lhs -= value[i];
      }
    }
    if (lhs <= MIN_VIOLATION || inside.isEmpty()) {
      return null;
    }
    double norm = Math.sqrt((double) inside.size() + rest.size());
    return new Cut(
        rest.stream().mapToInt(Integer::intValue).toArray(),
        inside.stream().mapToInt(Integer::intValue).toArray(),
        lhs / norm);
  }

  // a small maximum flow (Dinic) over double capacities
  private static final class Flow {
    private final int size;
    private int[] to = new int[16];
    private int[] next = new int[16];
    private double[] cap = new double[16];
    private final int[] first;
    private int arcs;
    private final int[] level;
    private final int[] iter;

    Flow(int size) {
      this.size = size;
      first = new int[size];
      Arrays.fill(first, -1);
      level = new int[size];
      iter = new int[size];
    }

    void arc(int u, int v, double c) {
      add(u, v, c);
      add(v, u, 0);
    }

    private void add(int u, int v, double c) {
      if (arcs == to.length) {
        to = Arrays.copyOf(to, arcs * 2);
        next = Arrays.copyOf(next, arcs * 2);
        cap = Arrays.copyOf(cap, arcs * 2);
      }
      to[arcs] = v;
      cap[arcs] = c;
      next[arcs] = first[u];
      first[u] = arcs++;
    }

    void maxFlow(int s, int t) {
      int[] queue = new int[size];
      while (true) {
        Arrays.fill(level, -1);
        level[s] = 0;
        int qh = 0;
        int qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
          int u = queue[qh++];
          for (int a = first[u]; a >= 0; a = next[a]) {
            if (cap[a] > EPS && level[to[a]] < 0) {
              level[to[a]] = level[u] + 1;
              queue[qt++] = to[a];
            }
          }
        }
        if (level[t] < 0) {
          return;
        }
        System.arraycopy(first, 0, iter, 0, size);
        while (push(s, t, Double.POSITIVE_INFINITY) > EPS) {
          // augment along blocking flow paths
        }
      }
    }

    private double push(int u, int t, double f) {
      if (u == t) {
        return f;
      }
      for (; iter[u] >= 0; iter[u] = next[iter[u]]) {
        int a = iter[u];
        int v = to[a];
        if (cap[a] > EPS && level[v] == level[u] + 1) {
          double d = push(v, t, Math.min(f, cap[a]));
          if (d > EPS) {
            cap[a] -= d;
            cap[a ^ 1] += d;
            return d;
          }
        }
      }
      return 0;
    }

    boolean[] sourceSide(int s) {
      boolean[] seen = new boolean[size];
      int[] stack = new int[size];
      int top = 0;
      stack[top++] = s;
      seen[s] = true;
      while (top > 0) {
        int u = stack[--top];
        for (int a = first[u]; a >= 0; a = next[a]) {
          if (cap[a] > EPS && !seen[to[a]]) {
            seen[to[a]] = true;
            stack[top++] = to[a];
          }
        }
      }
      return seen;
    }
  }
}
