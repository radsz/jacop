/*
 * Tree.java
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.LinearInt;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Tree constraint on a subgraph of a given graph (MiniZinc's {@code tree} and {@code dtree}). The
 * selected edges form a tree that spans the selected nodes and contains the root; in a directed
 * graph every edge points away from the root. Nodes are numbered from {@code base}, as in {@link
 * Reachable}.
 *
 * <p>It is decomposed into {@link Reachable} with forest pruning, the count {@code sum(es) =
 * sum(ns) - 1} and, in a directed graph, one incoming selected edge for each selected node other
 * than the root.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Tree extends DecomposedConstraint<Constraint> {

  final int[] from;
  final int[] to;
  final IntVar root;
  final IntVar[] ns;
  final IntVar[] es;
  final int base;
  final boolean directed;

  private final List<Var> auxiliary = new ArrayList<>();

  /**
   * It constructs a tree constraint.
   *
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param root the root node number; null is allowed in an undirected graph, where any selected
   *     node can be the root.
   * @param ns the Boolean of each node; ns[i] is node base + i.
   * @param es the Boolean of each edge.
   * @param base the number of the first node.
   * @param directed true for a directed graph, whose edges point away from the root.
   */
  public Tree(
      int[] from, int[] to, IntVar root, IntVar[] ns, IntVar[] es, int base, boolean directed) {
    if (directed && root == null) {
      throw new IllegalArgumentException("Tree: a directed tree needs a root");
    }
    this.from = from;
    this.to = to;
    this.root = root;
    this.ns = ns;
    this.es = es;
    this.base = base;
    this.directed = directed;
  }

  /**
   * It constructs a tree constraint on nodes numbered from 0.
   *
   * @param from the tail of each edge.
   * @param to the head of each edge.
   * @param root the root node.
   * @param ns the Boolean of each node.
   * @param es the Boolean of each edge.
   * @param directed true for a directed graph.
   */
  public Tree(int[] from, int[] to, IntVar root, IntVar[] ns, IntVar[] es, boolean directed) {
    this(from, to, root, ns, es, 0, directed);
  }

  @Override
  public void imposeDecomposition(Store store) {
    for (Constraint c : decompose(store)) {
      store.impose(c, queueIndex);
    }
  }

  @Override
  public List<Constraint> decompose(Store store) {
    List<Constraint> result = new ArrayList<>();
    result.add(new Reachable(from, to, root, ns, es, base, directed, true));
    result.add(edgeCount(ns, es));
    if (directed) {
      IntVar[] isRoot = nodeIndicators(store, root, ns.length, base, result, auxiliary);
      int[][] entering = edgesByNode(from, to, ns.length, base, true, false);
      for (int v = 0; v < ns.length; v++) {
        result.add(degree(entering[v], es, isRoot[v], null, ns[v], 1));
      }
    }
    return result;
  }

  @Override
  public List<Var> auxiliaryVariables() {
    return Collections.unmodifiableList(auxiliary);
  }

  /** The tree count: sum(es) - sum(ns) = -1. */
  static Constraint edgeCount(IntVar[] ns, IntVar[] es) {
    IntVar[] vars = new IntVar[es.length + ns.length];
    int[] weights = new int[vars.length];
    for (int e = 0; e < es.length; e++) {
      vars[e] = es[e];
      weights[e] = 1;
    }
    for (int v = 0; v < ns.length; v++) {
      vars[es.length + v] = ns[v];
      weights[es.length + v] = -1;
    }
    return new LinearInt(vars, weights, "==", -1);
  }

  /**
   * One 0/1 variable for each node telling whether x is that node, channelled to x when x is not
   * fixed; constants otherwise.
   */
  static IntVar[] nodeIndicators(
      Store store, IntVar x, int n, int base, List<Constraint> result, List<Var> auxiliary) {
    IntVar[] b = new IntVar[n];
    if (x.singleton()) {
      for (int v = 0; v < n; v++) {
        b[v] = new IntVar(store, x.value() == base + v ? 1 : 0, x.value() == base + v ? 1 : 0);
      }
      return b;
    }
    int[] values = new int[n];
    for (int v = 0; v < n; v++) {
      values[v] = base + v;
      b[v] = new BooleanVar(store);
      auxiliary.add(b[v]);
    }
    result.add(new ChannelReif(x, b, values));
    return b;
  }

  /**
   * The edges other than self-loops by node: entering it (heads), leaving it (tails) or touching it
   * (both), as {@code result[node - base]}.
   */
  static int[][] edgesByNode(int[] from, int[] to, int n, int base, boolean heads, boolean tails) {
    int[] count = new int[n];
    for (int e = 0; e < from.length; e++) {
      if (from[e] != to[e]) {
        if (tails) {
          count[from[e] - base]++;
        }
        if (heads) {
          count[to[e] - base]++;
        }
      }
    }
    int[][] result = new int[n][];
    for (int v = 0; v < n; v++) {
      result[v] = new int[count[v]];
      count[v] = 0;
    }
    for (int e = 0; e < from.length; e++) {
      if (from[e] != to[e]) {
        if (tails) {
          result[from[e] - base][count[from[e] - base]++] = e;
        }
        if (heads) {
          result[to[e] - base][count[to[e] - base]++] = e;
        }
      }
    }
    return result;
  }

  /** The degree equation sum(es[edges]) + a + b = k * node. */
  static Constraint degree(int[] edges, IntVar[] es, IntVar a, IntVar b, IntVar node, int k) {
    int size = edges.length + 1 + (a == null ? 0 : 1) + (b == null ? 0 : 1);
    IntVar[] vars = new IntVar[size];
    int[] weights = new int[size];
    int i = 0;
    for (int e : edges) {
      vars[i] = es[e];
      weights[i++] = 1;
    }
    if (a != null) {
      vars[i] = a;
      weights[i++] = 1;
    }
    if (b != null) {
      vars[i] = b;
      weights[i++] = 1;
    }
    vars[i] = node;
    weights[i] = -k;
    return new LinearInt(vars, weights, "==", 0);
  }
}
