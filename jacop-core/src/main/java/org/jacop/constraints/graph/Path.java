/*
 * Path.java
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
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Path constraint on a subgraph of a given graph (MiniZinc's {@code path} and {@code dpath}). The
 * selected nodes and edges form a simple path from s to t (a single node when s = t); in a directed
 * graph the edges are followed in their direction. Nodes are numbered from {@code base}, as in
 * {@link Reachable}.
 *
 * <p>It is decomposed into {@link Reachable} from s with forest pruning (and, in a directed graph,
 * {@link Reachable} from t in the reversed graph), the count {@code sum(es) = sum(ns) - 1} and the
 * degrees: in a directed graph one incoming selected edge for each selected node other than s and
 * one outgoing for each selected node other than t; in an undirected graph two selected edges at
 * each selected node, one less at s and one less at t.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Path extends DecomposedConstraint<Constraint> {

  final int[] from;
  final int[] to;
  final IntVar s;
  final IntVar t;
  final IntVar[] ns;
  final IntVar[] es;
  final int base;
  final boolean directed;

  private final List<Var> auxiliary = new ArrayList<>();

  /**
   * It constructs a path constraint.
   *
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param s the first node of the path.
   * @param t the last node of the path.
   * @param ns the Boolean of each node; ns[i] is node base + i.
   * @param es the Boolean of each edge.
   * @param base the number of the first node.
   * @param directed true for a directed graph.
   */
  public Path(
      int[] from,
      int[] to,
      IntVar s,
      IntVar t,
      IntVar[] ns,
      IntVar[] es,
      int base,
      boolean directed) {
    checkInputForNullness(new String[] {"s", "t"}, new Object[] {s, t});
    this.from = from;
    this.to = to;
    this.s = s;
    this.t = t;
    this.ns = ns;
    this.es = es;
    this.base = base;
    this.directed = directed;
  }

  /**
   * It constructs a path constraint on nodes numbered from 0.
   *
   * @param from the tail of each edge.
   * @param to the head of each edge.
   * @param s the first node of the path.
   * @param t the last node of the path.
   * @param ns the Boolean of each node.
   * @param es the Boolean of each edge.
   * @param directed true for a directed graph.
   */
  public Path(
      int[] from, int[] to, IntVar s, IntVar t, IntVar[] ns, IntVar[] es, boolean directed) {
    this(from, to, s, t, ns, es, 0, directed);
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
    result.add(new Reachable(from, to, s, ns, es, base, directed, true));
    if (directed) {
      // every selected node also reaches t: reachability from t in the reversed graph
      result.add(new Reachable(to, from, t, ns, es, base, true, false));
    }
    result.add(Tree.edgeCount(ns, es));
    int n = ns.length;
    IntVar[] isS = Tree.nodeIndicators(store, s, n, base, result, auxiliary);
    IntVar[] isT = Tree.nodeIndicators(store, t, n, base, result, auxiliary);
    if (directed) {
      int[][] entering = Tree.edgesByNode(from, to, n, base, true, false);
      int[][] leaving = Tree.edgesByNode(from, to, n, base, false, true);
      for (int v = 0; v < n; v++) {
        result.add(Tree.degree(entering[v], es, isS[v], null, ns[v], 1));
        result.add(Tree.degree(leaving[v], es, isT[v], null, ns[v], 1));
      }
    } else {
      int[][] touching = Tree.edgesByNode(from, to, n, base, true, true);
      for (int v = 0; v < n; v++) {
        result.add(Tree.degree(touching[v], es, isS[v], isT[v], ns[v], 2));
      }
    }
    return result;
  }

  @Override
  public List<Var> auxiliaryVariables() {
    return Collections.unmodifiableList(auxiliary);
  }
}
