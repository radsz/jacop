/*
 * WeightedSpanningTree.java
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
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Weighted spanning tree (MiniZinc's {@code weighted_spanning_tree}, {@code wst} and {@code dwst}):
 * the selected edges form a tree that spans every node of the graph and {@code cost} is the sum of
 * their weights. In a directed graph the tree is rooted at {@code root} with every edge pointing
 * away from it.
 *
 * <p>It is decomposed into {@link Tree} on all nodes, the cost sum and, for an undirected graph,
 * {@link SpanningTreeBound} (minimum spanning tree bound and edge filtering).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class WeightedSpanningTree extends DecomposedConstraint<Constraint> {

  final int n;
  final int[] from;
  final int[] to;
  final int[] weights;
  final IntVar root;
  final IntVar[] es;
  final IntVar cost;
  final int base;
  final boolean directed;

  private final List<Var> auxiliary = new ArrayList<>();

  /**
   * It constructs a weighted spanning tree constraint.
   *
   * @param n the number of nodes, numbered from base.
   * @param from the tail of each edge.
   * @param to the head of each edge.
   * @param weights the weight of each edge.
   * @param root the root of a directed tree; null (or any node) for an undirected one.
   * @param es the Boolean of each edge.
   * @param cost the sum of the weights of the selected edges.
   * @param base the number of the first node.
   * @param directed true for a directed graph.
   */
  public WeightedSpanningTree(
      int n,
      int[] from,
      int[] to,
      int[] weights,
      IntVar root,
      IntVar[] es,
      IntVar cost,
      int base,
      boolean directed) {
    if (directed && root == null) {
      throw new IllegalArgumentException("WeightedSpanningTree: a directed tree needs a root");
    }
    checkInputForNullness(new String[] {"cost"}, new Object[] {cost});
    this.n = n;
    this.from = from;
    this.to = to;
    this.weights = weights;
    this.root = root;
    this.es = es;
    this.cost = cost;
    this.base = base;
    this.directed = directed;
  }

  @Override
  public void imposeDecomposition(Store store) {
    for (Constraint c : decompose(store)) {
      store.impose(c, queueIndex);
    }
  }

  @Override
  public List<Constraint> decompose(Store store) {
    IntVar[] ns = new IntVar[n];
    for (int v = 0; v < n; v++) {
      ns[v] = new IntVar(store, 1, 1);
    }
    Tree tree = new Tree(from, to, root, ns, es, base, directed);
    List<Constraint> result = new ArrayList<>(tree.decompose(store));
    auxiliary.addAll(tree.auxiliaryVariables());
    result.add(new LinearInt(es, weights, "==", cost));
    if (!directed) {
      result.add(new SpanningTreeBound(n, from, to, weights, es, cost, base));
    }
    return result;
  }

  @Override
  public List<Var> auxiliaryVariables() {
    return Collections.unmodifiableList(auxiliary);
  }
}
