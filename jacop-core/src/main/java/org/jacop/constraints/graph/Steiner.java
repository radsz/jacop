/*
 * Steiner.java
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
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Steiner tree (MiniZinc's {@code steiner} and {@code dsteiner}): the selected nodes and edges form
 * a tree and {@code cost} is the sum of the weights of the selected edges. In a directed graph the
 * tree is rooted at {@code root} with every edge pointing away from it. The terminals are the nodes
 * whose Booleans are fixed to 1.
 *
 * <p>It is decomposed into {@link Tree}, the cost sum and, when no weight is negative, the dual
 * ascent bound {@link SteinerBound} with node and edge filtering.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Steiner extends DecomposedConstraint<Constraint> {

  final int[] from;
  final int[] to;
  final int[] weights;
  final IntVar root;
  final IntVar[] ns;
  final IntVar[] es;
  final IntVar cost;
  final int base;
  final boolean directed;

  private final List<Var> auxiliary = new ArrayList<>();

  /**
   * It constructs a Steiner tree constraint.
   *
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param weights the weight of each edge.
   * @param root the root node; null is allowed in an undirected graph.
   * @param ns the Boolean of each node; ns[i] is node base + i.
   * @param es the Boolean of each edge.
   * @param cost the sum of the weights of the selected edges.
   * @param base the number of the first node.
   * @param directed true for a directed graph.
   */
  public Steiner(
      int[] from,
      int[] to,
      int[] weights,
      IntVar root,
      IntVar[] ns,
      IntVar[] es,
      IntVar cost,
      int base,
      boolean directed) {
    if (directed && root == null) {
      throw new IllegalArgumentException("Steiner: a directed tree needs a root");
    }
    checkInputForNullness(new String[] {"cost"}, new Object[] {cost});
    this.from = from;
    this.to = to;
    this.weights = weights;
    this.root = root;
    this.ns = ns;
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
    Tree tree = new Tree(from, to, root, ns, es, base, directed);
    List<Constraint> result = new ArrayList<>(tree.decompose(store));
    auxiliary.addAll(tree.auxiliaryVariables());
    result.add(new LinearInt(es, weights, "==", cost));
    if (Arrays.stream(weights).allMatch(w -> w >= 0)) {
      result.add(new SteinerBound(from, to, weights, root, ns, es, cost, base, directed));
    }
    return result;
  }

  @Override
  public List<Var> auxiliaryVariables() {
    return Collections.unmodifiableList(auxiliary);
  }
}
