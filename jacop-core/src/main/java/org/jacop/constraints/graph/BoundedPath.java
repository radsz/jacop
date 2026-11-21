/*
 * BoundedPath.java
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
 * Bounded path (MiniZinc's {@code bounded_path} and {@code bounded_dpath}): the selected nodes and
 * edges form a simple path from s to t and {@code cost} is the sum of the weights of the selected
 * edges.
 *
 * <p>It is decomposed into {@link Path}, the cost sum and, for non-negative weights, a shortest
 * path bound that also removes nodes and edges that only lie on paths longer than the cost allows.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class BoundedPath extends DecomposedConstraint<Constraint> {

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

  private final List<Var> auxiliary = new ArrayList<>();

  /**
   * It constructs a bounded path constraint.
   *
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param weights the weight of each edge.
   * @param s the first node of the path.
   * @param t the last node of the path.
   * @param ns the Boolean of each node; ns[i] is node base + i.
   * @param es the Boolean of each edge.
   * @param cost the sum of the weights of the selected edges.
   * @param base the number of the first node.
   * @param directed true for a directed graph.
   */
  public BoundedPath(
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
    checkInputForNullness(new String[] {"s", "t", "cost"}, new Object[] {s, t, cost});
    this.from = from;
    this.to = to;
    this.weights = weights;
    this.s = s;
    this.t = t;
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
    Path path = new Path(from, to, s, t, ns, es, base, directed);
    List<Constraint> result = new ArrayList<>(path.decompose(store));
    auxiliary.addAll(path.auxiliaryVariables());
    result.add(new LinearInt(es, weights, "==", cost));
    result.add(new PathCostBound(from, to, weights, s, t, ns, es, cost, base, directed));
    return result;
  }

  @Override
  public List<Var> auxiliaryVariables() {
    return Collections.unmodifiableList(auxiliary);
  }
}
