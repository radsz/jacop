/*
 * CostGCC.java
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
import java.util.List;
import org.jacop.constraints.netflow.DomainStructure;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * CostGCC constraint, the global cardinality constraint with a cost matrix (Régin, CP 1999; SICStus
 * Prolog {@code global_cardinality(Xs, Vals, [cost(C, M)])}): counters[j] is the number of
 * variables of list equal to offset + j, and cost is the sum of the costs of the values of the
 * variables, costs[i][j] being the cost of list[i] = offset + j. The variables take values in
 * offset..offset + m - 1, where m is the number of counters.
 *
 * <p>It is decomposed into a {@link org.jacop.constraints.netflow.NetworkFlow}: one unit of flow
 * from each variable to its value, at the cost of the value, and the flow of each value to the sink
 * is its counter. The minimum cost flow bounds the cost from below, and the reduced costs of the
 * arcs remove the values and narrow the counters that cannot be part of a flow within the upper
 * bound of the cost. Post it together with {@link GCC} for the propagation of the counters without
 * costs.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@SuppressWarnings("checkstyle:AbbreviationAsWordInName") // GCC is standard terminology
public class CostGCC extends DecomposedConstraint<Constraint> {

  /** The variables. */
  public final IntVar[] list;

  /** The cost of each value: costs[i][j] is the cost of list[i] = offset + j. */
  public final int[][] costs;

  /** The number of variables equal to each value: counters[j] counts offset + j. */
  public final IntVar[] counters;

  /** The sum of the costs of the values. */
  public final IntVar cost;

  /** The value of the first counter and the first column of costs. */
  public final int offset;

  private List<Constraint> decomposition;

  /**
   * It constructs a global cardinality constraint with a cost, whose values are numbered from the
   * given offset.
   *
   * @param list the variables.
   * @param costs costs[i][j] is the cost of list[i] = offset + j; each row has one cost per
   *     counter.
   * @param counters counters[j] is the number of variables equal to offset + j.
   * @param cost the sum of the costs of the values of the variables.
   * @param offset the value counted by counters[0].
   */
  public CostGCC(IntVar[] list, int[][] costs, IntVar[] counters, IntVar cost, int offset) {

    checkInputForNullness(
        new String[] {"list", "costs", "counters", "cost"},
        list,
        costs,
        counters,
        new Object[] {cost});
    checkInputForDuplication("list", list);
    int m = counters.length;
    if (costs.length != list.length) {
      throw new IllegalArgumentException(
          "CostGCC needs a cost row for each of the " + list.length + " variables");
    }
    for (int[] row : costs) {
      if (row == null || row.length != m) {
        throw new IllegalArgumentException("CostGCC needs " + m + " costs in each row of costs");
      }
    }
    if ((long) offset < IntDomain.MIN_INT || (long) offset + m - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException(
          "CostGCC has values " + offset + ".." + ((long) offset + m - 1) + " out of range");
    }
    for (IntVar v : list) {
      for (IntVar c : counters) {
        if (v == c) {
          throw new IllegalArgumentException("CostGCC counter " + c + " is also in list");
        }
      }
      if (v == cost) {
        throw new IllegalArgumentException("CostGCC cost variable is also in list");
      }
    }
    for (IntVar c : counters) {
      if (c == cost) {
        throw new IllegalArgumentException("CostGCC cost variable is also a counter");
      }
    }

    this.list = Arrays.copyOf(list, list.length);
    this.counters = Arrays.copyOf(counters, m);
    this.costs = new int[list.length][];
    for (int i = 0; i < list.length; i++) {
      this.costs[i] = Arrays.copyOf(costs[i], m);
    }
    this.cost = cost;
    this.offset = offset;
  }

  @Override
  public List<Constraint> decompose(Store store) {
    if (decomposition == null) {
      decomposition = new ArrayList<>();
      int n = list.length;
      int m = counters.length;
      for (IntVar x : list) {
        decomposition.add(new In(x, new IntervalDomain(offset, offset + m - 1)));
      }
      NetworkBuilder net = new NetworkBuilder(cost);
      Node[] variables = new Node[n];
      for (int i = 0; i < n; i++) {
        variables[i] = net.addNode(list[i].id(), 1);
      }
      Node[] values = new Node[m];
      for (int j = 0; j < m; j++) {
        values[j] = net.addNode(String.valueOf(offset + j), 0);
      }
      Node sink = net.addNode("sink", -n);
      for (int i = 0; i < n; i++) {
        IntVar x = list[i];
        List<Arc> arcs = new ArrayList<>();
        List<IntDomain> domains = new ArrayList<>();
        for (int j = 0; j < m; j++) {
          if (x.domain.contains(offset + j)) {
            arcs.add(net.addArc(variables[i], values[j], costs[i][j], 0, 1));
            domains.add(new IntervalDomain(offset + j, offset + j));
          }
        }
        net.handlerList.add(
            new DomainStructure(x, domains.toArray(new IntDomain[0]), arcs.toArray(new Arc[0])));
      }
      for (int j = 0; j < m; j++) {
        net.addArc(values[j], sink, 0, counters[j]);
      }
      decomposition.add(net.build());
    }
    return decomposition;
  }

  @Override
  public void imposeDecomposition(Store store) {
    for (Constraint c : decompose(store)) {
      store.impose(c);
    }
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder("CostGCC([");
    for (int i = 0; i < list.length; i++) {
      result.append(list[i]);
      if (i < list.length - 1) {
        result.append(", ");
      }
    }
    result.append("], ");
    CostBounds.appendCosts(result, costs);
    result.append(", ").append(Arrays.toString(counters)).append(", ").append(cost);
    result.append(", ").append(offset).append(')');
    return result.toString();
  }
}
