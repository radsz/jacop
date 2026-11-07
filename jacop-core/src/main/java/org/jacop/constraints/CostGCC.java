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

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * CostGCC constraint, the global cardinality constraint with a cost matrix (SICStus Prolog {@code
 * global_cardinality(Xs, Vals, [cost(C, M)])}, Régin, CP 1999): counters[j] is the number of
 * variables of list equal to offset + j, and cost is the sum of the costs of the values of the
 * variables, costs[i][j] being the cost of list[i] = offset + j. The variables take values in
 * offset..offset + m - 1, where m is the number of counters.
 *
 * <p>The cost is filtered by the assignment relaxation of {@link CostAlldifferent} where value j
 * has as many columns as the upper bound of its counter: the minimum assignment, by the incremental
 * Hungarian method of {@link CircuitCost}, bounds the cost from below and removes the values whose
 * reduced cost exceeds the slack to the largest cost, and the maximum assignment does the same from
 * above. The lower bounds of the counters are left out of the relaxation, so it is a minimum cost
 * flow with capacities only. The counts are only checked once all variables are ground; post the
 * constraint together with {@link GCC} or {@link GlobalCardinality} for the propagation of the
 * counters.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@SuppressWarnings("checkstyle:AbbreviationAsWordInName") // GCC is standard terminology
public class CostGCC extends Constraint implements SatisfiedPresent, Copyable<CostGCC> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

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

  private final int n;

  private final int m;

  // the columns of each value in the assignments
  private final int[] copies;

  private final CircuitCost.Assignment minAssignment;

  private final CircuitCost.Assignment maxAssignment;

  // the sums of the smallest and of the largest cost of each row, from the last call
  private final long[] rows = new long[2];

  // the last minimum assignment
  private long assignmentBound = Long.MIN_VALUE;

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

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.counters = Arrays.copyOf(counters, m);
    this.n = list.length;
    this.m = m;
    this.costs = new int[n][];
    for (int i = 0; i < n; i++) {
      this.costs[i] = Arrays.copyOf(costs[i], m);
    }
    this.cost = cost;
    this.offset = offset;
    this.queueIndex = 2;

    copies = new int[m];
    for (int j = 0; j < m; j++) {
      copies[j] = Math.max(0, Math.min(counters[j].max(), n));
    }
    minAssignment = new CircuitCost.Assignment(n, m, this.costs, false, copies);
    maxAssignment = new CircuitCost.Assignment(n, m, this.costs, true, copies);

    setScope(list, counters, new IntVar[] {cost});
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    Integer event = getConsistencyPruningEventFromMap(v);
    if (event != null) {
      return event;
    }
    for (IntVar x : list) {
      if (x == v) {
        return IntDomain.ANY;
      }
    }
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {

    for (IntVar x : list) {
      x.domain.in(store.level, x, offset, offset + m - 1);
    }

    if (n > 0) {
      do {
        store.propagationHasOccurred = false;
        for (int j = 0; j < m; j++) {
          int open = Math.max(0, Math.min(counters[j].max(), copies[j]));
          minAssignment.setOpen(j, open);
          maxAssignment.setOpen(j, open);
        }
        CostBounds.rowSums(list, costs, offset, rows);
        CostBounds.setMax(store, cost, rows[1]);
        CostBounds.setMin(store, cost, rows[0]);
        assignmentBound =
            CostBounds.assignments(
                store,
                list,
                offset,
                cost,
                minAssignment,
                maxAssignment,
                rows,
                assignmentBound,
                Long.MIN_VALUE);
      } while (store.propagationHasOccurred);
    } else {
      cost.domain.in(store.level, cost, 0, 0);
    }

    if (allGround()) {
      int[] count = counts();
      for (int j = 0; j < m; j++) {
        counters[j].domain.in(store.level, counters[j], count[j], count[j]);
      }
    }
  }

  private boolean allGround() {
    for (IntVar x : list) {
      if (!x.singleton()) {
        return false;
      }
    }
    return true;
  }

  // the number of ground variables equal to each value
  private int[] counts() {
    int[] count = new int[m];
    for (IntVar x : list) {
      count[x.value() - offset]++;
    }
    return count;
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton() || !allGround()) {
      return false;
    }
    long sum = 0;
    for (int i = 0; i < n; i++) {
      int j = list[i].value() - offset;
      if (j < 0 || j >= m) {
        return false;
      }
      sum += costs[i][j];
    }
    int[] count = counts();
    for (int j = 0; j < m; j++) {
      if (!counters[j].singleton(count[j])) {
        return false;
      }
    }
    return sum == cost.value();
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : CostGCC([");
    appendArrayToString(result, list);
    result.append("], ");
    CostBounds.appendCosts(result, costs);
    result.append(", [");
    appendArrayToString(result, counters);
    result.append("], ").append(cost);
    if (offset != 1) {
      result.append(", ").append(offset);
    }
    result.append(')');
    return result.toString();
  }

  @Override
  public CostGCC copy(VarMap map) {
    return new CostGCC(map.get(list), costs, map.get(counters), map.get(cost), offset);
  }
}
