/*
 * CostAlldifferent.java
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
 * CostAlldifferent constraint assures that the variables take distinct values and that cost is the
 * sum of the costs of their values: costs[i][j] is the cost of list[i] = offset + j. It is the
 * all-different constraint with a cost matrix of SICStus Prolog ({@code all_different(Xs, [cost(C,
 * M)])}), or a linear assignment problem when there are as many values as variables.
 *
 * <p>The cost is filtered by the assignment relaxation, solved incrementally by the Hungarian
 * method (see {@link CircuitCost}): the minimum assignment bounds the cost from below and removes
 * every value whose reduced cost exceeds the slack between the bound and the largest cost, and the
 * maximum assignment does the same from above (Focacci, Lodi and Milano, CP 1999). The two
 * assignments only run when the bound of the cost is tighter than the sums of the row minima and
 * maxima. The values only need to be distinct once all variables are ground; post the constraint
 * together with {@link Alldistinct} or {@link Alldiff} on the same variables for the structural
 * propagation. {@link CostGCC} is the version with counters.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CostAlldifferent extends Constraint
    implements SatisfiedPresent, Copyable<CostAlldifferent> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The variables. */
  public final IntVar[] list;

  /** The cost of each value: costs[i][j] is the cost of list[i] = offset + j. */
  public final int[][] costs;

  /** The sum of the costs of the values. */
  public final IntVar cost;

  /** The value of the first column of costs. */
  public final int offset;

  private final int n;

  private final int m;

  private final CircuitCost.Assignment minAssignment;

  private final CircuitCost.Assignment maxAssignment;

  // the sums of the smallest and of the largest cost of each row, from the last call
  private final long[] rows = new long[2];

  // the last minimum assignment
  private long assignmentBound = Long.MIN_VALUE;

  /**
   * It constructs an all-different constraint with a cost, whose values are numbered from 1.
   *
   * @param list variables which must take distinct values.
   * @param costs costs[i][j] is the cost of list[i] = j + 1; all rows have the same length.
   * @param cost the sum of the costs of the values of the variables.
   */
  public CostAlldifferent(IntVar[] list, int[][] costs, IntVar cost) {
    this(list, costs, cost, 1);
  }

  /**
   * It constructs an all-different constraint with a cost, whose values are numbered from the given
   * offset. The variables take values in offset..offset + m - 1, where m is the length of the rows
   * of costs, at least the number of variables.
   *
   * @param list variables which must take distinct values.
   * @param costs costs[i][j] is the cost of list[i] = offset + j; all rows have the same length.
   * @param cost the sum of the costs of the values of the variables.
   * @param offset the value of the first column of costs.
   */
  public CostAlldifferent(IntVar[] list, int[][] costs, IntVar cost, int offset) {

    checkInputForNullness(new String[] {"list", "costs", "cost"}, list, costs, new Object[] {cost});
    checkInputForDuplication("list", list);
    if (costs.length != list.length) {
      throw new IllegalArgumentException(
          "CostAlldifferent needs a cost row for each of the " + list.length + " variables");
    }
    int columns = costs.length == 0 ? 0 : costs[0] == null ? -1 : costs[0].length;
    for (int[] row : costs) {
      if (row == null || row.length != columns) {
        throw new IllegalArgumentException("CostAlldifferent needs cost rows of the same length");
      }
    }
    if (columns < list.length) {
      throw new IllegalArgumentException(
          "CostAlldifferent needs at least as many values as the " + list.length + " variables");
    }
    if ((long) offset < IntDomain.MIN_INT || (long) offset + columns - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException(
          "CostAlldifferent has values "
              + offset
              + ".."
              + ((long) offset + columns - 1)
              + " out of range");
    }
    for (IntVar v : list) {
      if (v == cost) {
        throw new IllegalArgumentException("CostAlldifferent cost variable is also in list");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.n = list.length;
    this.m = columns;
    this.costs = new int[n][];
    for (int i = 0; i < n; i++) {
      this.costs[i] = Arrays.copyOf(costs[i], m);
    }
    this.cost = cost;
    this.offset = offset;
    this.queueIndex = 2;

    minAssignment = new CircuitCost.Assignment(n, m, this.costs, false);
    maxAssignment = new CircuitCost.Assignment(n, m, this.costs, true);

    setScope(list, new IntVar[] {cost});
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
    return v == cost ? IntDomain.BOUND : IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {

    if (n == 0) {
      cost.domain.in(store.level, cost, 0, 0);
      return;
    }

    for (IntVar x : list) {
      x.domain.in(store.level, x, offset, offset + m - 1);
    }

    // Every assignment costs at most the sum of the row maxima, so the minimum assignment can only
    // prune when the cost has a smaller upper bound, and the same for the maximum assignment.
    do {
      store.propagationHasOccurred = false;
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

    if (cost.singleton() && allGround() && !distinct()) {
      throw Store.failException;
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

  // the ground variables take distinct values
  private boolean distinct() {
    boolean[] taken = new boolean[m];
    for (IntVar x : list) {
      int j = x.value() - offset;
      if (taken[j]) {
        return false;
      }
      taken[j] = true;
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton()) {
      return false;
    }
    long sum = 0;
    for (int i = 0; i < n; i++) {
      if (!list[i].singleton()) {
        return false;
      }
      int j = list[i].value() - offset;
      if (j < 0 || j >= m) {
        return false;
      }
      sum += costs[i][j];
    }
    return sum == cost.value() && distinct();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : CostAlldifferent([");
    appendArrayToString(result, list);
    result.append("], ");
    CostBounds.appendCosts(result, costs);
    result.append(", ").append(cost);
    if (offset != 1) {
      result.append(", ").append(offset);
    }
    result.append(')');
    return result.toString();
  }

  @Override
  public CostAlldifferent copy(VarMap map) {
    return new CostAlldifferent(map.get(list), costs, map.get(cost), offset);
  }
}
