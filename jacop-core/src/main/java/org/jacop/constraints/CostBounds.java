/*
 * CostBounds.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Bounds shared by the constraints on a cost that is the sum of the arc costs of a successor array:
 * CircuitCost, SubcircuitCost and WeightedSubcircuits.
 */
final class CostBounds {

  private CostBounds() {}

  /**
   * Computes the sums of the smallest and of the largest arc cost of each row over the current
   * domains, into rows[0] and rows[1].
   */
  static void rowSums(IntVar[] list, int[][] costs, int offset, long[] rows) {
    long sumMin = 0;
    long sumMax = 0;
    for (int i = 0; i < list.length; i++) {
      IntVar x = list[i];
      int[] row = costs[i];
      int max = Integer.MIN_VALUE;
      int min = Integer.MAX_VALUE;
      int last = x.max();
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int c = row[val - offset];
        if (c > max) {
          max = c;
        }
        if (c < min) {
          min = c;
        }
        if (val >= last) {
          break;
        }
      }
      sumMax += max;
      sumMin += min;
    }
    rows[0] = sumMin;
    rows[1] = sumMax;
  }

  /**
   * Runs the minimum assignment when the cost has an upper bound below the row sums, and the
   * maximum assignment when its lower bound is above the row sums and above the lower bounds
   * already known, the assignment bound included.
   *
   * @return the minimum assignment bound, or assignmentBound when it did not run.
   */
  static long assignments(
      Store store,
      IntVar[] list,
      int offset,
      IntVar cost,
      CircuitCost.Assignment minAssignment,
      CircuitCost.Assignment maxAssignment,
      long[] rows,
      long assignmentBound,
      long otherLowerBound) {
    long bound = assignmentBound;
    if (cost.max() < rows[1]) {
      bound = minAssignment.solve(list, offset);
      setMin(store, cost, bound);
      minAssignment.prune(store, list, offset, cost.max());
    }
    if (cost.min() > rows[0] && cost.min() > Math.max(bound, otherLowerBound)) {
      long negatedBound = maxAssignment.solve(list, offset);
      setMax(store, cost, -negatedBound);
      maxAssignment.prune(store, list, offset, -(long) cost.min());
    }
    return bound;
  }

  static void setMin(Store store, IntVar v, long min) {
    if (min > v.max()) {
      throw Store.failException;
    }
    if (min > v.min()) {
      v.domain.inMin(store.level, v, (int) min);
    }
  }

  static void setMax(Store store, IntVar v, long max) {
    if (max < v.min()) {
      throw Store.failException;
    }
    if (max < v.max()) {
      v.domain.inMax(store.level, v, (int) max);
    }
  }

  /** Appends the cost matrix row by row. */
  static void appendCosts(StringBuilder result, int[][] costs) {
    result.append('[');
    for (int i = 0; i < costs.length; i++) {
      result.append(Arrays.toString(costs[i]));
      if (i < costs.length - 1) {
        result.append(", ");
      }
    }
    result.append(']');
  }
}
