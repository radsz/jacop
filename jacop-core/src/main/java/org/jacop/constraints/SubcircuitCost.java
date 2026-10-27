/*
 * SubcircuitCost.java
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * SubcircuitCost constraint assures that the variables build a subcircuit and that cost is the sum
 * of costs[i][x[i]] over all variables. Value of every variable x[i] points to the next variable in
 * the subcircuit, and a variable that is not in the subcircuit points to itself, as in {@link
 * Subcircuit}. The diagonal costs[i][i] is the cost of leaving variable i out of the subcircuit,
 * for example the penalty of a prize-collecting tour, and is 0 when leaving a node out costs
 * nothing. Variables are numbered from 1 by default, or from the given offset.
 *
 * <p>This is the weighted subcircuit with one tour of Vismara and Briot (A Circuit Constraint for
 * Multiple Tours Problems, CP 2018). The nodes are required (x[i] != i), optional or left out (x[i]
 * = i). The constraint filters the arcs and the cost with two relaxations:
 *
 * <ul>
 *   <li>the assignment problem over all nodes with the self-loops, solved incrementally by the
 *       Hungarian method as in {@link CircuitCost}. A subcircuit is an assignment whose self-loops
 *       are the nodes left out, so the minimum assignment bounds the cost and every arc whose
 *       reduced cost exceeds the slack is removed. Removing a self-loop makes a node required;
 *   <li>the Steiner cycle bound: the circuit passes through all required nodes, and the part of it
 *       from one required node to the next goes through optional nodes only. The shortest such
 *       paths give a graph on the required nodes (the extended graph G* of the paper), and the
 *       assignment problem on it, without self-loops, bounds the cost. An optional node is charged
 *       its cheapest arc, self-loop included, and the arcs leaving it the excess over that charge.
 *       Unlike the first bound it does not let a required node close a cycle through optional nodes
 *       only. Every arc is filtered against it: the cost with the arc forced is bounded by the
 *       duals of the assignment plus the shortest paths from the required nodes to the arc and from
 *       the arc back.
 * </ul>
 *
 * <p>Both relaxations run only when the cost has an upper bound tighter than the sum of the largest
 * arc cost of each variable, typically once branch and bound has a first solution. The structure of
 * the subcircuit is only checked once all variables are ground; post the constraint together with
 * {@link Subcircuit} on the same variables for the structural propagation.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class SubcircuitCost extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The successor variables. */
  public final IntVar[] list;

  /** The cost of each arc: costs[i][j] is the cost of list[i] = offset + j. */
  public final int[][] costs;

  /** The cost of the subcircuit together with the costs of the nodes left out. */
  public final IntVar cost;

  /** The value that points to list[0]. */
  public final int offset;

  private final int n;

  private boolean useAssignment = true;

  private boolean useSteiner = true;

  private final CircuitCost.Assignment minAssignment;

  private final CircuitCost.Assignment maxAssignment;

  private SteinerCycleBound steiner;

  // the sums of the largest and of the smallest arc cost of each row, from the last call
  private long rowsUpperBound;

  private long rowsLowerBound;

  // the last lower bounds from the two relaxations
  private long assignmentBound = Long.MIN_VALUE;

  private long steinerBound = Long.MIN_VALUE;

  /**
   * It constructs a subcircuit constraint with a cost, whose variables are numbered from 1.
   *
   * @param list variables which must form a subcircuit.
   * @param costs costs[i][j] is the cost of list[i] pointing to list[j]; costs[i][i] is the cost of
   *     leaving list[i] out of the subcircuit.
   * @param cost the sum of costs[i][list[i] - 1] over all variables.
   */
  public SubcircuitCost(IntVar[] list, int[][] costs, IntVar cost) {
    this(list, costs, cost, 1);
  }

  /**
   * It constructs a subcircuit constraint with a cost, whose variables are numbered from the given
   * offset.
   *
   * @param list variables which must form a subcircuit.
   * @param costs costs[i][j] is the cost of list[i] = offset + j; costs[i][i] is the cost of
   *     leaving list[i] out of the subcircuit.
   * @param cost the sum of costs[i][list[i] - offset] over all variables.
   * @param offset the value that points to list[0]; list[i] is pointed to by offset + i.
   */
  public SubcircuitCost(IntVar[] list, int[][] costs, IntVar cost, int offset) {

    checkInputForNullness(new String[] {"list", "costs", "cost"}, list, costs, new Object[] {cost});
    checkInputForDuplication("list", list);
    if ((long) offset < IntDomain.MIN_INT || (long) offset + list.length - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException(
          "SubcircuitCost has values "
              + offset
              + ".."
              + ((long) offset + list.length - 1)
              + " out of range");
    }
    if (costs.length != list.length) {
      throw new IllegalArgumentException(
          "SubcircuitCost needs a cost row for each of the " + list.length + " variables");
    }
    for (int[] row : costs) {
      if (row == null || row.length != list.length) {
        throw new IllegalArgumentException(
            "SubcircuitCost needs " + list.length + " costs in each row of costs");
      }
    }
    for (IntVar v : list) {
      if (v == cost) {
        throw new IllegalArgumentException("SubcircuitCost cost variable is also in list");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.n = list.length;
    this.costs = new int[n][];
    for (int i = 0; i < n; i++) {
      this.costs[i] = Arrays.copyOf(costs[i], n);
    }
    this.cost = cost;
    this.offset = offset;
    this.queueIndex = 2;

    minAssignment = new CircuitCost.Assignment(n, this.costs, false);
    maxAssignment = new CircuitCost.Assignment(n, this.costs, true);

    setScope(list, new IntVar[] {cost});
  }

  /**
   * It selects the relaxations used for filtering.
   *
   * @param assignment true to use the assignment bound with self-loops and its reduced costs.
   * @param steiner true to use the Steiner cycle bound on the required nodes.
   */
  public void setFiltering(boolean assignment, boolean steiner) {
    this.useAssignment = assignment;
    this.useSteiner = steiner;
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

    for (IntVar x : list) {
      x.domain.in(store.level, x, offset, offset + n - 1);
    }

    boolean again;
    do {
      do {
        store.propagationHasOccurred = false;
        boundsFromRows(store);
        // Every subcircuit costs at most the sum of the row maxima, so the minimum assignment can
        // only prune when the cost has a smaller upper bound, and the same for the maximum
        // assignment, which in addition only runs when the lower bound of the cost is not one
        // this constraint set.
        if (useAssignment && cost.max() < rowsUpperBound) {
          assignmentBound = minAssignment.solve(list, offset);
          setMin(store, assignmentBound);
          minAssignment.prune(store, list, offset, cost.max());
        }
        if (useAssignment
            && cost.min() > rowsLowerBound
            && cost.min() > Math.max(assignmentBound, steinerBound)) {
          long negatedBound = maxAssignment.solve(list, offset);
          setMax(store, -negatedBound);
          maxAssignment.prune(store, list, offset, -(long) cost.min());
        }
      } while (store.propagationHasOccurred);

      // the Steiner bound costs a shortest path search from every required node, so it runs once
      // the assignment has reached its fixpoint, and again only when it pruned
      again = false;
      if (useSteiner && cost.max() < rowsUpperBound) {
        if (steiner == null) {
          steiner = new SteinerCycleBound(list, costs, offset);
        }
        store.propagationHasOccurred = false;
        steiner(store);
        again = store.propagationHasOccurred;
      }
    } while (again);

    if (cost.singleton() && allGround()) {
      checkSubcircuit();
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

  private void checkSubcircuit() {
    if (!isSubcircuit()) {
      throw Store.failException;
    }
  }

  // the ground variables that do not point to themselves form a single cycle
  private boolean isSubcircuit() {
    int start = -1;
    int inCircuit = 0;
    for (int i = 0; i < n; i++) {
      if (list[i].value() - offset != i) {
        start = i;
        inCircuit++;
      }
    }
    if (inCircuit == 0) {
      return true;
    }
    int length = 0;
    int i = start;
    do {
      i = list[i].value() - offset;
      length++;
    } while (i != start && length <= inCircuit);
    return i == start && length == inCircuit;
  }

  // the cost is between the sums of the smallest and of the largest arc cost of each row; exact
  // when all variables are ground
  private void boundsFromRows(Store store) {
    long sumMax = 0;
    long sumMin = 0;
    for (int i = 0; i < n; i++) {
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
    rowsUpperBound = sumMax;
    rowsLowerBound = sumMin;
    setMax(store, sumMax);
    setMin(store, sumMin);
  }

  void setMin(Store store, long min) {
    if (min > cost.max()) {
      throw Store.failException;
    }
    if (min > cost.min()) {
      cost.domain.inMin(store.level, cost, (int) min);
    }
  }

  void setMax(Store store, long max) {
    if (max < cost.min()) {
      throw Store.failException;
    }
    if (max < cost.max()) {
      cost.domain.inMax(store.level, cost, (int) max);
    }
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton() || !allGround()) {
      return false;
    }
    long sum = 0;
    boolean[] pointedTo = new boolean[n];
    for (int i = 0; i < n; i++) {
      int j = list[i].value() - offset;
      if (j < 0 || j >= n || pointedTo[j]) {
        return false;
      }
      pointedTo[j] = true;
      sum += costs[i][j];
    }
    return sum == cost.value() && isSubcircuit();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : SubcircuitCost([");
    appendArrayToString(result, list);
    result.append("], [");
    for (int i = 0; i < n; i++) {
      result.append(Arrays.toString(costs[i]));
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(cost);
    if (offset != 1) {
      result.append(", ").append(offset);
    }
    result.append(')');
    return result.toString();
  }

  /*
   * The Steiner cycle bound on the required nodes. An optional node is charged its cheapest cost,
   * self-loop included, and a node left out its self-loop, so leaving an optional node o out
   * costs c(o, o) - m(o) more than the bound.
   */
  private void steiner(Store store) {
    byte[] kind = steiner.kind;
    long[] charge = steiner.charge;
    int required = 0;
    int optional = 0;
    long base = 0;
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      if (!x.domain.contains(offset + i)) {
        kind[i] = SteinerCycleBound.REQUIRED;
        required++;
      } else if (x.singleton()) {
        kind[i] = SteinerCycleBound.OUT;
        base += costs[i][i];
      } else {
        kind[i] = SteinerCycleBound.OPTIONAL;
        optional++;
        long m = Long.MAX_VALUE;
        int last = x.max();
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          m = Math.min(m, costs[i][val - offset]);
          if (val >= last) {
            break;
          }
        }
        charge[i] = m;
        base += m;
      }
    }
    if (required == 0 || optional == 0) {
      // nothing is required, or the assignment bound already covers this case exactly
      return;
    }

    long lowerBound = base + steiner.solve();
    steinerBound = lowerBound;
    setMin(store, lowerBound);
    long slack = cost.max() - lowerBound;

    for (int a = 0; a < n; a++) {
      if (kind[a] == SteinerCycleBound.OUT) {
        continue;
      }
      IntVar x = list[a];
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int b = val - offset;
        boolean remove;
        if (b == a) {
          // leaving the optional node a out
          remove = costs[a][a] - charge[a] > slack;
        } else {
          remove = kind[b] != SteinerCycleBound.OUT && steiner.arc(a, b) > slack;
        }
        if (remove) {
          x.domain.inComplement(store.level, x, val);
        }
        if (val >= x.max()) {
          break;
        }
      }
    }
  }
}
