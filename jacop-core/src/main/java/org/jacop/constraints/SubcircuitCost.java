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

  private Steiner steiner;

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
          steiner = new Steiner();
        }
        store.propagationHasOccurred = false;
        steiner.propagate(store);
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

  /**
   * The Steiner cycle relaxation of Vismara and Briot on the required nodes R (x[i] != i). The
   * optional nodes O may be on the circuit or not, and the nodes left out are fixed.
   *
   * <p>Each optional node o is charged m(o), the cheapest cost in its domain (its self-loop
   * included), and an arc o to j then costs c(o, j) - m(o) &gt;= 0, so the cost of any subcircuit
   * is at least the charges plus the costs of the paths that link each required node to the next
   * one through optional nodes. The cheapest such path from i to j, d(i, j), is found by Dijkstra's
   * algorithm, and the minimum assignment of R on d, without self-loops when |R| &gt;= 2 (all
   * required nodes are on one cycle), bounds the cost. With |R| = 1, d(i, i) is the cheapest cycle
   * through i.
   *
   * <p>An arc a to b forced into the circuit lies on the path from some required node i to some
   * required node j, so the assignment costs at least its dual bound plus F(a) + c'(a, b) + G(b),
   * where F(a) = min over i of (shortest path from i to a) - u(i) and G(b) = min over j of
   * (shortest path from b to j) - v(j), with F = -u and G = -v on the required nodes themselves.
   * Both are computed by one multi-source Dijkstra each. Leaving an optional node o out costs at
   * least c(o, o) - m(o) more than the bound.
   */
  private final class Steiner {

    private static final long INF = Long.MAX_VALUE / 8;

    private static final byte OUT = 0;
    private static final byte REQUIRED = 1;
    private static final byte OPTIONAL = 2;

    private final byte[] kind = new byte[n];
    // the required nodes, and the position of each in that list
    private final int[] required = new int[n];
    private final int[] position = new int[n];
    private final long[] charge = new long[n];
    private final long[] dist = new long[n];
    private final boolean[] done = new boolean[n];
    private final long[] forward = new long[n];
    private final long[] backward = new long[n];
    private long[][] weight = new long[0][];

    // the Hungarian method on the required nodes (1-based arrays)
    private long[] u = new long[1];
    private long[] v = new long[1];
    private int[] mate = new int[1];
    private int[] way = new int[1];
    private long[] minv = new long[1];
    private boolean[] used = new boolean[1];

    void propagate(Store store) {

      int r = 0;
      int optional = 0;
      long base = 0;
      for (int i = 0; i < n; i++) {
        IntVar x = list[i];
        int self = offset + i;
        if (!x.domain.contains(self)) {
          kind[i] = REQUIRED;
          position[i] = r;
          required[r++] = i;
        } else if (x.singleton()) {
          kind[i] = OUT;
          base += costs[i][i];
        } else {
          kind[i] = OPTIONAL;
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
      if (r == 0 || optional == 0) {
        // nothing is required, or the assignment bound already covers this case exactly
        return;
      }

      if (weight.length < r) {
        weight = new long[r][r];
        u = new long[r + 1];
        v = new long[r + 1];
        mate = new int[r + 1];
        way = new int[r + 1];
        minv = new long[r + 1];
        used = new boolean[r + 1];
      }
      for (int k = 0; k < r; k++) {
        paths(required[k], weight[k], r);
      }

      long bound;
      if (r == 1) {
        bound = weight[0][0];
        if (bound >= INF) {
          throw Store.failException;
        }
        u[1] = bound;
        v[1] = 0;
      } else {
        for (int k = 0; k < r; k++) {
          weight[k][k] = INF;
        }
        bound = hungarian(r);
      }

      long lowerBound = base + bound;
      steinerBound = lowerBound;
      setMin(store, lowerBound);
      long slack = cost.max() - lowerBound;

      forwardPaths(r);
      backwardPaths(r);

      for (int a = 0; a < n; a++) {
        if (kind[a] == OUT) {
          continue;
        }
        IntVar x = list[a];
        long fa = kind[a] == REQUIRED ? -u[position[a] + 1] : forward[a];
        long chargeA = kind[a] == REQUIRED ? 0 : charge[a];
        int[] row = costs[a];
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int b = val - offset;
          boolean remove;
          if (b == a) {
            // leaving the optional node a out
            remove = row[a] - chargeA > slack;
          } else if (kind[b] == OUT) {
            remove = false;
          } else {
            long gb = kind[b] == REQUIRED ? -v[position[b] + 1] : backward[b];
            remove = fa >= INF || gb >= INF || fa + row[b] - chargeA + gb > slack;
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

    // the cheapest paths from the required node s through optional nodes to every required node
    private void paths(int s, long[] out, int r) {
      Arrays.fill(out, 0, r, INF);
      Arrays.fill(dist, INF);
      Arrays.fill(done, false);
      relax(s, 0, 0, out);
      while (true) {
        int best = -1;
        long bestDist = INF;
        for (int o = 0; o < n; o++) {
          if (kind[o] == OPTIONAL && !done[o] && dist[o] < bestDist) {
            bestDist = dist[o];
            best = o;
          }
        }
        if (best < 0) {
          return;
        }
        done[best] = true;
        relax(best, bestDist, charge[best], out);
      }
    }

    // the arcs leaving node a, reached at distance d, with the charge of a taken off
    private void relax(int a, long d, long chargeA, long[] out) {
      IntVar x = list[a];
      int[] row = costs[a];
      int last = x.max();
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int b = val - offset;
        if (b != a) {
          long nd = d + row[b] - chargeA;
          if (kind[b] == REQUIRED) {
            int p = position[b];
            if (nd < out[p]) {
              out[p] = nd;
            }
          } else if (kind[b] == OPTIONAL && !done[b] && nd < dist[b]) {
            dist[b] = nd;
          }
        }
        if (val >= last) {
          break;
        }
      }
    }

    // forward[o] = min over required i of (cheapest path from i to the optional node o) - u(i)
    private void forwardPaths(int r) {
      Arrays.fill(forward, INF);
      Arrays.fill(done, false);
      for (int k = 0; k < r; k++) {
        int i = required[k];
        long ui = u[k + 1];
        IntVar x = list[i];
        int[] row = costs[i];
        int last = x.max();
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int b = val - offset;
          if (kind[b] == OPTIONAL) {
            long d = row[b] - ui;
            if (d < forward[b]) {
              forward[b] = d;
            }
          }
          if (val >= last) {
            break;
          }
        }
      }
      while (true) {
        int best = -1;
        long bestDist = INF;
        for (int o = 0; o < n; o++) {
          if (kind[o] == OPTIONAL && !done[o] && forward[o] < bestDist) {
            bestDist = forward[o];
            best = o;
          }
        }
        if (best < 0) {
          return;
        }
        done[best] = true;
        IntVar x = list[best];
        int[] row = costs[best];
        long c = charge[best];
        int last = x.max();
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int b = val - offset;
          if (b != best && kind[b] == OPTIONAL && !done[b]) {
            long d = bestDist + row[b] - c;
            if (d < forward[b]) {
              forward[b] = d;
            }
          }
          if (val >= last) {
            break;
          }
        }
      }
    }

    // backward[o] = min over required j of (cheapest path from the optional node o to j) - v(j)
    private void backwardPaths(int r) {
      Arrays.fill(backward, INF);
      Arrays.fill(done, false);
      for (int o = 0; o < n; o++) {
        if (kind[o] != OPTIONAL) {
          continue;
        }
        IntVar x = list[o];
        int[] row = costs[o];
        long c = charge[o];
        int last = x.max();
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int b = val - offset;
          if (kind[b] == REQUIRED) {
            long d = row[b] - c - v[position[b] + 1];
            if (d < backward[o]) {
              backward[o] = d;
            }
          }
          if (val >= last) {
            break;
          }
        }
      }
      while (true) {
        int best = -1;
        long bestDist = INF;
        for (int o = 0; o < n; o++) {
          if (kind[o] == OPTIONAL && !done[o] && backward[o] < bestDist) {
            bestDist = backward[o];
            best = o;
          }
        }
        if (best < 0) {
          return;
        }
        done[best] = true;
        int val = offset + best;
        for (int a = 0; a < n; a++) {
          if (a != best && kind[a] == OPTIONAL && !done[a] && list[a].domain.contains(val)) {
            long d = bestDist + costs[a][best] - charge[a];
            if (d < backward[a]) {
              backward[a] = d;
            }
          }
        }
      }
    }

    /**
     * The minimum assignment of the r required nodes on weight, by the Hungarian method with
     * shortest augmenting paths; u and v get its duals. Infinite weights are replaced by a weight
     * larger than any assignment of finite ones, so an assignment that needs one means that the
     * required nodes cannot be linked into a cycle.
     */
    private long hungarian(int r) {
      long big = 1;
      for (int i = 0; i < r; i++) {
        long rowMax = 0;
        for (int j = 0; j < r; j++) {
          if (weight[i][j] < INF) {
            rowMax = Math.max(rowMax, Math.abs(weight[i][j]));
          }
        }
        big += 2 * rowMax;
      }
      for (int i = 0; i < r; i++) {
        for (int j = 0; j < r; j++) {
          if (weight[i][j] >= INF) {
            weight[i][j] = big;
          }
        }
      }
      Arrays.fill(u, 0, r + 1, 0);
      Arrays.fill(v, 0, r + 1, 0);
      Arrays.fill(mate, 0, r + 1, 0);
      for (int i = 1; i <= r; i++) {
        mate[0] = i;
        int j0 = 0;
        Arrays.fill(minv, 0, r + 1, Long.MAX_VALUE);
        Arrays.fill(used, 0, r + 1, false);
        do {
          used[j0] = true;
          int i0 = mate[j0];
          long delta = Long.MAX_VALUE;
          int j1 = 0;
          long[] w = weight[i0 - 1];
          for (int j = 1; j <= r; j++) {
            if (!used[j]) {
              long cur = w[j - 1] - u[i0] - v[j];
              if (cur < minv[j]) {
                minv[j] = cur;
                way[j] = j0;
              }
              if (minv[j] < delta) {
                delta = minv[j];
                j1 = j;
              }
            }
          }
          for (int j = 0; j <= r; j++) {
            if (used[j]) {
              u[mate[j]] += delta;
              v[j] -= delta;
            } else {
              minv[j] -= delta;
            }
          }
          j0 = j1;
        } while (mate[j0] != 0);
        do {
          int j1 = way[j0];
          mate[j0] = mate[j1];
          j0 = j1;
        } while (j0 != 0);
      }
      long sum = 0;
      for (int j = 1; j <= r; j++) {
        long w = weight[mate[j] - 1][j - 1];
        if (w == big) {
          throw Store.failException;
        }
        sum += w;
      }
      // u[0] is not a dual of any row; the duals of the rows and columns sum to the assignment
      u[0] = 0;
      return sum;
    }
  }
}
