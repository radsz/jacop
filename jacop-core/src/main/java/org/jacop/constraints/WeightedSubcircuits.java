/*
 * WeightedSubcircuits.java
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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * WeightedSubcircuits constraint of Vismara and Briot (A Circuit Constraint for Multiple Tours
 * Problems, CP 2018): up to K disjoint circuits, each with its own cost, cover part of the nodes,
 * and the other nodes are left out. Value of every variable x[i] points to the next node of its
 * circuit, or to i itself when node i is left out. tour[i] is the circuit of node i, from 1 to K,
 * or 0 when node i is left out. The constraint holds when
 *
 * <ul>
 *   <li>x[i] = i exactly when tour[i] = 0;
 *   <li>tour[x[i]] = tour[i], and the nodes of each tour k form a single circuit (or none);
 *   <li>tourCost[k - 1] is the sum of costs[i][x[i]] over the nodes of tour k;
 *   <li>cost is the sum of costs[i][x[i]] over all nodes, so the diagonal costs[i][i] is the cost
 *       of leaving node i out (0 when it costs nothing).
 * </ul>
 *
 * <p>With one tour it is a weighted subcircuit ({@link SubcircuitCost}). The x variables must take
 * different values, so post {@link Alldistinct} on them as well; this constraint checks it only
 * when they are ground. The filtering:
 *
 * <ul>
 *   <li>structure: the channelling between x and tour, the tours of the two ends of every arc, and
 *       the rules of the NoSubTours constraint of the paper on the paths of fixed arcs. A path may
 *       close into a circuit only if one of its possible tours has no fixed node outside it, and
 *       must close if no node outside it can join any of its possible tours;
 *   <li>the assignment relaxation of all nodes with the self-loops, which bounds cost and removes
 *       arcs by reduced costs, as in {@link SubcircuitCost};
 *   <li>for every tour, the Steiner cycle bound on the nodes fixed to it, with the nodes that may
 *       join it as optional nodes, which bounds its cost, removes arcs at a fixed node of the tour
 *       and removes the tour from the nodes that cannot join it within its cost.
 * </ul>
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class WeightedSubcircuits extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The successor variables. */
  public final IntVar[] list;

  /** The tour of each node, 0 for the nodes left out. */
  public final IntVar[] tour;

  /** The cost of each arc: costs[i][j] is the cost of list[i] = offset + j. */
  public final int[][] costs;

  /** The cost of each tour. */
  public final IntVar[] tourCost;

  /** The cost of all tours together with the costs of the nodes left out. */
  public final IntVar cost;

  /** The value that points to list[0]. */
  public final int offset;

  private final int n;

  private final int k;

  private boolean useAssignment = true;

  private boolean useSteiner = true;

  private final CircuitCost.Assignment minAssignment;

  private final CircuitCost.Assignment maxAssignment;

  private SteinerCycleBound steiner;

  // the sums of the largest and of the smallest arc cost of each row, from the last call
  private long rowsUpperBound;

  private long rowsLowerBound;

  private long assignmentBound = Long.MIN_VALUE;

  // the largest arc cost of each tour, from the last call
  private final long[] tourUpperBound;

  // scratch arrays of the structural filtering
  private final int[] predecessor;
  private final int[] chain;
  private final boolean[] onChain;
  private final boolean[] visited;

  /**
   * It constructs the constraint with successors numbered from 1.
   *
   * @param list the successor of each node, the node itself when it is left out.
   * @param tour the tour of each node, from 1 to tourCost.length, or 0 when it is left out.
   * @param costs costs[i][j] is the cost of list[i] pointing to list[j]; costs[i][i] is the cost of
   *     leaving node i out.
   * @param tourCost the cost of each tour.
   * @param cost the sum of costs[i][list[i] - 1] over all nodes.
   */
  public WeightedSubcircuits(
      IntVar[] list, IntVar[] tour, int[][] costs, IntVar[] tourCost, IntVar cost) {
    this(list, tour, costs, tourCost, cost, 1);
  }

  /**
   * It constructs the constraint with successors numbered from the given offset.
   *
   * @param list the successor of each node, the node itself when it is left out.
   * @param tour the tour of each node, from 1 to tourCost.length, or 0 when it is left out.
   * @param costs costs[i][j] is the cost of list[i] = offset + j; costs[i][i] is the cost of
   *     leaving node i out.
   * @param tourCost the cost of each tour.
   * @param cost the sum of costs[i][list[i] - offset] over all nodes.
   * @param offset the value that points to list[0]; list[i] is pointed to by offset + i.
   */
  public WeightedSubcircuits(
      IntVar[] list, IntVar[] tour, int[][] costs, IntVar[] tourCost, IntVar cost, int offset) {

    checkInputForNullness(
        new String[] {"list", "tour", "costs", "tourCost", "cost"},
        list,
        tour,
        costs,
        tourCost,
        new Object[] {cost});
    if ((long) offset < IntDomain.MIN_INT || (long) offset + list.length - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException(
          "WeightedSubcircuits has values "
              + offset
              + ".."
              + ((long) offset + list.length - 1)
              + " out of range");
    }
    if (tour.length != list.length || costs.length != list.length) {
      throw new IllegalArgumentException(
          "WeightedSubcircuits needs a tour and a cost row for each of the "
              + list.length
              + " nodes");
    }
    for (int[] row : costs) {
      if (row == null || row.length != list.length) {
        throw new IllegalArgumentException(
            "WeightedSubcircuits needs " + list.length + " costs in each row of costs");
      }
    }
    if (tourCost.length == 0) {
      throw new IllegalArgumentException("WeightedSubcircuits needs at least one tour");
    }
    List<IntVar> all = new ArrayList<>(Arrays.asList(list));
    all.addAll(Arrays.asList(tour));
    all.addAll(Arrays.asList(tourCost));
    all.add(cost);
    checkInputForDuplication("list, tour, tourCost and cost", all.toArray(new IntVar[0]));

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.tour = Arrays.copyOf(tour, tour.length);
    this.n = list.length;
    this.k = tourCost.length;
    this.costs = new int[n][];
    for (int i = 0; i < n; i++) {
      this.costs[i] = Arrays.copyOf(costs[i], n);
    }
    this.tourCost = Arrays.copyOf(tourCost, k);
    this.cost = cost;
    this.offset = offset;
    this.queueIndex = 2;

    minAssignment = new CircuitCost.Assignment(n, this.costs, false);
    maxAssignment = new CircuitCost.Assignment(n, this.costs, true);
    tourUpperBound = new long[k + 1];
    predecessor = new int[n];
    chain = new int[n];
    onChain = new boolean[n];
    visited = new boolean[n];

    setScope(all.toArray(new Var[0]));
  }

  /**
   * It selects the cost relaxations used for filtering.
   *
   * @param assignment true to use the assignment bound with self-loops for the cost.
   * @param steiner true to use the Steiner cycle bound for the cost of each tour.
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
    if (v == cost) {
      return IntDomain.BOUND;
    }
    for (IntVar t : tourCost) {
      if (v == t) {
        return IntDomain.BOUND;
      }
    }
    return IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {

    for (int i = 0; i < n; i++) {
      list[i].domain.in(store.level, list[i], offset, offset + n - 1);
      tour[i].domain.in(store.level, tour[i], 0, k);
    }

    boolean again;
    do {
      do {
        store.propagationHasOccurred = false;
        structure(store);
        costBounds(store);
      } while (store.propagationHasOccurred);

      if (useAssignment) {
        do {
          store.propagationHasOccurred = false;
          if (cost.max() < rowsUpperBound) {
            assignmentBound = minAssignment.solve(list, offset);
            setMin(store, cost, assignmentBound);
            minAssignment.prune(store, list, offset, cost.max());
          }
          if (cost.min() > rowsLowerBound && cost.min() > assignmentBound) {
            long negatedBound = maxAssignment.solve(list, offset);
            setMax(store, cost, -negatedBound);
            maxAssignment.prune(store, list, offset, -(long) cost.min());
          }
        } while (store.propagationHasOccurred);
      }

      store.propagationHasOccurred = false;
      if (useSteiner) {
        for (int t = 1; t <= k; t++) {
          if (tourCost[t - 1].max() < tourUpperBound[t]) {
            if (steiner == null) {
              steiner = new SteinerCycleBound(list, costs, offset);
            }
            steiner(store, t);
          }
        }
      }
      again = store.propagationHasOccurred;
    } while (again);

    if (allGround() && !check()) {
      throw Store.failException;
    }
  }

  // the channelling of x and tour, the tours of the ends of the arcs and the paths of fixed arcs
  private void structure(Store store) {
    int level = store.level;
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      IntVar t = tour[i];
      int self = offset + i;
      if (!t.domain.contains(0)) {
        x.domain.inComplement(level, x, self);
      }
      if (!x.domain.contains(self)) {
        t.domain.inComplement(level, t, 0);
      }
      if (x.singleton(self)) {
        t.domain.in(level, t, 0, 0);
      }
      if (t.singleton(0)) {
        x.domain.in(level, x, self, self);
      }
    }

    // an arc joins two nodes of the same tour
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      if (x.singleton()) {
        continue;
      }
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int j = val - offset;
        if (j != i && !shareTour(i, j)) {
          x.domain.inComplement(level, x, val);
        }
        if (val >= x.max()) {
          break;
        }
      }
    }
    // a node of tour t has a successor and a predecessor that may be in tour t
    for (int i = 0; i < n; i++) {
      IntVar t = tour[i];
      if (t.max() == 0) {
        continue;
      }
      for (int tv = firstTour(t); tv > 0; tv = nextTour(t, tv)) {
        if (!hasSuccessorIn(i, tv) || !hasPredecessorIn(i, tv)) {
          t.domain.inComplement(level, t, tv);
        }
      }
    }

    paths(store);
  }

  private boolean shareTour(int i, int j) {
    IntVar a = tour[i];
    IntVar b = tour[j];
    for (int tv = firstTour(a); tv > 0; tv = nextTour(a, tv)) {
      if (b.domain.contains(tv)) {
        return true;
      }
    }
    return false;
  }

  // the smallest tour in the domain of t, or -1 if it only has 0
  private static int firstTour(IntVar t) {
    if (t.min() > 0) {
      return t.min();
    }
    return t.max() > 0 ? t.domain.nextValue(0) : -1;
  }

  // the next tour after tv in the domain of t, or -1
  private static int nextTour(IntVar t, int tv) {
    return tv >= t.max() ? -1 : t.domain.nextValue(tv);
  }

  private boolean hasSuccessorIn(int i, int tv) {
    IntVar x = list[i];
    for (int val = x.min(); ; val = x.domain.nextValue(val)) {
      int j = val - offset;
      if (j != i && tour[j].domain.contains(tv)) {
        return true;
      }
      if (val >= x.max()) {
        return false;
      }
    }
  }

  private boolean hasPredecessorIn(int i, int tv) {
    int self = offset + i;
    for (int p = 0; p < n; p++) {
      if (p != i && list[p].domain.contains(self) && tour[p].domain.contains(tv)) {
        return true;
      }
    }
    return false;
  }

  /*
   * The paths of fixed arcs. All nodes of a path are in one tour. A path from b to e may close
   * (x[e] = b) only if one of its possible tours has no fixed node outside the path, and must
   * close if no node outside the path may join any of its possible tours. A closed circuit is a
   * whole tour: its tour is fixed when other nodes fix the other tours, and other nodes cannot
   * join it.
   */
  private void paths(Store store) {
    int level = store.level;
    Arrays.fill(predecessor, -1);
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      if (x.singleton() && x.value() - offset != i) {
        int j = x.value() - offset;
        if (predecessor[j] != -1 || list[j].singleton(offset + j)) {
          // two arcs into j, or an arc into a node left out
          throw Store.failException;
        }
        predecessor[j] = i;
      }
    }
    Arrays.fill(visited, false);
    // a failure in a previous call may have left nodes marked
    Arrays.fill(onChain, false);
    for (int s = 0; s < n; s++) {
      if (visited[s]
          || predecessor[s] != -1
          || !list[s].singleton()
          || list[s].value() == offset + s) {
        continue;
      }
      // an open path from s
      int length = 0;
      int e = s;
      while (true) {
        visited[e] = true;
        onChain[e] = true;
        chain[length++] = e;
        IntVar x = list[e];
        if (!x.singleton()) {
          break;
        }
        e = x.value() - offset;
      }
      closePath(level, s, e, length);
      for (int c = 0; c < length; c++) {
        onChain[chain[c]] = false;
      }
    }
    for (int s = 0; s < n; s++) {
      if (visited[s] || predecessor[s] == -1) {
        continue;
      }
      // the rest are circuits of fixed arcs
      int length = 0;
      int e = s;
      do {
        visited[e] = true;
        onChain[e] = true;
        chain[length++] = e;
        e = list[e].value() - offset;
      } while (e != s);
      circuit(level, length);
      for (int c = 0; c < length; c++) {
        onChain[chain[c]] = false;
      }
    }
  }

  private void closePath(int level, int s, int e, int length) {
    IntVar t = tour[s];
    boolean mayClose = false;
    boolean mustClose = true;
    for (int tv = firstTour(t); tv > 0; tv = nextTour(t, tv)) {
      boolean fixedOutside = false;
      boolean possibleOutside = false;
      for (int o = 0; o < n && !fixedOutside; o++) {
        if (!onChain[o] && tour[o].domain.contains(tv)) {
          possibleOutside = true;
          fixedOutside = tour[o].singleton();
        }
      }
      mayClose |= !fixedOutside;
      mustClose &= !possibleOutside;
    }
    IntVar x = list[e];
    if (!mayClose) {
      x.domain.inComplement(level, x, offset + s);
    } else if (mustClose && t.min() > 0) {
      x.domain.in(level, x, offset + s, offset + s);
    }
  }

  private void circuit(int level, int length) {
    for (int o = 0; o < n; o++) {
      if (!onChain[o] && tour[o].singleton() && tour[o].value() > 0) {
        for (int c = 0; c < length; c++) {
          IntVar t = tour[chain[c]];
          t.domain.inComplement(level, t, tour[o].value());
        }
      }
    }
    IntVar t = tour[chain[0]];
    if (t.singleton()) {
      for (int o = 0; o < n; o++) {
        if (!onChain[o]) {
          tour[o].domain.inComplement(level, tour[o], t.value());
        }
      }
    }
  }

  // the bounds of the costs from the arc costs in the domains, and cost = sum of tourCost plus the
  // costs of the nodes left out
  private void costBounds(Store store) {
    long sumMax = 0;
    long sumMin = 0;
    long[] tourMin = new long[k + 1];
    long[] tourMax = new long[k + 1];
    long outMin = 0;
    long outMax = 0;
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      IntVar t = tour[i];
      int[] row = costs[i];
      long max = Long.MIN_VALUE;
      long min = Long.MAX_VALUE;
      long arcMax = Long.MIN_VALUE;
      long arcMin = Long.MAX_VALUE;
      int last = x.max();
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int j = val - offset;
        long c = row[j];
        max = Math.max(max, c);
        min = Math.min(min, c);
        if (j != i) {
          arcMax = Math.max(arcMax, c);
          arcMin = Math.min(arcMin, c);
        }
        if (val >= last) {
          break;
        }
      }
      sumMax += max;
      sumMin += min;
      if (t.domain.contains(0)) {
        long d = row[i];
        outMin += t.singleton() ? d : Math.min(0, d);
        outMax += t.singleton() ? d : Math.max(0, d);
      }
      if (t.max() > 0 && arcMin == Long.MAX_VALUE) {
        // node i has no arc to join a tour; the channelling leaves it out
        if (!t.domain.contains(0)) {
          throw Store.failException;
        }
        continue;
      }
      for (int tv = firstTour(t); tv > 0; tv = nextTour(t, tv)) {
        if (t.singleton()) {
          tourMin[tv] += arcMin;
          tourMax[tv] += arcMax;
        } else {
          tourMin[tv] += Math.min(0, arcMin);
          tourMax[tv] += Math.max(0, arcMax);
        }
      }
    }
    rowsUpperBound = sumMax;
    rowsLowerBound = sumMin;
    setMax(store, cost, sumMax);
    setMin(store, cost, sumMin);
    long costsMin = 0;
    long costsMax = 0;
    for (int tv = 1; tv <= k; tv++) {
      IntVar tc = tourCost[tv - 1];
      tourUpperBound[tv] = tourMax[tv];
      setMin(store, tc, tourMin[tv]);
      setMax(store, tc, tourMax[tv]);
      costsMin += tc.min();
      costsMax += tc.max();
    }
    setMin(store, cost, costsMin + outMin);
    setMax(store, cost, costsMax + outMax);
    for (int tv = 1; tv <= k; tv++) {
      IntVar tc = tourCost[tv - 1];
      setMin(store, tc, cost.min() - (costsMax - tc.max()) - outMax);
      setMax(store, tc, cost.max() - (costsMin - tc.min()) - outMin);
    }
  }

  /*
   * The Steiner cycle bound of tour t: the nodes fixed to it are required, the nodes that may join
   * it are optional, and an optional node is charged the smaller of 0 and its cheapest arc to a
   * node of the tour, since it adds nothing to the cost of the tour when it does not join it.
   */
  private void steiner(Store store, int t) {
    byte[] kind = steiner.kind;
    long[] charge = steiner.charge;
    int required = 0;
    for (int i = 0; i < n; i++) {
      IntVar tv = tour[i];
      if (!tv.domain.contains(t)) {
        kind[i] = SteinerCycleBound.OUT;
      } else if (tv.singleton()) {
        kind[i] = SteinerCycleBound.REQUIRED;
        required++;
      } else {
        kind[i] = SteinerCycleBound.OPTIONAL;
      }
    }
    if (required == 0) {
      return;
    }
    long base = 0;
    for (int i = 0; i < n; i++) {
      if (kind[i] == SteinerCycleBound.OPTIONAL) {
        long m = 0;
        IntVar x = list[i];
        int last = x.max();
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int j = val - offset;
          if (j != i && kind[j] != SteinerCycleBound.OUT) {
            m = Math.min(m, costs[i][j]);
          }
          if (val >= last) {
            break;
          }
        }
        charge[i] = m;
        base += m;
      }
    }

    IntVar tc = tourCost[t - 1];
    long lowerBound = base + steiner.solve();
    setMin(store, tc, lowerBound);
    long slack = tc.max() - lowerBound;

    int level = store.level;
    for (int a = 0; a < n; a++) {
      if (kind[a] == SteinerCycleBound.OUT) {
        continue;
      }
      if (kind[a] == SteinerCycleBound.OPTIONAL && steiner.node(a) > slack) {
        tour[a].domain.inComplement(level, tour[a], t);
        continue;
      }
      IntVar x = list[a];
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        int b = val - offset;
        // an arc at a node fixed to tour t is in tour t when it is used
        if (b != a
            && kind[b] != SteinerCycleBound.OUT
            && (kind[a] == SteinerCycleBound.REQUIRED || kind[b] == SteinerCycleBound.REQUIRED)
            && steiner.arc(a, b) > slack) {
          x.domain.inComplement(level, x, val);
        }
        if (val >= x.max()) {
          break;
        }
      }
    }
  }

  private static void setMin(Store store, IntVar v, long min) {
    if (min > v.max()) {
      throw Store.failException;
    }
    if (min > v.min()) {
      v.domain.inMin(store.level, v, (int) min);
    }
  }

  private static void setMax(Store store, IntVar v, long max) {
    if (max < v.min()) {
      throw Store.failException;
    }
    if (max < v.max()) {
      v.domain.inMax(store.level, v, (int) max);
    }
  }

  private boolean allGround() {
    for (int i = 0; i < n; i++) {
      if (!list[i].singleton() || !tour[i].singleton()) {
        return false;
      }
    }
    return true;
  }

  // the definition on ground x and tour; the costs only when they are ground
  private boolean check() {
    boolean[] pointedTo = new boolean[n];
    long[] sums = new long[k + 1];
    long total = 0;
    int[] size = new int[k + 1];
    int[] start = new int[k + 1];
    for (int i = 0; i < n; i++) {
      int j = list[i].value() - offset;
      int t = tour[i].value();
      if (j < 0 || j >= n || pointedTo[j] || t < 0 || t > k || (j == i) != (t == 0)) {
        return false;
      }
      if (tour[j].value() != t) {
        return false;
      }
      pointedTo[j] = true;
      total += costs[i][j];
      sums[t] += costs[i][j];
      size[t]++;
      start[t] = i;
    }
    for (int t = 1; t <= k; t++) {
      if (size[t] > 0) {
        int length = 0;
        int i = start[t];
        do {
          i = list[i].value() - offset;
          length++;
        } while (i != start[t]);
        if (length != size[t]) {
          return false;
        }
      }
      IntVar tc = tourCost[t - 1];
      if (tc.singleton() && tc.value() != sums[t]) {
        return false;
      }
    }
    return !cost.singleton() || cost.value() == total;
  }

  @Override
  public boolean satisfied() {
    if (!allGround() || !cost.singleton()) {
      return false;
    }
    for (IntVar tc : tourCost) {
      if (!tc.singleton()) {
        return false;
      }
    }
    return check();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : WeightedSubcircuits([");
    appendArrayToString(result, list);
    result.append("], [");
    appendArrayToString(result, tour);
    result.append("], [");
    for (int i = 0; i < n; i++) {
      result.append(Arrays.toString(costs[i]));
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], [");
    appendArrayToString(result, tourCost);
    result.append("], ").append(cost);
    if (offset != 1) {
      result.append(", ").append(offset);
    }
    result.append(')');
    return result.toString();
  }
}
