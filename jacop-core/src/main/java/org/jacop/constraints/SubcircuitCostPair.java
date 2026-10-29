/*
 * SubcircuitCostPair.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Two sums of arc costs on one subcircuit, such as a prize to collect within a length budget,
 * filtered together by Lagrangian relaxation. For arc costs a and b with sum(b) &lt;= B every
 * assignment of the successors, and so every subcircuit, satisfies
 *
 * <pre>
 *   a(x) &gt;= min over assignments of (a + lambda * b) - lambda * B   for every lambda &gt;= 0,
 * </pre>
 *
 * the minimum assignment bound of a weighed against b. It bounds both sums from both sides, the
 * other sum's bound giving B (with negated costs for the other sides), and removes every arc whose
 * reduced cost takes the bound past the bounded sum's other bound. Lambda = 0 is the plain bound of
 * {@link SubcircuitCost}, so a direction searches lambda only when the plain optimum breaks the
 * other sum's bound. The search walks the piecewise linear concave function of lambda: doubling or
 * halving from the last best lambda of the direction to a bracket, then the meeting points of the
 * lines at its ends. Each direction keeps an incremental Hungarian method, whose duals are repaired
 * when lambda changes. A direction that prunes nothing skips its next calls, twice as many after
 * each miss, up to 63.
 *
 * <p>Like the assignment bound it ignores connectivity, so it is posted next to a subcircuit, and
 * it does not check that the successors form one.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class SubcircuitCostPair extends Constraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The most nodes; larger subcircuits are only restricted to their values. */
  public static final int NODE_LIMIT = 500;

  // lambda = p / SCALE
  private static final long SCALE = 1024;

  // the most assignments solved for one direction in one call
  private static final int SOLVES = 8;

  // a direction that prunes nothing skips up to 2^MAX_BACKOFF - 1 calls
  private static final int MAX_BACKOFF = 6;

  /** The successors. */
  public final IntVar[] list;

  /**
   * The arc costs of each sum, costs[k][i][j] for list[i] = offset + j, the diagonal leaving i out.
   */
  public final int[][][] costs;

  /** The two sums. */
  public final IntVar[] cost;

  /** The value that points to list[0]. */
  public final int offset;

  private final int n;

  // the largest absolute arc cost of each sum, at least 1
  private final long[] maxCost = new long[2];

  // per direction (see direction): the last best p and the Hungarian method
  private final long[] lastP = new long[8];
  private final CircuitCost.Assignment[] assignments = new CircuitCost.Assignment[8];

  // per direction: calls in a row that pruned nothing, and calls left to skip
  private final int[] misses = new int[8];
  private final int[] skips = new int[8];

  // sb * b of the last assignment solved
  private long last;

  /**
   * It constructs the constraint.
   *
   * @param list the successors, which form a subcircuit by another constraint.
   * @param costs1 the arc costs of the first sum, costs1[i][j] for list[i] = offset + j.
   * @param cost1 the first sum.
   * @param costs2 the arc costs of the second sum.
   * @param cost2 the second sum.
   * @param offset the value that points to list[0].
   */
  public SubcircuitCostPair(
      IntVar[] list, int[][] costs1, IntVar cost1, int[][] costs2, IntVar cost2, int offset) {
    checkInputForNullness(
        new String[] {"list", "costs1", "cost1", "costs2", "cost2"},
        list,
        costs1,
        new Object[] {cost1},
        costs2,
        new Object[] {cost2});
    checkInputForDuplication("list", list);
    n = list.length;
    if ((long) offset < IntDomain.MIN_INT || (long) offset + n - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException(
          "SubcircuitCostPair has values "
              + offset
              + ".."
              + ((long) offset + n - 1)
              + " out of range");
    }
    for (int[][] c : new int[][][] {costs1, costs2}) {
      if (c.length != n) {
        throw new IllegalArgumentException(
            "SubcircuitCostPair needs a cost row for each of the " + n + " variables");
      }
      for (int[] row : c) {
        if (row == null || row.length != n) {
          throw new IllegalArgumentException(
              "SubcircuitCostPair needs " + n + " costs in each row of costs");
        }
      }
    }
    if (cost1 == cost2) {
      throw new IllegalArgumentException("SubcircuitCostPair needs two different sums");
    }
    for (IntVar x : list) {
      if (x == cost1 || x == cost2) {
        throw new IllegalArgumentException("SubcircuitCostPair sum is also in list");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, n);
    this.costs = new int[2][n][];
    for (int i = 0; i < n; i++) {
      this.costs[0][i] = Arrays.copyOf(costs1[i], n);
      this.costs[1][i] = Arrays.copyOf(costs2[i], n);
    }
    this.cost = new IntVar[] {cost1, cost2};
    for (int k = 0; k < 2; k++) {
      long max = 1;
      for (int[] row : costs[k]) {
        for (int c : row) {
          max = Math.max(max, Math.abs((long) c));
        }
      }
      maxCost[k] = max;
    }
    this.offset = offset;
    this.queueIndex = 4;
    setScope(list, new IntVar[] {cost1, cost2});
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getConsistencyPruningEvent(Var var) {
    Integer event = getConsistencyPruningEventFromMap(var);
    if (event != null) {
      return event;
    }
    return var == cost[0] || var == cost[1] ? IntDomain.BOUND : IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {
    for (IntVar x : list) {
      x.domain.in(store.level, x, offset, offset + n - 1);
    }
    if (n > NODE_LIMIT) {
      return;
    }
    // one pass: what it prunes wakes it again
    for (int d = 0; d < 8; d++) {
      if (skips[d] > 0) {
        skips[d]--;
        continue;
      }
      int sizes = size();
      direction(store, d);
      if (size() < sizes) {
        misses[d] = 0;
      } else {
        // pruned nothing: back off exponentially
        misses[d]++;
        skips[d] = (1 << Math.min(misses[d], MAX_BACKOFF)) - 1;
      }
    }
  }

  /*
   * Direction d bounds sum a = d >> 2 from below (sa = 1) or from above (sa = -1, bit 1), weighed
   * against the other sum b at most its maximum (sb = 1) or at least its minimum (sb = -1, bit 0):
   * with B = max(b), or -min(b), every assignment x has
   * SCALE * sa * a(x) >= min (SCALE * sa * a + p * sb * b) - p * B for p >= 0.
   */
  private void direction(Store store, int d) {
    int a = d >> 2;
    int b = 1 - a;
    long sa = (d & 2) == 0 ? 1 : -1;
    long sb = (d & 1) == 0 ? 1 : -1;
    IntVar ca = cost[a];
    IntVar cb = cost[b];
    long bound = sb > 0 ? cb.max() : -(long) cb.min();
    // the bound of b cuts no assignment off
    if (rowSum(b, sb) <= bound) {
      lastP[d] = 0;
      return;
    }
    // the limit of sa * a: a <= max, or -a <= -min
    long limit = sa > 0 ? ca.max() : -(long) ca.min();
    long pLimit = (Long.MAX_VALUE / 16) / (n * (SCALE * maxCost[a] + maxCost[b]) + Math.abs(bound));

    // p = 0: when its optimum keeps sb * b within the bound, no p does better
    long plain = solve(d, a, sa, b, sb, 0);
    long slope = last - bound;
    if (slope <= 0) {
      lastP[d] = 0;
      return;
    }

    // a bracket [lo, hi] of p, the slope positive at lo and at most 0 at hi
    long lo = 0;
    long loValue = plain;
    long loSlope = slope;
    long hi = -1;
    long hiValue = 0;
    long hiSlope = 0;
    long best = plain;
    long bestP = 0;
    long solvedP = 0;
    int solves = 1;
    long p = Math.min(Math.max(1, lastP[d]), pLimit);
    while (solves < SOLVES) {
      long value = solve(d, a, sa, b, sb, p);
      solves++;
      solvedP = p;
      long s = last - bound;
      long g = value - p * bound;
      if (g > best) {
        best = g;
        bestP = p;
      }
      if (s > 0) {
        lo = p;
        loValue = value;
        loSlope = s;
        if (hi >= 0 || 2 * p > pLimit) {
          break;
        }
        p *= 2;
      } else {
        hi = p;
        hiValue = value;
        hiSlope = s;
        if (lo > 0 || p == 1) {
          break;
        }
        p = Math.max(1, p / 2);
      }
    }
    // the lines at lo and hi meet at the next p, until it lies on them
    while (hi >= 0 && solves < SOLVES && hi - lo > 1) {
      long gLo = loValue - lo * bound;
      long gHi = hiValue - hi * bound;
      double meet = lo + (double) (gHi - gLo + (lo - hi) * hiSlope) / (loSlope - hiSlope);
      long next = Math.round(meet);
      if (next <= lo || next >= hi) {
        break;
      }
      long value = solve(d, a, sa, b, sb, next);
      solves++;
      solvedP = next;
      long s = last - bound;
      long g = value - next * bound;
      if (g > best) {
        best = g;
        bestP = next;
      }
      if (g >= gLo + (double) (next - lo) * loSlope - 0.5) {
        break;
      }
      if (s > 0) {
        lo = next;
        loValue = value;
        loSlope = s;
      } else {
        hi = next;
        hiValue = value;
        hiSlope = s;
      }
    }
    lastP[d] = bestP;
    if (bestP == 0) {
      return;
    }

    // SCALE * sa * a >= best
    long lower = Math.floorDiv(best + SCALE - 1, SCALE);
    if (lower > limit) {
      throw Store.failException;
    }
    if (sa > 0) {
      CostBounds.setMin(store, ca, lower);
    } else {
      CostBounds.setMax(store, ca, -lower);
    }

    // an arc whose reduced cost takes SCALE * sa * a past SCALE * limit
    if (solvedP != bestP) {
      solve(d, a, sa, b, sb, bestP);
    }
    assignments[d].prune(store, list, offset, SCALE * limit + bestP * bound);
  }

  // the domain sizes of the successors and the sums
  private int size() {
    int size = cost[0].getSize() + cost[1].getSize();
    for (IntVar x : list) {
      size += x.getSize();
    }
    return size;
  }

  // the largest sb * b of an assignment ignoring the columns: the sum of the row maxima
  private long rowSum(int b, long sb) {
    long sum = 0;
    int[][] c = costs[b];
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      int[] row = c[i];
      long max = Long.MIN_VALUE;
      int end = x.max();
      for (int val = x.min(); ; val = x.domain.nextValue(val)) {
        max = Math.max(max, sb * row[val - offset]);
        if (val >= end) {
          break;
        }
      }
      sum += max;
    }
    return sum;
  }

  /*
   * The minimum assignment of the weights SCALE * sa * a + p * sb * b of direction d over the
   * current domains, by the direction's incremental Hungarian method, with sb * b of its matching
   * in last; Store.failException when the successors cannot all be matched.
   */
  private long solve(int d, int a, long sa, int b, long sb, long p) {
    CircuitCost.Assignment assignment = assignments[d];
    if (assignment == null) {
      assignment = new CircuitCost.Assignment(n, costs[a], false);
      assignments[d] = assignment;
    }
    int[][] ca = costs[a];
    int[][] cb = costs[b];
    long[][] w = assignment.weights();
    for (int i = 0; i < n; i++) {
      long[] row = w[i];
      for (int j = 0; j < n; j++) {
        row[j] = SCALE * sa * ca[i][j] + p * sb * cb[i][j];
      }
    }
    long value = assignment.solve(list, offset);
    long sum = 0;
    for (int i = 0; i < n; i++) {
      sum += cb[i][assignment.rowMate(i)];
    }
    last = sb * sum;
    return value;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : SubcircuitCostPair([");
    appendArrayToString(result, list);
    result.append("], ");
    CostBounds.appendCosts(result, costs[0]);
    result.append(", ").append(cost[0]).append(", ");
    CostBounds.appendCosts(result, costs[1]);
    result.append(", ").append(cost[1]);
    if (offset != 1) {
      result.append(", ").append(offset);
    }
    result.append(')');
    return result.toString();
  }
}
