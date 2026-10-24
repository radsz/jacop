/*
 * KnapsackDP.java
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

package org.jacop.constraints.knapsack;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * A knapsack constraint, sum(weights[i] * quantity[i]) = capacity and sum(profits[i] * quantity[i])
 * = profit, propagated by dynamic programming over the used capacity, following M. Trick, "A
 * dynamic programming approach for consistency and propagation for knapsack constraints", Annals of
 * Operations Research 118 (2003).
 *
 * <p>For every used capacity it computes the maximal (and, when the maximal profit restricts, the
 * minimal) profit of the items before and after each item. A value of a quantity is kept only if
 * some assignment using it reaches a capacity in the capacity domain with a profit of at least the
 * minimal profit, and some assignment using it reaches a capacity in the capacity domain with a
 * profit of at most the maximal profit. This gives domain consistency for the quantities with
 * respect to the capacity domain and each profit bound, prunes values of the capacity, and gives
 * the bounds of the profit. It costs O(n * C * d) time for n items, a remaining capacity C and
 * quantities with at most d values, and O(n * C) memory, so it is skipped (no pruning) when n * C
 * is above a limit. It is meant to be used together with {@link Knapsack}, which is cheap and
 * propagates in all cases.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class KnapsackDP extends Constraint implements SatisfiedPresent {

  private static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The default limit on the number of items times the remaining capacity. */
  public static final long DEFAULT_LIMIT = 2_000_000L;

  private static final long UNREACHABLE = Long.MIN_VALUE / 4;

  private final IntVar[] quantity;

  private final int[] weights;

  private final int[] profits;

  private final IntVar knapsackCapacity;

  private final IntVar knapsackProfit;

  private final long limit;

  /** Best profit for each layer and capacity, reused between calls. */
  private long[][] forward;

  /**
   * It constructs the constraint with the default limit.
   *
   * @param profits the profit of one unit of each item, at least 0.
   * @param weights the weight of one unit of each item, at least 0.
   * @param quantity the quantity of each item.
   * @param knapsackCapacity the used capacity.
   * @param knapsackProfit the obtained profit.
   */
  public KnapsackDP(
      int[] profits,
      int[] weights,
      IntVar[] quantity,
      IntVar knapsackCapacity,
      IntVar knapsackProfit) {
    this(profits, weights, quantity, knapsackCapacity, knapsackProfit, DEFAULT_LIMIT);
  }

  /**
   * It constructs the constraint.
   *
   * @param profits the profit of one unit of each item, at least 0.
   * @param weights the weight of one unit of each item, at least 0.
   * @param quantity the quantity of each item.
   * @param knapsackCapacity the used capacity.
   * @param knapsackProfit the obtained profit.
   * @param limit the maximal number of items times remaining capacity for which the dynamic program
   *     is run.
   */
  public KnapsackDP(
      int[] profits,
      int[] weights,
      IntVar[] quantity,
      IntVar knapsackCapacity,
      IntVar knapsackProfit,
      long limit) {

    checkInputForNullness(
        new String[] {"profits", "weights", "quantity", "knapsackCapacity", "knapsackProfit"},
        new Object[] {profits},
        new Object[] {weights},
        quantity,
        new Object[] {knapsackCapacity},
        new Object[] {knapsackProfit});

    if (profits.length != weights.length || profits.length != quantity.length) {
      throw new IllegalArgumentException(
          "Constraint KnapsackDP has profits, weights and quantity parameters of different length");
    }
    for (int i = 0; i < weights.length; i++) {
      if (weights[i] < 0 || profits[i] < 0) {
        throw new IllegalArgumentException(
            "Constraint KnapsackDP requires weights and profits of at least 0.");
      }
    }

    numberId = idNumber.incrementAndGet();
    queueIndex = 2;

    this.profits = profits.clone();
    this.weights = weights.clone();
    this.quantity = quantity.clone();
    this.knapsackCapacity = knapsackCapacity;
    this.knapsackProfit = knapsackProfit;
    this.limit = limit;

    setScope(Stream.concat(Arrays.stream(quantity), Stream.of(knapsackCapacity, knapsackProfit)));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {
    do {
      store.propagationHasOccurred = false;
      singlePass(store);
    } while (store.propagationHasOccurred);
  }

  private void singlePass(Store store) {

    int n = quantity.length;
    long baseWeight = 0;
    long baseProfit = 0;
    long spanWeight = 0;
    long spanProfit = 0;
    for (int i = 0; i < n; i++) {
      baseWeight += (long) quantity[i].min() * weights[i];
      baseProfit += (long) quantity[i].min() * profits[i];
      spanWeight += (long) (quantity[i].max() - quantity[i].min()) * weights[i];
      spanProfit += (long) (quantity[i].max() - quantity[i].min()) * profits[i];
    }

    long capacityMax = knapsackCapacity.max() - baseWeight;
    if (capacityMax < 0 || knapsackCapacity.min() - baseWeight > spanWeight) {
      throw Store.failException;
    }
    long capacity = Math.min(capacityMax, spanWeight);
    if ((n + 1) * (capacity + 1) > limit) {
      return;
    }
    int c = (int) capacity;

    long profitMin = knapsackProfit.min() - baseProfit;
    long profitMax = knapsackProfit.max() - baseProfit;

    // The maximal profit side, used against the minimal profit.
    IntervalDomain[] supportedMax = new IntervalDomain[n];
    long[] totalsMax = new long[c + 1];
    run(c, baseWeight, profitMin, false, supportedMax, totalsMax);

    // The minimal profit side, used against the maximal profit, only when it can restrict.
    IntervalDomain[] supportedMin = null;
    long[] totalsMin = null;
    if (profitMax < spanProfit) {
      supportedMin = new IntervalDomain[n];
      totalsMin = new long[c + 1];
      run(c, baseWeight, -profitMax, true, supportedMin, totalsMin);
    }

    long bestProfit = UNREACHABLE;
    long worstProfit = Long.MAX_VALUE;
    IntervalDomain capacities = new IntervalDomain();
    for (int x = 0; x <= c; x++) {
      long best = totalsMax[x];
      if (best == UNREACHABLE
          || best < profitMin
          || !knapsackCapacity.domain.contains((int) (baseWeight + x))) {
        continue;
      }
      long worst = totalsMin == null ? 0 : -totalsMin[x];
      if (totalsMin != null && (totalsMin[x] == UNREACHABLE || worst > profitMax)) {
        continue;
      }
      capacities.unionAdapt((int) (baseWeight + x), (int) (baseWeight + x));
      bestProfit = Math.max(bestProfit, best);
      worstProfit = Math.min(worstProfit, totalsMin == null ? 0 : worst);
    }
    if (capacities.isEmpty()) {
      throw Store.failException;
    }

    knapsackCapacity.domain.in(store.level, knapsackCapacity, capacities);
    knapsackProfit.domain.in(
        store.level,
        knapsackProfit,
        Constraint.long2int(baseProfit + Math.max(0, worstProfit)),
        Constraint.long2int(baseProfit + bestProfit));

    for (int i = 0; i < n; i++) {
      IntervalDomain supported = supportedMax[i];
      if (supportedMin != null) {
        supported = (IntervalDomain) supported.intersect(supportedMin[i]);
      }
      quantity[i].domain.in(store.level, quantity[i], supported);
    }
  }

  /**
   * It runs the dynamic program for the maximal profit (or, with negated profits, for the minimal
   * profit).
   *
   * @param c the remaining capacity.
   * @param baseWeight the weight of the minimal quantities.
   * @param threshold the profit (relative to the minimal quantities) that must be reached.
   * @param negate true to minimize the profit.
   * @param supported the supported values of each quantity, filled by this method.
   * @param totals the best profit for each used capacity over all items, filled by this method.
   */
  private void run(
      int c,
      long baseWeight,
      long threshold,
      boolean negate,
      IntervalDomain[] supported,
      long[] totals) {

    int n = quantity.length;
    if (forward == null || forward.length < n + 1 || forward[0].length < c + 1) {
      forward = new long[n + 1][c + 1];
    }

    long[] first = forward[0];
    Arrays.fill(first, 0, c + 1, UNREACHABLE);
    first[0] = 0;
    for (int i = 0; i < n; i++) {
      long[] from = forward[i];
      long[] to = forward[i + 1];
      Arrays.fill(to, 0, c + 1, UNREACHABLE);
      int min = quantity[i].min();
      int profit = negate ? -profits[i] : profits[i];
      for (ValueEnumeration e = quantity[i].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int units = e.nextElement() - min;
        long dw = (long) units * weights[i];
        if (dw > c) {
          continue;
        }
        long dp = (long) units * profit;
        for (int x = 0; x + dw <= c; x++) {
          if (from[x] != UNREACHABLE && from[x] + dp > to[x + (int) dw]) {
            to[x + (int) dw] = from[x] + dp;
          }
        }
      }
    }
    System.arraycopy(forward[n], 0, totals, 0, c + 1);

    long[] backward = new long[c + 1];
    for (int x = 0; x <= c; x++) {
      backward[x] = knapsackCapacity.domain.contains((int) (baseWeight + x)) ? 0 : UNREACHABLE;
    }
    long[] next = new long[c + 1];
    for (int i = n - 1; i >= 0; i--) {
      long[] before = forward[i];
      Arrays.fill(next, 0, c + 1, UNREACHABLE);
      IntervalDomain values = new IntervalDomain();
      int min = quantity[i].min();
      int profit = negate ? -profits[i] : profits[i];
      for (ValueEnumeration e = quantity[i].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int value = e.nextElement();
        long dw = (long) (value - min) * weights[i];
        if (dw > c) {
          continue;
        }
        long dp = (long) (value - min) * profit;
        boolean support = false;
        for (int x = 0; x + dw <= c; x++) {
          long after = backward[x + (int) dw];
          if (after == UNREACHABLE) {
            continue;
          }
          if (after + dp > next[x]) {
            next[x] = after + dp;
          }
          if (!support && before[x] != UNREACHABLE && before[x] + dp + after >= threshold) {
            support = true;
          }
        }
        if (support) {
          values.unionAdapt(value, value);
        }
      }
      supported[i] = values;
      long[] swap = backward;
      backward = next;
      next = swap;
    }
  }

  @Override
  public boolean satisfied() {
    long weight = 0;
    long profit = 0;
    for (int i = 0; i < quantity.length; i++) {
      if (!quantity[i].singleton()) {
        return false;
      }
      weight += (long) quantity[i].value() * weights[i];
      profit += (long) quantity[i].value() * profits[i];
    }
    return knapsackCapacity.singleton(Constraint.long2int(weight))
        && knapsackProfit.singleton(Constraint.long2int(profit));
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder();
    result.append(id()).append(" : KnapsackDP([");
    for (int i = 0; i < quantity.length; i++) {
      result.append(quantity[i]).append('*').append(weights[i]).append('/').append(profits[i]);
      if (i < quantity.length - 1) {
        result.append(", ");
      }
    }
    result.append("], Capacity: ").append(knapsackCapacity);
    result.append(", Profit: ").append(knapsackProfit).append(')');
    return result.toString();
  }
}
