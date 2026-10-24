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
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * A knapsack constraint, sum(weights[i] * quantity[i]) = capacity and sum(profits[i] * quantity[i])
 * = profit, propagated by dynamic programming over the used capacity, following M. Trick, "A
 * dynamic programming approach for consistency and propagation for knapsack constraints", Annals of
 * Operations Research 118 (2003).
 *
 * <p>For every item it keeps the best profit of the items before it (forward tables) and of the
 * items after it (backward tables) for every extra weight above the minimal quantities. A value of
 * a quantity is kept only if some assignment using it reaches a capacity in the capacity domain
 * with a profit of at least the minimal profit and, when the maximal profit restricts, some such
 * assignment has a profit of at most the maximal profit. This gives domain consistency for the
 * quantities with respect to the capacity domain and each profit bound, prunes values of the
 * capacity, and bounds the profit.
 *
 * <p>The propagation is incremental. The tables do not depend on the capacity or the profit, so
 * they are kept between calls and only the layers after (forward) or before (backward) a changed
 * item are recomputed. Fixed items cost nothing, and every supported value remembers its support,
 * so it is checked again in constant time.
 *
 * <p>A call costs at most O(n * C * d) time for n items, a remaining capacity C and quantities with
 * at most d values, and the tables take O(n * C) memory, so the constraint does nothing when n * C
 * is above a limit. {@link Knapsack} runs it by default next to its cheap relaxation (see {@link
 * Knapsack#dynamicProgramming(boolean)}), so it rarely needs to be posted on its own. By default it
 * is adaptive: every call earns a work budget proportional to the number of items (see {@link
 * #workRatio(double)}), and the tables are updated only when the budget covers the cost of the
 * previous update, so the constraint spends at most about as much work as the rest of the search
 * and costs little on instances where {@link Knapsack} alone suffices. {@link #adaptive(boolean)}
 * with false propagates at every call to a fixpoint. It always propagates when all quantities are
 * fixed, so it never accepts a wrong solution.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class KnapsackDP extends Constraint implements SatisfiedPresent {

  private static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The default limit on the number of items times the remaining capacity. */
  public static final long DEFAULT_LIMIT = 2_000_000L;

  /** The default share of the search effort the adaptive mode may spend on the tables. */
  public static final double DEFAULT_WORK_RATIO = 1.0;

  /**
   * The work, in table cells per item, one call of the constraint earns in adaptive mode. It is
   * about the cost of propagating {@link Knapsack} and exploring one search node.
   */
  static final int WORK_PER_CALL_AND_ITEM = 32;

  /** The largest profit span the tables can hold. */
  static final long MAX_PROFIT_SPAN = 1L << 28;

  /** The value of an unreachable cell. Sums with it stay below {@link #REACHABLE}. */
  static final int UNREACHABLE = -(1 << 30);

  /** Every reachable cell is above this value. */
  static final int REACHABLE = -(1 << 29);

  private final IntVar[] quantity;

  private final int[] weights;

  private final int[] profits;

  private final IntVar knapsackCapacity;

  private final IntVar knapsackProfit;

  private final long limit;

  private boolean adaptive = true;

  private double workRatio = DEFAULT_WORK_RATIO;

  /** The work, in table cells, the constraint may still spend in adaptive mode. */
  private double budget;

  /** The work, in table cells, spent so far. */
  private long work;

  /** The work of the last call which propagated, or -1 before the first one. */
  private long lastWork = -1;

  private Side maxSide;

  private Side minSide;

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

  /**
   * It decides whether the constraint skips calls after calls which prune nothing. It is on by
   * default. Without it the constraint propagates at every call.
   *
   * @param adaptive true to skip calls after calls which prune nothing.
   * @return this constraint.
   */
  public KnapsackDP adaptive(boolean adaptive) {
    this.adaptive = adaptive;
    return this;
  }

  /**
   * It sets the share of the search effort the adaptive mode may spend on the tables. With 1 the
   * tables take about as much work as the rest of the search; larger values propagate more often.
   *
   * @param workRatio the share, above 0.
   * @return this constraint.
   */
  public KnapsackDP workRatio(double workRatio) {
    if (!(workRatio > 0)) {
      throw new IllegalArgumentException("Constraint KnapsackDP requires a work ratio above 0.");
    }
    this.workRatio = workRatio;
    return this;
  }

  /**
   * It tells whether posting this constraint next to {@link Knapsack} is safe: its tables for the
   * current domains fit within the default limit. Posted in the default adaptive mode, it then
   * spends at most about as much work as the rest of the search, and pays off when the linear
   * relaxation used by {@link Knapsack} is weak, as for strongly correlated weights and profits.
   *
   * @param weights the weight of one unit of each item.
   * @param quantity the quantity of each item.
   * @param knapsackCapacity the used capacity.
   * @return true if the tables fit within {@link #DEFAULT_LIMIT}.
   */
  public static boolean fits(int[] weights, IntVar[] quantity, IntVar knapsackCapacity) {
    long base = 0;
    long span = 0;
    for (int i = 0; i < quantity.length; i++) {
      base += (long) quantity[i].min() * weights[i];
      span += (long) (quantity[i].max() - quantity[i].min()) * weights[i];
    }
    long capacity = Math.min(knapsackCapacity.max() - base, span);
    return capacity >= 0 && (quantity.length + 1) * (capacity + 1) <= DEFAULT_LIMIT;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {
    propagateIfWorthIt(store);
  }

  /**
   * It propagates to a fixpoint unless the adaptive mode skips this call.
   *
   * @param store the constraint store.
   * @return true if a domain was pruned.
   */
  boolean propagateIfWorthIt(Store store) {

    boolean allFixed = true;
    for (IntVar q : quantity) {
      if (!q.singleton()) {
        allFixed = false;
        break;
      }
    }

    if (adaptive && !allFixed) {
      budget += workRatio * WORK_PER_CALL_AND_ITEM * quantity.length;
      if (budget < (lastWork < 0 ? fullWork() : lastWork)) {
        return false;
      }
    }

    return propagate(store);
  }

  private boolean propagate(Store store) {
    long before = work;
    boolean pruned = false;
    do {
      store.propagationHasOccurred = false;
      singlePass(store);
      pruned |= store.propagationHasOccurred;
    } while (store.propagationHasOccurred);
    lastWork = work - before;
    budget -= lastWork;
    return pruned;
  }

  /** It estimates the work of computing all the tables, for the first call. */
  private long fullWork() {
    long base = 0;
    long span = 0;
    long values = 0;
    for (int i = 0; i < quantity.length; i++) {
      base += (long) quantity[i].min() * weights[i];
      span += (long) (quantity[i].max() - quantity[i].min()) * weights[i];
      values += quantity[i].getSize() + 2;
    }
    long capacity = Math.max(0, Math.min(knapsackCapacity.max() - base, span));
    return 2 * values * (capacity + 1);
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
    if ((n + 1) * (capacity + 1) > limit || spanProfit > MAX_PROFIT_SPAN) {
      return;
    }
    int c = (int) capacity;

    long profitMin = knapsackProfit.min() - baseProfit;
    long profitMax = knapsackProfit.max() - baseProfit;

    if (maxSide == null) {
      maxSide = new Side(false);
    }
    maxSide.updateForward(c);

    // The capacities reachable with enough profit, and the best profit.
    int[] last = maxSide.forward[n];
    IntervalDomain capacities = new IntervalDomain();
    long bestProfit = Long.MIN_VALUE;
    for (int x = 0; x <= c; x++) {
      if (last[x] > REACHABLE
          && last[x] >= profitMin
          && knapsackCapacity.domain.contains((int) (baseWeight + x))) {
        capacities.unionAdapt((int) (baseWeight + x), (int) (baseWeight + x));
        bestProfit = Math.max(bestProfit, last[x]);
      }
    }
    if (capacities.isEmpty()) {
      throw Store.failException;
    }

    // The minimal profit side bounds the profit from below and, when the maximal profit restricts,
    // prunes the capacity. It prunes the quantities only when some assignment can exceed the
    // maximal profit.
    boolean useMin = adaptive ? profitMax < bestProfit : profitMax < spanProfit;
    long worstProfit = 0;
    if (useMin) {
      if (minSide == null) {
        minSide = new Side(true);
      }
      minSide.updateForward(c);
      int[] lowest = minSide.forward[n];
      IntervalDomain both = new IntervalDomain();
      bestProfit = Long.MIN_VALUE;
      worstProfit = Long.MAX_VALUE;
      for (int x = 0; x <= c; x++) {
        if (capacities.contains((int) (baseWeight + x))
            && lowest[x] > REACHABLE
            && -lowest[x] <= profitMax) {
          both.unionAdapt((int) (baseWeight + x), (int) (baseWeight + x));
          bestProfit = Math.max(bestProfit, last[x]);
          worstProfit = Math.min(worstProfit, -lowest[x]);
        }
      }
      if (both.isEmpty()) {
        throw Store.failException;
      }
      capacities = both;
      useMin = profitMax < bestProfit;
    }

    knapsackCapacity.domain.in(store.level, knapsackCapacity, capacities);
    knapsackProfit.domain.in(
        store.level,
        knapsackProfit,
        Constraint.long2int(baseProfit + Math.max(0, worstProfit)),
        Constraint.long2int(baseProfit + bestProfit));

    // The supports are checked against the pruned capacity domain.
    maxSide.updateBackward(c);
    if (useMin) {
      minSide.updateBackward(c);
    }
    Window window = new Window(knapsackCapacity.dom(), baseWeight, c);
    for (int i = 0; i < n; i++) {
      if (quantity[i].singleton()) {
        continue;
      }
      IntervalDomain supported = maxSide.supported(i, profitMin, window, c);
      if (useMin && !supported.isEmpty()) {
        supported =
            (IntervalDomain) supported.intersect(minSide.supported(i, -profitMax, window, c));
      }
      quantity[i].domain.in(store.level, quantity[i], supported);
    }
  }

  /** The relative capacities allowed by the capacity domain, as intervals of extra weight. */
  private static final class Window {

    final int[] low;

    final int[] high;

    final IntDomain domain;

    final long base;

    Window(IntDomain domain, long base, int c) {
      this.domain = domain;
      this.base = base;
      int count = 0;
      int[] lows = new int[domain.noIntervals()];
      int[] highs = new int[lows.length];
      for (IntervalEnumeration e = domain.intervalEnumeration(); e.hasMoreElements(); ) {
        Interval interval = e.nextElement();
        long from = Math.max(0, interval.min() - base);
        long to = Math.min(c, interval.max() - base);
        if (from <= to) {
          lows[count] = (int) from;
          highs[count] = (int) to;
          count++;
        }
      }
      low = Arrays.copyOf(lows, count);
      high = Arrays.copyOf(highs, count);
    }

    boolean contains(long extra) {
      return domain.contains((int) (base + extra));
    }
  }

  /**
   * The tables for the maximal profit, or with negated profits for the minimal profit. The forward
   * table of layer k holds, for every extra weight of the items before item k, the best extra
   * profit; the backward table of layer k does the same for item k and the items after it. Extra
   * weights and profits are counted above the minimal quantities, so a layer stays valid as long as
   * the quantities it covers do not change and it covers the remaining capacity.
   */
  private final class Side {

    private final boolean negate;

    /** The tables used by each layer; a fixed item shares the table of its neighbour. */
    final int[][] forward;

    final int[][] backward;

    /** The tables owned by each layer. */
    private final int[][] forwardOwn;

    private final int[][] backwardOwn;

    /** The capacity each layer covers, or -1 if the layer must be computed. */
    private final int[] forwardCapacity;

    private final int[] backwardCapacity;

    /** The domain of the item each layer was computed with. */
    private final IntDomain[] forwardDomain;

    private final IntDomain[] backwardDomain;

    /** The last support of each value: its value, extra weight before, and extra weight after. */
    private final int[][] supportValue;

    private final int[][] supportBefore;

    private final int[][] supportAfter;

    private int[] windowBest;

    private int[] prefixMax;

    private int[] blockPrefix;

    private int[] blockSuffix;

    Side(boolean negate) {
      this.negate = negate;
      int n = quantity.length;
      forward = new int[n + 1][];
      backward = new int[n + 1][];
      forwardOwn = new int[n + 1][];
      backwardOwn = new int[n + 1][];
      forwardCapacity = new int[n + 1];
      backwardCapacity = new int[n + 1];
      Arrays.fill(forwardCapacity, -1);
      Arrays.fill(backwardCapacity, -1);
      forwardDomain = new IntDomain[n];
      backwardDomain = new IntDomain[n];
      supportValue = new int[n][];
      supportBefore = new int[n][];
      supportAfter = new int[n][];
    }

    /**
     * It brings the forward tables up to date for the remaining capacity c, recomputing only the
     * layers after the first changed item.
     */
    void updateForward(int c) {
      int n = quantity.length;

      int from = n + 1;
      if (forwardCapacity[0] < c) {
        from = 0;
      } else {
        for (int k = 1; k <= n; k++) {
          if (forwardCapacity[k] < c || !forwardDomain[k - 1].eq(quantity[k - 1].dom())) {
            from = k;
            break;
          }
        }
      }
      if (from == 0) {
        int[] first = own(forwardOwn, 0, c);
        Arrays.fill(first, 0, c + 1, UNREACHABLE);
        first[0] = 0;
        forward[0] = first;
        forwardCapacity[0] = c;
        from = 1;
      }
      for (int k = from; k <= n; k++) {
        int item = k - 1;
        forward[k] = layer(forwardOwn, k, forward[k - 1], item, c);
        forwardCapacity[k] = c;
        forwardDomain[item] = quantity[item].dom().cloneLight();
      }
    }

    /** It brings the backward tables up to date, as {@link #updateForward} does. */
    void updateBackward(int c) {
      int n = quantity.length;
      int to = -1;
      if (backwardCapacity[n] < c) {
        to = n;
      } else {
        for (int k = n - 1; k >= 0; k--) {
          if (backwardCapacity[k] < c || !backwardDomain[k].eq(quantity[k].dom())) {
            to = k;
            break;
          }
        }
      }
      if (to == n) {
        int[] last = own(backwardOwn, n, c);
        Arrays.fill(last, 0, c + 1, UNREACHABLE);
        last[0] = 0;
        backward[n] = last;
        backwardCapacity[n] = c;
        to = n - 1;
      }
      for (int k = to; k >= 0; k--) {
        backward[k] = layer(backwardOwn, k, backward[k + 1], k, c);
        backwardCapacity[k] = c;
        backwardDomain[k] = quantity[k].dom().cloneLight();
      }
    }

    private int[] own(int[][] tables, int k, int c) {
      if (tables[k] == null || tables[k].length < c + 1) {
        tables[k] = new int[c + 1];
      }
      return tables[k];
    }

    /** It adds one item to the table of the previous layer. */
    private int[] layer(int[][] tables, int k, int[] previous, int item, int c) {
      IntVar q = quantity[item];
      if (q.singleton()) {
        return previous;
      }
      int[] next = own(tables, k, c);
      work += (long) (c + 1) * q.getSize();
      Arrays.fill(next, 0, c + 1, UNREACHABLE);
      int min = q.min();
      int profit = negate ? -profits[item] : profits[item];
      for (ValueEnumeration e = q.domain.valueEnumeration(); e.hasMoreElements(); ) {
        int units = e.nextElement() - min;
        long weight = (long) units * weights[item];
        if (weight > c) {
          break;
        }
        int dw = (int) weight;
        int dp = units * profit;
        for (int x = 0, y = dw; y <= c; x++, y++) {
          next[y] = Math.max(next[y], previous[x] + dp);
        }
      }
      return next;
    }

    /**
     * It returns the values of a quantity which have a support with an extra profit of at least the
     * threshold and a capacity in the window. It first checks the last support of each value.
     */
    IntervalDomain supported(int item, long threshold, Window window, int c) {
      IntVar q = quantity[item];
      int[] before = forward[item];
      int[] after = backward[item + 1];
      int min = q.min();
      int profit = negate ? -profits[item] : profits[item];

      int size = q.getSize();
      if (supportValue[item] == null || supportValue[item].length < size) {
        supportValue[item] = new int[size];
        supportBefore[item] = new int[size];
        supportAfter[item] = new int[size];
        Arrays.fill(supportBefore[item], -1);
      }
      int[] values = supportValue[item];
      int[] xs = supportBefore[item];
      int[] ts = supportAfter[item];

      IntervalDomain result = new IntervalDomain();
      boolean windowReady = false;
      int slot = 0;
      for (ValueEnumeration e = q.domain.valueEnumeration(); e.hasMoreElements(); slot++) {
        int value = e.nextElement();
        long weight = (long) (value - min) * weights[item];
        if (weight > c) {
          xs[slot] = -1;
          continue;
        }
        int dw = (int) weight;
        long dp = (long) (value - min) * profit;

        if (values[slot] == value && xs[slot] >= 0) {
          int x = xs[slot];
          int t = ts[slot];
          if (x <= c
              && t <= c
              && (long) x + dw + t <= c
              && before[x] > REACHABLE
              && after[t] > REACHABLE
              && before[x] + dp + after[t] >= threshold
              && window.contains((long) x + dw + t)) {
            result.unionAdapt(value, value);
            continue;
          }
        }

        if (!windowReady) {
          computeWindow(after, window, c);
          windowReady = true;
        }
        values[slot] = value;
        xs[slot] = -1;
        for (int x = 0, y = dw; y <= c; x++, y++) {
          int best = windowBest[y];
          if (best > REACHABLE && before[x] > REACHABLE && before[x] + dp + best >= threshold) {
            xs[slot] = x;
            ts[slot] = findAfter(after, window, y);
            result.unionAdapt(value, value);
            break;
          }
        }
      }
      return result;
    }

    /**
     * For every extra weight y used by the items up to the checked one, it computes the best extra
     * profit of the items after it such that the total extra weight is in the window. For an
     * interval [a, b] of the window and y at least a, the allowed extra weights after the item are
     * [0, b - y], a prefix maximum. For y below a they are [a - y, b - y], a sliding window of
     * fixed length, computed with the block decomposition of van Herk and Gil-Werman.
     */
    private void computeWindow(int[] after, Window window, int c) {
      if (windowBest == null || windowBest.length < c + 1) {
        windowBest = new int[c + 1];
        prefixMax = new int[c + 1];
        blockPrefix = new int[c + 1];
        blockSuffix = new int[c + 1];
      }
      Arrays.fill(windowBest, 0, c + 1, UNREACHABLE);
      work += 4L * (c + 1);
      int running = UNREACHABLE;
      for (int t = 0; t <= c; t++) {
        running = Math.max(running, after[t]);
        prefixMax[t] = running;
      }
      for (int i = 0; i < window.low.length; i++) {
        int a = window.low[i];
        int b = window.high[i];
        for (int y = a; y <= b; y++) {
          windowBest[y] = Math.max(windowBest[y], prefixMax[b - y]);
        }
        if (a == 0) {
          continue;
        }
        int length = b - a + 1;
        for (int start = 0; start <= b; start += length) {
          int end = Math.min(b, start + length - 1);
          int value = UNREACHABLE;
          for (int t = start; t <= end; t++) {
            value = Math.max(value, after[t]);
            blockPrefix[t] = value;
          }
          value = UNREACHABLE;
          for (int t = end; t >= start; t--) {
            value = Math.max(value, after[t]);
            blockSuffix[t] = value;
          }
        }
        for (int y = 0; y < a; y++) {
          int best = Math.max(blockSuffix[a - y], blockPrefix[b - y]);
          windowBest[y] = Math.max(windowBest[y], best);
        }
      }
    }

    /** It finds an extra weight after the checked item which gives the best profit for y. */
    private int findAfter(int[] after, Window window, int y) {
      for (int i = 0; i < window.low.length; i++) {
        int b = window.high[i];
        if (y > b) {
          continue;
        }
        for (int t = Math.max(0, window.low[i] - y); t <= b - y; t++) {
          if (after[t] == windowBest[y]) {
            return t;
          }
        }
      }
      throw new IllegalStateException("No extra weight gives the best profit.");
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
