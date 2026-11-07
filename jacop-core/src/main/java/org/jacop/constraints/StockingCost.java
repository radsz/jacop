/*
 * StockingCost.java
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
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * StockingCost constraint for lot sizing (Houndji, Schaus, Wolsey and Deville, "The StockingCost
 * Constraint", CP 2014, and "The item dependent stockingcost constraint", Constraints 24, 2019).
 * Order i is produced in period x[i], at the latest on its due date d[i]; at most c orders are
 * produced in the same period; and the stocking cost sum(i) h[i] * (d[i] - x[i]) is at most cost.
 *
 * <p>Posting x[i] &le; d[i], a gcc and the cost sum apart assumes that every order can be produced
 * on its due date. This constraint bounds the cost by the optimum of the relaxation that keeps the
 * capacity and the upper bounds of x and drops their lower bounds, found greedily from the latest
 * period down: each period takes the orders with the largest h among those due by then. Orders
 * already produced keep their period and use its capacity. The minimum of x[i] is raised to the
 * first period at which producing order i keeps that optimum within the maximum of cost. With equal
 * costs h this is exact (bounds consistency on the relaxation, Observation 5 of the CP 2014 paper):
 * moving i down to period v loses the period of i and shifts the orders of the full periods just
 * below v. With item dependent costs it uses the lower bound of the 2019 paper, with the gain of
 * the other orders bounded by the largest of their h times the periods they can move up.
 *
 * <p>The constraint enforces the capacity only for the orders already produced and through the
 * cost; post a gcc (an alldifferent when c is 1) for the capacity of the other periods. The cost is
 * an upper bound, as in the papers; post the sum as well when it must be equal.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class StockingCost extends Constraint implements SatisfiedPresent, Copyable<StockingCost> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] x;
  final int[] due;
  final int[] h;
  final IntVar cost;
  final int capacity;

  private final int n;

  // free orders sorted by decreasing maximum, and the sort keys
  private final int[] order;
  private final long[] key;
  private int free;

  // produced orders by increasing period, and their count per distinct period
  private final int[] fixedPeriod;
  private final int[] fixedCount;
  private int fixedPeriods;

  // the periods visited by the greedy, from the latest down
  private final long[] period;
  private final int[] used;
  private final int[] room;
  private final boolean[] drained;
  private final int[] lost;
  private int periods;

  // full periods in increasing order, and the top of the run of consecutive full periods of each
  private final long[] full;
  private final long[] runTop;
  private int fulls;

  // per order: index of its due period in the greedy, its period, and the heap of waiting orders
  private final int[] entry;
  private final long[] slot;
  private final int[] heap;

  // per position in order: the largest h before it and the order holding it, and the second one
  private final int[] best;
  private final int[] bestOrder;
  private final int[] second;

  /**
   * It constructs a StockingCost constraint with a unit cost per order and period.
   *
   * @param x the production period of each order.
   * @param due the due date of each order.
   * @param cost the bound on the number of periods between production and due dates.
   * @param capacity the number of orders that a period can produce.
   */
  public StockingCost(IntVar[] x, int[] due, IntVar cost, int capacity) {
    this(x, due, unit(x), cost, capacity);
  }

  /**
   * It constructs an item dependent StockingCost constraint.
   *
   * @param x the production period of each order.
   * @param due the due date of each order.
   * @param h the stocking cost of each order per period, at least 0.
   * @param cost the bound on the total stocking cost.
   * @param capacity the number of orders that a period can produce.
   */
  public StockingCost(IntVar[] x, int[] due, int[] h, IntVar cost, int capacity) {

    if (x == null || due == null || h == null || due.length != x.length || h.length != x.length) {
      throw new IllegalArgumentException("StockingCost needs one due date and one cost per order.");
    }
    checkInputForNullness(new String[] {"x", "cost"}, x, new Object[] {cost});
    if (capacity < 1) {
      throw new IllegalArgumentException("StockingCost needs a capacity of at least 1.");
    }
    for (int v : h) {
      if (v < 0) {
        throw new IllegalArgumentException("StockingCost needs stocking costs of at least 0.");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.x = Arrays.copyOf(x, x.length);
    this.due = Arrays.copyOf(due, due.length);
    this.h = Arrays.copyOf(h, h.length);
    this.cost = cost;
    this.capacity = capacity;
    this.n = x.length;

    this.order = new int[n];
    this.key = new long[n];
    this.fixedPeriod = new int[n];
    this.fixedCount = new int[n];
    this.period = new long[2 * n];
    this.used = new int[2 * n];
    this.room = new int[2 * n];
    this.drained = new boolean[2 * n];
    this.lost = new int[2 * n];
    this.full = new long[3 * n];
    this.runTop = new long[3 * n];
    this.entry = new int[n];
    this.slot = new long[n];
    this.heap = new int[n];
    this.best = new int[n];
    this.bestOrder = new int[n];
    this.second = new int[n];

    this.queueIndex = 2;

    setScope(Stream.concat(Arrays.stream(x), Stream.of(cost)));
  }

  private static int[] unit(IntVar[] x) {
    int[] h = new int[x == null ? 0 : x.length];
    Arrays.fill(h, 1);
    return h;
  }

  @Override
  public void consistency(Store store) {

    for (int i = 0; i < n; i++) {
      if (x[i].max() > due[i]) {
        x[i].domain.inMax(store.level, x[i], due[i]);
      }
    }

    do {
      store.propagationHasOccurred = false;

      long fixedCost = collectFixed();
      if (avoidFullPeriods(store)) {
        // maxima changed, so the order is sorted again
        continue;
      }
      long optimum = fixedCost + greedy();
      if (optimum > IntDomain.MAX_INT) {
        throw Store.failException;
      }
      if (optimum > cost.min()) {
        cost.domain.inMin(store.level, cost, (int) optimum);
      }
      long slack = cost.max() - optimum;

      int uniform = uniformCost();
      if (uniform > 0) {
        fullPeriods();
      } else {
        prefixBest();
      }
      for (int k = 0; k < free; k++) {
        int i = order[k];
        if (h[i] == 0) {
          continue;
        }
        long least;
        if (uniform > 0) {
          // H(x[i] = v) = optimum + h * (lost period - last period below v that is not full)
          long lostPeriod = period[lost[entry[i]]];
          least = Math.min(lostPeriod, notFullFrom(lostPeriod - slack / uniform));
        } else {
          least = slot[i] - (slack + gain(i)) / h[i];
        }
        if (least > x[i].min()) {
          x[i].domain.inMin(store.level, x[i], (int) least);
        }
      }

    } while (store.propagationHasOccurred);
  }

  /**
   * It sorts the produced orders by period and the others by decreasing maximum.
   *
   * @return the stocking cost of the produced orders.
   */
  private long collectFixed() {
    long fixedCost = 0;
    int fixedOrders = 0;
    free = 0;
    for (int i = 0; i < n; i++) {
      if (x[i].singleton()) {
        fixedPeriod[fixedOrders++] = x[i].value();
        fixedCost += (long) h[i] * (due[i] - x[i].value());
      } else {
        key[free++] = ((long) x[i].max() << 32) | i;
      }
    }
    Arrays.sort(key, 0, free);
    for (int k = 0; k < free; k++) {
      order[k] = (int) key[free - 1 - k];
    }

    Arrays.sort(fixedPeriod, 0, fixedOrders);
    fixedPeriods = 0;
    for (int k = 0; k < fixedOrders; k++) {
      if (fixedPeriods > 0 && fixedPeriod[fixedPeriods - 1] == fixedPeriod[k]) {
        fixedCount[fixedPeriods - 1]++;
      } else {
        fixedPeriod[fixedPeriods] = fixedPeriod[k];
        fixedCount[fixedPeriods++] = 1;
      }
      if (fixedCount[fixedPeriods - 1] > capacity) {
        throw Store.failException;
      }
    }
    return fixedCost;
  }

  /**
   * It moves the bounds of the free orders out of the periods that produced orders fill up.
   *
   * @return true if a bound changed.
   */
  private boolean avoidFullPeriods(Store store) {
    if (fixedPeriods == 0) {
      return false;
    }
    boolean changed = false;
    for (int k = 0; k < free; k++) {
      IntVar v = x[order[k]];
      while (filled(v.min())) {
        v.domain.inMin(store.level, v, v.min() + 1);
        changed = true;
      }
      while (filled(v.max())) {
        v.domain.inMax(store.level, v, v.max() - 1);
        changed = true;
      }
    }
    return changed;
  }

  private boolean filled(int t) {
    int k = Arrays.binarySearch(fixedPeriod, 0, fixedPeriods, t);
    return k >= 0 && fixedCount[k] == capacity;
  }

  /**
   * It produces the free orders greedily from the latest period down, each period taking the orders
   * with the largest h that are due by then, in the capacity left by the produced orders.
   *
   * @return the stocking cost of the free orders.
   */
  private long greedy() {
    long total = 0;
    periods = 0;
    int waiting = 0;
    int next = 0;
    // the produced orders are scanned from the latest period down
    int fixedIndex = fixedPeriods - 1;
    long t = Long.MAX_VALUE;
    while (next < free || waiting > 0) {
      if (waiting == 0) {
        t = x[order[next]].max();
      }
      while (next < free && x[order[next]].max() == t) {
        int i = order[next++];
        entry[i] = periods;
        push(waiting++, i);
      }
      while (fixedIndex >= 0 && fixedPeriod[fixedIndex] > t) {
        fixedIndex--;
      }
      int left =
          capacity - (fixedIndex >= 0 && fixedPeriod[fixedIndex] == t ? fixedCount[fixedIndex] : 0);
      int produced = Math.min(left, waiting);
      for (int p = 0; p < produced; p++) {
        int i = pop(waiting--);
        slot[i] = t;
        total += h[i] * (due[i] - t);
      }
      period[periods] = t;
      used[periods] = produced;
      room[periods] = left;
      drained[periods] = waiting == 0;
      periods++;
      t--;
    }
    // the period lost when an order due at index j is removed: the first one below without carry
    for (int j = periods - 1; j >= 0; j--) {
      lost[j] = drained[j] ? j : lost[j + 1];
    }
    return total;
  }

  /**
   * It returns h when all free orders have the same positive cost h, 0 otherwise. An order without
   * cost could move down for free in place of a costly one, so it makes the costs differ too.
   */
  private int uniformCost() {
    int common = free > 0 ? h[order[0]] : 0;
    for (int k = 1; k < free && common > 0; k++) {
      if (h[order[k]] != common) {
        return 0;
      }
    }
    return common;
  }

  /**
   * It lists the full periods: those the greedy filled up and those the produced orders fill up.
   */
  private void fullPeriods() {
    fulls = 0;
    for (int j = 0; j < periods; j++) {
      if (used[j] == room[j]) {
        full[fulls++] = period[j];
      }
    }
    for (int f = 0; f < fixedPeriods; f++) {
      if (fixedCount[f] == capacity) {
        full[fulls++] = fixedPeriod[f];
      }
    }
    Arrays.sort(full, 0, fulls);
    int distinct = 0;
    for (int k = 0; k < fulls; k++) {
      if (distinct == 0 || full[distinct - 1] != full[k]) {
        full[distinct++] = full[k];
      }
    }
    fulls = distinct;
    for (int k = fulls - 1; k >= 0; k--) {
      runTop[k] = k + 1 < fulls && full[k + 1] == full[k] + 1 ? runTop[k + 1] : full[k];
    }
  }

  /** It returns the first period at or above t that is not full. */
  private long notFullFrom(long t) {
    int k = Arrays.binarySearch(full, 0, fulls, t);
    return k < 0 ? t : runTop[k] + 1;
  }

  /**
   * It bounds the decrease in the cost of the other orders when order i, at position k of order, is
   * moved away from its period: one period of theirs moves up to the period of i, and the order in
   * it is due at least then.
   */
  private long gain(int i) {
    long up = slot[i] - period[lost[entry[i]]];
    if (up == 0) {
      return 0;
    }
    // orders due at the period of i or later are a prefix of order
    int lo = 0;
    int hi = free;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (x[order[mid]].max() >= slot[i]) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    if (lo == 0) {
      return 0;
    }
    int largest = bestOrder[lo - 1] == i ? second[lo - 1] : best[lo - 1];
    return largest * up;
  }

  private void prefixBest() {
    int b = -1;
    int bo = -1;
    int s = 0;
    for (int k = 0; k < free; k++) {
      int c = h[order[k]];
      if (c > b) {
        s = Math.max(b, 0);
        b = c;
        bo = order[k];
      } else if (c > s) {
        s = c;
      }
      best[k] = b;
      bestOrder[k] = bo;
      second[k] = s;
    }
  }

  // binary max-heap of waiting orders by h
  private void push(int size, int i) {
    int c = size;
    while (c > 0) {
      int p = (c - 1) >>> 1;
      if (h[heap[p]] >= h[i]) {
        break;
      }
      heap[c] = heap[p];
      c = p;
    }
    heap[c] = i;
  }

  private int pop(int size) {
    int top = heap[0];
    int last = heap[size - 1];
    int c = 0;
    int m = size - 1;
    while (true) {
      int l = 2 * c + 1;
      if (l >= m) {
        break;
      }
      int r = l + 1;
      int larger = r < m && h[heap[r]] > h[heap[l]] ? r : l;
      if (h[heap[larger]] <= h[last]) {
        break;
      }
      heap[c] = heap[larger];
      c = larger;
    }
    heap[c] = last;
    return top;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    long total = 0;
    int[] values = new int[n];
    for (int i = 0; i < n; i++) {
      if (!x[i].singleton()) {
        return false;
      }
      values[i] = x[i].value();
      if (values[i] > due[i]) {
        return false;
      }
      total += (long) h[i] * (due[i] - values[i]);
    }
    Arrays.sort(values);
    for (int i = capacity; i < n; i++) {
      if (values[i] == values[i - capacity]) {
        return false;
      }
    }
    return total <= cost.min();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : StockingCost([");
    for (int i = 0; i < n; i++) {
      result.append(x[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(Arrays.toString(due));
    result.append(", ").append(Arrays.toString(h));
    result.append(", ").append(cost);
    result.append(", ").append(capacity).append(")");

    return result.toString();
  }

  @Override
  public StockingCost copy(VarMap map) {
    return new StockingCost(map.get(x), due, h, map.get(cost), capacity);
  }
}
