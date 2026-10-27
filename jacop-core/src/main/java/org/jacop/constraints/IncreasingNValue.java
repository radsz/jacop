/*
 * IncreasingNValue.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * IncreasingNValue constraint: x[0] &le; x[1] &le; ... &le; x[n-1] and x takes exactly count
 * distinct values (Beldiceanu, Hermenier, Lorca and Petit, "The Increasing Nvalue Constraint",
 * CPAIOR 2010).
 *
 * <p>Posted apart, Increasing and Values miss the interaction: for x0 and x1 in 1..2 and x2 = 2
 * with two distinct values neither of them prunes anything, while together they give x0 = 1. For an
 * ordered x the number of distinct values is one plus the number of strict steps, so it decomposes
 * along the sequence. For each value v of x[i] the constraint computes the fewest and the most
 * distinct values of x[i..n-1] with x[i] = v, and the same for x[0..i]; every count in between is
 * reached, so v is supported when the interval of counts of whole sequences through x[i] = v meets
 * the domain of count. This is domain consistency in time linear in the total size of the domains
 * of x. When the domains together hold more than {@link #VALUE_LIMIT} values, only the order and
 * the bounds 1..n of count are propagated until they shrink.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class IncreasingNValue extends Constraint
    implements SatisfiedPresent, Copyable<IncreasingNValue> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] x;
  final IntVar count;
  private final int n;

  // for x[i], its values and the fewest and most distinct values of x[i..n-1] (suffix) and of
  // x[0..i] (prefix) with x[i] taking the value
  private final int[][] values;
  private final int[][] sufMin;
  private final int[][] sufMax;
  private final int[][] preMin;
  private final int[][] preMax;
  private final int[] size;

  // best counts over the values of a neighbour above (or below) a position
  private int[] bestMin = new int[0];
  private int[] bestMax = new int[0];

  private static final int NONE = Integer.MAX_VALUE / 4;

  /** The largest total size of the domains of x for which values are filtered one by one. */
  public static final long VALUE_LIMIT = 1L << 20;

  /**
   * It constructs an increasing nvalue constraint.
   *
   * @param x variables which must be in non-decreasing order.
   * @param count the number of distinct values of x.
   */
  public IncreasingNValue(IntVar[] x, IntVar count) {

    checkInputForNullness(new String[] {"x", "count"}, new Object[][] {x, {count}});
    if (x.length == 0) {
      throw new IllegalArgumentException("IncreasingNValue needs at least one variable");
    }

    this.numberId = idNumber.incrementAndGet();
    this.x = Arrays.copyOf(x, x.length);
    this.count = count;
    this.n = x.length;
    this.values = new int[n][];
    this.sufMin = new int[n][];
    this.sufMax = new int[n][];
    this.preMin = new int[n][];
    this.preMax = new int[n][];
    this.size = new int[n];

    this.queueIndex = 1;

    setScope(Stream.concat(Arrays.stream(x), Stream.of(count)));
  }

  @Override
  public void consistency(Store store) {

    count.domain.in(store.level, count, 1, n);

    // the order: lower bounds forward, upper bounds backward; this is domain consistency for it
    for (int i = 1; i < n; i++) {
      int lb = x[i - 1].min();
      if (x[i].min() < lb) {
        x[i].domain.inMin(store.level, x[i], lb);
      }
    }
    for (int i = n - 1; i > 0; i--) {
      int ub = x[i].max();
      if (x[i - 1].max() > ub) {
        x[i - 1].domain.inMax(store.level, x[i - 1], ub);
      }
    }

    long total = 0;
    for (int i = 0; i < n; i++) {
      total += x[i].getSize();
    }
    if (total > VALUE_LIMIT) {
      return;
    }
    for (int i = 0; i < n; i++) {
      load(i);
    }

    // suffix counts, backward: x[i] = v continues with x[i+1] = v or with a larger value
    Arrays.fill(sufMin[n - 1], 0, size[n - 1], 1);
    Arrays.fill(sufMax[n - 1], 0, size[n - 1], 1);
    for (int i = n - 2; i >= 0; i--) {
      int[] next = values[i + 1];
      int m = size[i + 1];
      reserve(m + 1);
      // best counts over the values of x[i+1] from index j up
      bestMin[m] = NONE;
      bestMax[m] = -NONE;
      for (int j = m - 1; j >= 0; j--) {
        bestMin[j] = Math.min(bestMin[j + 1], sufMin[i + 1][j]);
        bestMax[j] = Math.max(bestMax[j + 1], sufMax[i + 1][j]);
      }
      int j = 0;
      for (int k = 0; k < size[i]; k++) {
        int v = values[i][k];
        while (j < m && next[j] < v) {
          j++;
        }
        boolean same = j < m && next[j] == v;
        int above = same ? j + 1 : j;
        int lo = bestMin[above] + 1;
        int hi = bestMax[above] + 1;
        if (same) {
          lo = Math.min(lo, sufMin[i + 1][j]);
          hi = Math.max(hi, sufMax[i + 1][j]);
        }
        sufMin[i][k] = lo;
        sufMax[i][k] = hi;
      }
    }

    // prefix counts, forward: x[i] = v follows x[i-1] = v or a smaller value
    Arrays.fill(preMin[0], 0, size[0], 1);
    Arrays.fill(preMax[0], 0, size[0], 1);
    for (int i = 1; i < n; i++) {
      int[] prev = values[i - 1];
      int m = size[i - 1];
      reserve(m + 1);
      // best counts over the values of x[i-1] below index j
      bestMin[0] = NONE;
      bestMax[0] = -NONE;
      for (int j = 0; j < m; j++) {
        bestMin[j + 1] = Math.min(bestMin[j], preMin[i - 1][j]);
        bestMax[j + 1] = Math.max(bestMax[j], preMax[i - 1][j]);
      }
      int j = 0;
      for (int k = 0; k < size[i]; k++) {
        int v = values[i][k];
        while (j < m && prev[j] < v) {
          j++;
        }
        int lo = bestMin[j] + 1;
        int hi = bestMax[j] + 1;
        if (j < m && prev[j] == v) {
          lo = Math.min(lo, preMin[i - 1][j]);
          hi = Math.max(hi, preMax[i - 1][j]);
        }
        preMin[i][k] = lo;
        preMax[i][k] = hi;
      }
    }

    // the counts of whole sequences
    IntervalDomain counts = new IntervalDomain();
    for (int k = 0; k < size[0]; k++) {
      if (sufMin[0][k] <= sufMax[0][k]) {
        counts.unionAdapt(sufMin[0][k], sufMax[0][k]);
      }
    }
    if (counts.isEmpty()) {
      throw Store.failException;
    }
    count.domain.in(store.level, count, counts);

    IntDomain allowed = count.dom();
    for (int i = 0; i < n; i++) {
      prune(store, i, allowed);
    }
  }

  // the values of x[i] in increasing order
  private void load(int i) {
    IntDomain d = x[i].dom();
    int s = d.getSize();
    if (values[i] == null || values[i].length < s) {
      int capacity = Math.max(s, values[i] == null ? 0 : 2 * values[i].length);
      values[i] = new int[capacity];
      sufMin[i] = new int[capacity];
      sufMax[i] = new int[capacity];
      preMin[i] = new int[capacity];
      preMax[i] = new int[capacity];
    }
    int k = 0;
    for (int r = 0; r < d.noIntervals(); r++) {
      int right = d.rightElement(r);
      for (int v = d.leftElement(r); v <= right; v++) {
        values[i][k++] = v;
        if (v == right) {
          break;
        }
      }
    }
    size[i] = k;
  }

  private void reserve(int capacity) {
    if (bestMin.length < capacity) {
      bestMin = new int[Math.max(capacity, 2 * bestMin.length)];
      bestMax = new int[bestMin.length];
    }
  }

  // keeps the values of x[i] through which a whole sequence has a count in allowed
  private void prune(Store store, int i, IntDomain allowed) {
    int first = 0;
    while (first < size[i] && supported(i, first, allowed)) {
      first++;
    }
    if (first == size[i]) {
      return;
    }
    // runs of consecutive kept values become one interval each
    IntervalDomain kept = new IntervalDomain();
    int start = 0;
    int end = -1;
    for (int k = 0; k < size[i]; k++) {
      if (k < first || k > first && supported(i, k, allowed)) {
        int v = values[i][k];
        if (end >= start && v == values[i][end] + 1) {
          end = k;
          continue;
        }
        if (end >= start) {
          kept.unionAdapt(values[i][start], values[i][end]);
        }
        start = k;
        end = k;
      }
    }
    if (end >= start) {
      kept.unionAdapt(values[i][start], values[i][end]);
    }
    if (kept.isEmpty()) {
      throw Store.failException;
    }
    x[i].domain.in(store.level, x[i], kept);
  }

  private boolean supported(int i, int k, IntDomain allowed) {
    int lo = preMin[i][k] + sufMin[i][k] - 1;
    int hi = preMax[i][k] + sufMax[i][k] - 1;
    return lo <= hi && allowed.isIntersecting(lo, hi);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    if (!count.singleton()) {
      return false;
    }
    int distinct = 1;
    for (int i = 0; i < n; i++) {
      if (!x[i].singleton()) {
        return false;
      }
      if (i > 0) {
        if (x[i].value() < x[i - 1].value()) {
          return false;
        }
        if (x[i].value() > x[i - 1].value()) {
          distinct++;
        }
      }
    }
    return distinct == count.value();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : IncreasingNValue([");

    for (int i = 0; i < n; i++) {
      result.append(x[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(count).append(")");

    return result.toString();
  }

  @Override
  public IncreasingNValue copy(VarMap map) {
    return new IncreasingNValue(map.get(x), map.get(count));
  }
}
