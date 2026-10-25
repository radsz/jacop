/*
 * IncreasingSum.java
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
 * IncreasingSum constraint: x[0] &le; x[1] &le; ... &le; x[n-1] and x[0] + ... + x[n-1] = s (Petit,
 * R&eacute;gin and Beldiceanu, "A &Theta;(n) Bound-Consistency Algorithm for the Increasing Sum
 * Constraint", CP 2011). With the strict option the order is x[0] &lt; x[1] &lt; ... &lt; x[n-1].
 *
 * <p>Posting the two parts separately loses the interaction between them: for x = [x0, x1, x2] in
 * 0..10 with sum 6, the sum and the order posted apart only give x[i] &le; 6, while together x0
 * &le; 2 and x2 &ge; 2. This constraint reaches bounds consistency on the integer intervals of x
 * and s in time linear in n per call: the largest value of x[i] is the largest v for which keeping
 * x[0..i-1] at their minima and raising x[i..n-1] to at least v stays within the maximum of s.
 * These limits are non-decreasing in i, and so is the first index whose minimum lies above the
 * limit, so all of them are found in one sweep. The smallest values follow by symmetry.
 *
 * <p>A strict order is the non-strict one on y[i] = x[i] - i, whose sum is s - n(n-1)/2.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class IncreasingSum extends Constraint implements SatisfiedPresent, Copyable<IncreasingSum> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] x;
  final IntVar sum;
  final boolean strict;
  private final int n;
  private final int step;

  // bounds of y[i] = x[i] - i * step, and work arrays of the sweep
  private final long[] lo;
  private final long[] hi;
  private final long[] mirror;
  private final long[] limit;

  /**
   * It constructs an increasing sum constraint.
   *
   * @param x variables which must be in non-decreasing order.
   * @param sum the sum of x.
   */
  public IncreasingSum(IntVar[] x, IntVar sum) {
    this(x, sum, false);
  }

  /**
   * It constructs an increasing sum constraint.
   *
   * @param x variables which must be in increasing order.
   * @param sum the sum of x.
   * @param strict true if strictly increasing order is required, false for non-decreasing order.
   */
  public IncreasingSum(IntVar[] x, IntVar sum, boolean strict) {

    checkInputForNullness(new String[] {"x", "sum"}, new Object[][] {x, {sum}});

    this.numberId = idNumber.incrementAndGet();
    this.x = Arrays.copyOf(x, x.length);
    this.sum = sum;
    this.strict = strict;
    this.n = x.length;
    this.step = strict ? 1 : 0;
    this.lo = new long[n];
    this.hi = new long[n];
    this.mirror = new long[n];
    this.limit = new long[n];

    this.queueIndex = 1;

    setScope(Stream.concat(Arrays.stream(x), Stream.of(sum)));
  }

  @Override
  public void consistency(Store store) {

    // the order of the y's offset by sum(i * step)
    long offset = (long) step * n * (n - 1) / 2;

    do {
      store.propagationHasOccurred = false;

      // order: lower bounds forward, upper bounds backward
      for (int i = 1; i < n; i++) {
        int lb = x[i - 1].min() + step;
        if (x[i].min() < lb) {
          x[i].domain.inMin(store.level, x[i], lb);
        }
      }
      for (int i = n - 1; i > 0; i--) {
        int ub = x[i].max() - step;
        if (x[i - 1].max() > ub) {
          x[i - 1].domain.inMax(store.level, x[i - 1], ub);
        }
      }

      long sumLo = 0;
      long sumHi = 0;
      for (int i = 0; i < n; i++) {
        lo[i] = (long) x[i].min() - (long) i * step;
        hi[i] = (long) x[i].max() - (long) i * step;
        sumLo += lo[i];
        sumHi += hi[i];
      }

      // every sum between the sums of the minima and of the maxima is reached by ordered values
      if (sumLo + offset > sum.min() || sumHi + offset < sum.max()) {
        if (sumLo + offset > sum.max() || sumHi + offset < sum.min()) {
          throw Store.failException;
        }
        sum.domain.in(
            store.level,
            sum,
            (int) Math.max(sum.min(), sumLo + offset),
            (int) Math.min(sum.max(), sumHi + offset));
      }
      long smin = sum.min() - offset;
      long smax = sum.max() - offset;

      // largest values: y[i] <= limit[i] keeps the smallest sum with y[i] fixed within smax
      largest(lo, smax, limit);
      for (int i = 0; i < n; i++) {
        if (limit[i] < hi[i]) {
          if (limit[i] < lo[i]) {
            throw Store.failException;
          }
          x[i].domain.inMax(store.level, x[i], (int) (limit[i] + (long) i * step));
        }
      }

      // smallest values: the largest values of z[j] = -y[n-1-j] with sum -s
      for (int j = 0; j < n; j++) {
        mirror[j] = -hi[n - 1 - j];
      }
      largest(mirror, -smin, limit);
      for (int i = 0; i < n; i++) {
        long least = -limit[n - 1 - i];
        if (least > lo[i]) {
          if (least > hi[i]) {
            throw Store.failException;
          }
          x[i].domain.inMin(store.level, x[i], (int) (least + (long) i * step));
        }
      }

    } while (store.propagationHasOccurred);
  }

  /**
   * For non-decreasing minima min[0..n-1] whose sum is at most max, it computes for every i the
   * largest v such that min[0] + ... + min[i-1] + max(min[i], v) + ... + max(min[n-1], v) &le; max.
   *
   * <p>For a given i let k be the first index after i whose minimum cannot be reached, that is
   * f(min[k]) &gt; max for f(v) = sum over j &ge; i of max(min[j], v); then v lies below min[k] and
   * f(v) = v * (k - i) + min[k] + ... + min[n-1]. Moving from i to i + 1 makes the condition on k
   * stronger, since the budget drops by min[i] while f(min[k]) drops by min[k] &ge; min[i]; so k
   * never moves back and the sweep is linear.
   */
  private void largest(long[] min, long max, long[] result) {
    // tail = min[k] + ... + min[n-1], prefix = min[0] + ... + min[i-1]
    long tail = 0;
    for (int j = 0; j < n; j++) {
      tail += min[j];
    }
    long prefix = 0;
    int k = 0;
    for (int i = 0; i < n; i++) {
      while (k <= i) {
        tail -= min[k++];
      }
      long budget = max - prefix;
      while (k < n && min[k] * (k - i) + tail <= budget) {
        tail -= min[k++];
      }
      result[i] = Math.floorDiv(budget - tail, (long) (k - i));
      prefix += min[i];
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    if (!sum.singleton()) {
      return false;
    }
    long total = 0;
    for (int i = 0; i < n; i++) {
      if (!x[i].singleton()) {
        return false;
      }
      if (i > 0 && x[i].value() < x[i - 1].value() + step) {
        return false;
      }
      total += x[i].value();
    }
    return total == sum.value();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : IncreasingSum([");

    for (int i = 0; i < n; i++) {
      result.append(x[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(sum);
    result.append(", ").append(strict ? "strict" : "non-strict").append(")");

    return result.toString();
  }

  @Override
  public IncreasingSum copy(VarMap map) {
    return new IncreasingSum(map.get(x), map.get(sum), strict);
  }
}
