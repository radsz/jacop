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
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

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
public class IncreasingSum extends Constraint
    implements SatisfiedPresent, Copyable<IncreasingSum>, Explainable {

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

  /*
   * Explanations for lazy clause generation, on y[j] = x[j] - j * step, which is non-decreasing. A
   * bound of x[i] follows from the order and the bound of a neighbour, or from the sum: y[i] >= Y + 1
   * raises every later y to Y + 1, so the earlier minima and the later ones above Y + 1 with the
   * upper bound of the sum rule it out (and the mirror image for lower bounds). A sum bound
   * follows from all minima or all maxima. Every bound is weakened as far as the slack allows.
   */

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar v = trail.variable(entry);
    boolean ge = trail.kind(entry) == AtomicTrail.GE;
    if (trail.kind(entry) == AtomicTrail.NE) {
      return false;
    }
    // the bound the propagation needed: below the atom's value down to the holes it skipped
    long value = trail.skippedBound(entry);
    trail.addSkippedHoles(entry, (int) value, out);
    if (v == sum) {
      // sum >= value from the minima, sum <= value from the maxima
      long total = 0;
      for (int j = 0; j < n; j++) {
        total += ge ? trail.minBefore(x[j], entry) : trail.maxBefore(x[j], entry);
      }
      long room = ge ? total - value : value - total;
      if (room < 0) {
        return false;
      }
      for (int j = 0; j < n; j++) {
        room -= trail.addBoundWithin(x[j], entry, ge, room, out);
      }
      return true;
    }
    int i = indexOf(v);
    if (i < 0) {
      return false;
    }
    // the order: x[i] >= x[i-1] + step, x[i] <= x[i+1] - step
    if (ge && i > 0 && trail.minBefore(x[i - 1], entry) >= value - step) {
      trail.addBoundReaching(x[i - 1], entry, true, value - step, out);
      return true;
    }
    if (!ge && i < n - 1 && trail.maxBefore(x[i + 1], entry) <= value + step) {
      trail.addBoundReaching(x[i + 1], entry, false, value + step, out);
      return true;
    }
    return ge
        ? fromSum(trail, entry, i, value, true, out)
        : fromSum(trail, entry, i, value, false, out);
  }

  // x[i] <= value (lower = false): y[i] >= Y + 1 for Y = value - i * step would make the sum exceed
  // its maximum; x[i] >= value (lower = true) is the mirror image with the minimum of the sum
  private boolean fromSum(
      AtomicTrail trail, int entry, int i, long value, boolean lower, EntryList out) {
    long offset = (long) step * n * (n - 1) / 2;
    // in the mirror image the roles of minima and maxima, and of earlier and later, swap
    long cut = lower ? -(value - (long) i * step) + 1 : value - (long) i * step + 1;
    long[] bound = new long[n];
    long total = 0;
    for (int j = 0; j < n; j++) {
      long b =
          lower
              ? -((long) trail.maxBefore(x[j], entry) - (long) j * step)
              : (long) trail.minBefore(x[j], entry) - (long) j * step;
      bound[j] = b;
      boolean after = lower ? j < i : j > i;
      total += j == i ? cut : after ? Math.max(b, cut) : b;
    }
    long sumBound =
        lower
            ? -((long) trail.minBefore(sum, entry) - offset)
            : trail.maxBefore(sum, entry) - offset;
    long room = total - sumBound - 1;
    if (room < 0) {
      return false;
    }
    // the later bounds above the cut, cheapest to drop first; then the earlier ones; then the sum
    for (int j = 0; j < n; j++) {
      boolean after = lower ? j < i : j > i;
      if (!after || bound[j] <= cut) {
        continue;
      }
      long excess = bound[j] - cut;
      if (excess <= room) {
        room -= excess;
      } else {
        room -= trail.addBoundWithin(x[j], entry, !lower, room, out);
      }
    }
    for (int j = 0; j < n; j++) {
      boolean before = lower ? j > i : j < i;
      if (before) {
        room -= trail.addBoundWithin(x[j], entry, !lower, room, out);
      }
    }
    trail.addBoundWithin(sum, entry, lower, room, out);
    return true;
  }

  private int indexOf(IntVar v) {
    for (int j = 0; j < n; j++) {
      if (x[j] == v) {
        return j;
      }
    }
    return -1;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int now = trail.size();
    for (int i = 1; i < n; i++) {
      long lb = (long) trail.minBefore(x[i - 1], now) + step;
      if (lb > trail.maxBefore(x[i], now)) {
        trail.addLowerBound(x[i - 1], now, out);
        trail.addUpperBound(x[i], now, out);
        return true;
      }
    }
    long lo = 0;
    long hi = 0;
    for (int j = 0; j < n; j++) {
      lo += trail.minBefore(x[j], now);
      hi += trail.maxBefore(x[j], now);
    }
    if (lo > trail.maxBefore(sum, now)) {
      long room = lo - trail.maxBefore(sum, now) - 1;
      for (int j = 0; j < n; j++) {
        room -= trail.addBoundWithin(x[j], now, true, room, out);
      }
      trail.addBoundWithin(sum, now, false, room, out);
      return true;
    }
    if (hi < trail.minBefore(sum, now)) {
      long room = trail.minBefore(sum, now) - hi - 1;
      for (int j = 0; j < n; j++) {
        room -= trail.addBoundWithin(x[j], now, false, room, out);
      }
      trail.addBoundWithin(sum, now, true, room, out);
      return true;
    }
    return false;
  }

  @Override
  public IncreasingSum copy(VarMap map) {
    return new IncreasingSum(map.get(x), map.get(sum), strict);
  }
}
