/*
 * AbstractBalance.java
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
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Common part of the balancing constraints {@link Deviation} and {@link Spread}: x[0] + ... +
 * x[n-1] = s and d = g(x[0]) + ... + g(x[n-1]) for a convex cost g of the distance of a * x[i] to
 * b, |a * x[i] - b| for the deviation and (a * x[i] - b)<sup>2</sup> for the spread. With a = n and
 * b = s the cost measures the distance of each x[i] to the mean s / n, scaled by n so that it is an
 * integer also when the mean is fractional.
 *
 * <p>The propagation is bounds consistent on the integer intervals of x for the relaxation d &ge;
 * g(x[0]) + ... + g(x[n-1]) with the sum: d.min is raised to the least cost of an integer
 * assignment of x within its bounds with sum s, and every bound of x[i] is the least or greatest
 * value v for which some integer assignment within the bounds with x[i] = v and sum s costs at most
 * d.max. The maximum of d is only reduced to the sum of the largest costs of each x[i]; d is equal
 * to the cost once x is fixed.
 *
 * <p>The least cost F<sub>i</sub>(v) of the assignments with x[i] = v is g(v) + G<sub>-i</sub>(s -
 * v), where G<sub>-i</sub>(t) is the least cost of the other variables with sum t. Both are convex,
 * since g is convex and the minimum of a separable convex sum over integer boxes with a fixed sum
 * is convex in the sum, so the values v with F<sub>i</sub>(v) &le; d.max form an interval around
 * the minimum of F<sub>i</sub> and binary searches find its ends. The subclasses compute G in
 * constant (deviation) or O(log n log D) (spread) time from sums prepared once per pass, so a pass
 * costs O(n log D) for the deviation and O(n log n log<sup>2</sup> D) for the spread, D the largest
 * domain width. The pass is repeated until no bound changes.
 *
 * <p>Repeated variables in x are treated as independent, which keeps the pruning correct but may
 * make it weaker.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractBalance extends Constraint implements SatisfiedPresent {

  /** The balanced variables. */
  final IntVar[] x;

  /** The fixed sum of x. */
  final int sum;

  /** The cost variable. */
  final IntVar cost;

  /** The multiplier of x[i] in the cost terms. */
  final int a;

  /** The value a * x[i] is compared with. */
  final int b;

  final int n;

  /** Bounds of x at the start of a pass. */
  final long[] lo;

  final long[] hi;

  /** Sums of lo and hi at the start of a pass. */
  long sumLo;

  long sumHi;

  AbstractBalance(IntVar[] x, int a, int b, int sum, IntVar cost) {
    checkInputForNullness(new String[] {"x", "cost"}, new Object[][] {x, {cost}});
    if (x.length == 0) {
      throw new IllegalArgumentException("Balancing constraint needs at least one variable.");
    }
    if (a <= 0) {
      throw new IllegalArgumentException("Balancing constraint needs a positive multiplier a.");
    }
    this.x = Arrays.copyOf(x, x.length);
    this.n = x.length;
    this.a = a;
    this.b = b;
    this.sum = sum;
    this.cost = cost;
    this.lo = new long[n];
    this.hi = new long[n];
    this.queueIndex = 1;
    setScope(Stream.concat(Arrays.stream(x), Stream.of(cost)));
  }

  /**
   * The cost of one term.
   *
   * @param v the value of x[i].
   * @return the cost of x[i] = v.
   */
  abstract long term(long v);

  /**
   * It prepares the sums the least costs are computed from, after lo, hi, sumLo and sumHi are set.
   */
  abstract void prepare();

  /**
   * The least cost of all variables, or of all but one, with the given sum.
   *
   * @param skip the index of the variable left out, or -1 for none.
   * @param t the sum, within the sums of the bounds of the variables counted.
   * @return the least cost of an integer assignment within the bounds with sum t.
   */
  abstract long least(int skip, long t);

  /**
   * It narrows the bounds of x before the main pass, so that the costs computed later stay small.
   * The default does nothing.
   *
   * @param store the constraint store.
   */
  void narrow(Store store) {
    // nothing by default
  }

  @Override
  public void consistency(Store store) {

    do {
      store.propagationHasOccurred = false;

      narrow(store);

      sumLo = 0;
      sumHi = 0;
      long largest = 0;
      for (int i = 0; i < n; i++) {
        lo[i] = x[i].min();
        hi[i] = x[i].max();
        sumLo += lo[i];
        sumHi += hi[i];
        largest += Math.max(term(lo[i]), term(hi[i]));
      }
      if (sum < sumLo || sum > sumHi) {
        throw Store.failException;
      }
      prepare();

      long best = least(-1, sum);
      if (best > cost.max() || largest < cost.min()) {
        throw Store.failException;
      }
      if (best > cost.min() || largest < cost.max()) {
        cost.domain.in(
            store.level,
            cost,
            (int) Math.max(best, cost.min()),
            (int) Math.min(largest, cost.max()));
      }
      long limit = cost.max();

      for (int i = 0; i < n; i++) {
        // x[i] = v leaves s - v to the others, within the sums of their bounds
        long from = Math.max(lo[i], sum - (sumHi - hi[i]));
        long to = Math.min(hi[i], sum - (sumLo - lo[i]));

        // the least v whose cost does not decrease towards v + 1 minimizes the convex F
        long l = from;
        long h = to;
        while (l < h) {
          long m = l + (h - l) / 2;
          if (cost(i, m + 1) >= cost(i, m)) {
            h = m;
          } else {
            l = m + 1;
          }
        }
        long centre = l;

        // largest v in [centre, to] with F(v) <= limit
        l = centre;
        h = to;
        while (l < h) {
          long m = h - (h - l) / 2;
          if (cost(i, m) <= limit) {
            l = m;
          } else {
            h = m - 1;
          }
        }
        long max = l;

        // smallest v in [from, centre] with F(v) <= limit
        l = from;
        h = centre;
        while (l < h) {
          long m = l + (h - l) / 2;
          if (cost(i, m) <= limit) {
            h = m;
          } else {
            l = m + 1;
          }
        }
        long min = l;

        if (min > lo[i] || max < hi[i]) {
          x[i].domain.in(store.level, x[i], (int) min, (int) max);
        }
      }

    } while (store.propagationHasOccurred);
  }

  // least cost with x[i] = v
  private long cost(int i, long v) {
    return term(v) + least(i, sum - v);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton()) {
      return false;
    }
    long total = 0;
    long value = 0;
    for (int i = 0; i < n; i++) {
      if (!x[i].singleton()) {
        return false;
      }
      total += x[i].value();
      value += term(x[i].value());
    }
    return total == sum && value == cost.value();
  }

  String describe() {
    StringBuilder result = new StringBuilder("([");
    for (int i = 0; i < n; i++) {
      result.append(x[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], a = ").append(a).append(", b = ").append(b);
    result.append(", sum = ").append(sum).append(", ").append(cost).append(")");
    return result.toString();
  }
}
