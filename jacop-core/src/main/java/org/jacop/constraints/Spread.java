/*
 * Spread.java
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
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Spread constraint: x[0] + ... + x[n-1] = s and d = (a * x[0] - b)<sup>2</sup> + ... + (a * x[n-1]
 * - b)<sup>2</sup>. The default a = n and b = s give d = sum of (n * x[i] - s)<sup>2</sup>,
 * n<sup>3</sup> times the variance of x around its mean s / n: the L2 balancing constraint of
 * Pesant and R&eacute;gin ("SPREAD: A Balancing Constraint Based on Statistics", CP 2005), with
 * integer bounds consistent filtering as in Schaus and R&eacute;gin ("Bound-Consistent Spread
 * Constraint", EURO Journal on Computational Optimization, 2014). Since the sum is fixed, any a and
 * b give the same order of the assignments, so the constraint also bounds a sum of squares
 * x[0]<sup>2</sup> + ... + x[n-1]<sup>2</sup> (a = 1, b = 0).
 *
 * <p>Pruning is bounds consistent on the integer intervals of x for d &ge; spread (see {@link
 * AbstractBalance}). The least sum of squares of a set of variables with sum t raises every
 * variable to a common level &theta; within its bounds (water filling) and the remaining units to
 * &theta; + 1; with the bounds sorted, the sum at a level takes O(log n) and the level a binary
 * search. Before that each x[i] is narrowed so that its own term is at most d.max, which also keeps
 * the computed costs far from overflow.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Spread extends AbstractBalance implements Copyable<Spread> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // b = c * a + r with 0 <= r < a; the costs are computed on y = x - c, as (a * y - r)^2
  private final long c;
  private final long r;

  // bounds of y sorted, with prefix sums of the values and their squares
  private final long[] low;
  private final long[] high;
  private final long[] lowSum;
  private final long[] lowSquares;
  private final long[] highSum;
  private final long[] highSquares;

  /**
   * It constructs the spread constraint sum of x = s, d = sum of (n * x[i] - s)<sup>2</sup>.
   *
   * @param x the balanced variables.
   * @param sum the sum of x.
   * @param spread the sum of the squares of n * x[i] - s.
   */
  public Spread(IntVar[] x, int sum, IntVar spread) {
    this(x, x.length, sum, sum, spread);
  }

  /**
   * It constructs the spread constraint sum of x = s, d = sum of (a * x[i] - b)<sup>2</sup>.
   *
   * @param x the balanced variables.
   * @param a the positive multiplier of each x[i].
   * @param b the value a * x[i] is compared with.
   * @param sum the sum of x.
   * @param spread the sum of (a * x[i] - b)<sup>2</sup>.
   */
  public Spread(IntVar[] x, int a, int b, int sum, IntVar spread) {
    super(x, a, b, sum, spread);
    this.numberId = idNumber.incrementAndGet();
    this.c = Math.floorDiv(b, a);
    this.r = Math.floorMod(b, a);
    this.low = new long[n];
    this.high = new long[n];
    this.lowSum = new long[n + 1];
    this.lowSquares = new long[n + 1];
    this.highSum = new long[n + 1];
    this.highSquares = new long[n + 1];
  }

  @Override
  long term(long v) {
    long e = a * v - b;
    return e * e;
  }

  @Override
  void narrow(Store store) {
    // every term is at most d.max: |a * x[i] - b| <= root
    long root = (long) Math.sqrt(Math.max(0, cost.max()));
    while ((root + 1) * (root + 1) <= cost.max()) {
      root++;
    }
    while (root * root > cost.max()) {
      root--;
    }
    long min = -Math.floorDiv(-(b - root), (long) a);
    long max = Math.floorDiv(b + root, (long) a);
    for (int i = 0; i < n; i++) {
      if (x[i].min() < min || x[i].max() > max) {
        if (min > x[i].max() || max < x[i].min()) {
          throw Store.failException;
        }
        x[i].domain.in(
            store.level, x[i], (int) Math.max(min, x[i].min()), (int) Math.min(max, x[i].max()));
      }
    }
  }

  @Override
  void prepare() {
    for (int i = 0; i < n; i++) {
      low[i] = lo[i] - c;
      high[i] = hi[i] - c;
    }
    Arrays.sort(low);
    Arrays.sort(high);
    for (int i = 0; i < n; i++) {
      lowSum[i + 1] = lowSum[i] + low[i];
      lowSquares[i + 1] = lowSquares[i] + low[i] * low[i];
      highSum[i + 1] = highSum[i] + high[i];
      highSquares[i + 1] = highSquares[i] + high[i] * high[i];
    }
  }

  @Override
  long least(int skip, long t) {
    long count = skip >= 0 ? n - 1 : n;
    long target = t - count * c;
    long skipLow = skip >= 0 ? lo[skip] - c : 0;
    long skipHigh = skip >= 0 ? hi[skip] - c : 0;

    // the largest level whose sum is at most target; the sum at low[0] is the sum of the minima
    long l = low[0];
    long h = high[n - 1];
    while (l < h) {
      long m = h - (h - l) / 2;
      long level = level(m);
      if (skip >= 0) {
        level -= clamp(m, skipLow, skipHigh);
      }
      if (level <= target) {
        l = m;
      } else {
        h = m - 1;
      }
    }
    long level = level(l);
    long squares = squares(l);
    if (skip >= 0) {
      long v = clamp(l, skipLow, skipHigh);
      level -= v;
      squares -= v * v;
    }
    // the remaining units go from l to l + 1
    squares += (target - level) * (2 * l + 1);

    // sum of (a * y - r)^2 = a^2 * sum of y^2 - 2 * a * r * sum of y + count * r^2
    return (long) a * a * squares - 2L * a * r * target + count * r * r;
  }

  private static long clamp(long v, long min, long max) {
    return Math.max(min, Math.min(max, v));
  }

  // sum over all variables of y[i] clamped to [low, high] at the given level
  private long level(long v) {
    int above = firstAbove(low, v);
    int below = firstAtLeast(high, v);
    long between = (long) above - below;
    return lowSum[n] - lowSum[above] + highSum[below] + v * between;
  }

  // the same sum for the squares
  private long squares(long v) {
    int above = firstAbove(low, v);
    int below = firstAtLeast(high, v);
    long between = (long) above - below;
    return lowSquares[n] - lowSquares[above] + highSquares[below] + v * v * between;
  }

  // first index with array[i] > v
  private static int firstAbove(long[] array, long v) {
    int l = 0;
    int h = array.length;
    while (l < h) {
      int m = (l + h) >>> 1;
      if (array[m] > v) {
        h = m;
      } else {
        l = m + 1;
      }
    }
    return l;
  }

  // first index with array[i] >= v
  private static int firstAtLeast(long[] array, long v) {
    int l = 0;
    int h = array.length;
    while (l < h) {
      int m = (l + h) >>> 1;
      if (array[m] >= v) {
        h = m;
      } else {
        l = m + 1;
      }
    }
    return l;
  }

  @Override
  public String toString() {
    return id() + " : Spread" + describe();
  }

  @Override
  public Spread copy(VarMap map) {
    return new Spread(map.get(x), a, b, sum, map.get(cost));
  }
}
