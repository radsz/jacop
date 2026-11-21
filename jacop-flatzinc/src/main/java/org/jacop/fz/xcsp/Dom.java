/*
 * Dom.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in material modified versions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.xcsp;

import java.util.Arrays;

/**
 * An immutable finite set of integers, kept as sorted disjoint intervals {@code [lo[i], hi[i]]}
 * with a gap of at least one value between two intervals. The values are longs so that the reader
 * can hold XCSP3 domains beyond the int range before it clamps them.
 */
final class Dom {

  static final Dom EMPTY = new Dom(new long[0], new long[0]);

  /** The domain {0, 1} of a 0/1 variable. */
  static final Dom BOOL = range(0, 1);

  final long[] lo;
  final long[] hi;

  private Dom(long[] lo, long[] hi) {
    this.lo = lo;
    this.hi = hi;
  }

  static Dom range(long min, long max) {
    if (min > max) {
      return EMPTY;
    }
    return new Dom(new long[] {min, 0}, new long[] {max, 0}).trim(1);
  }

  static Dom value(long v) {
    return range(v, v);
  }

  /**
   * The domain of the given values, in any order and with repetitions.
   *
   * @param values the values
   * @param n how many of them to read
   * @return the domain
   */
  static Dom of(long[] values, int n) {
    long[] v = Arrays.copyOf(values, n);
    Arrays.sort(v);
    Builder b = new Builder();
    for (long x : v) {
      b.add(x, x);
    }
    return b.build();
  }

  private Dom trim(int n) {
    return new Dom(Arrays.copyOf(lo, n), Arrays.copyOf(hi, n));
  }

  boolean isEmpty() {
    return lo.length == 0;
  }

  long min() {
    return lo[0];
  }

  long max() {
    return hi[hi.length - 1];
  }

  int intervals() {
    return lo.length;
  }

  /** The number of values, saturated at Long.MAX_VALUE. */
  long size() {
    long s = 0;
    for (int i = 0; i < lo.length; i++) {
      long d = hi[i] - lo[i] + 1;
      if (d <= 0 || s > Long.MAX_VALUE - d) {
        return Long.MAX_VALUE;
      }
      s += d;
    }
    return s;
  }

  boolean isInterval() {
    return lo.length == 1;
  }

  boolean isSingleton() {
    return lo.length == 1 && lo[0] == hi[0];
  }

  boolean contains(long v) {
    int i = find(v);
    return i >= 0;
  }

  // the interval holding v, or -1
  private int find(long v) {
    int a = 0;
    int b = lo.length - 1;
    while (a <= b) {
      int m = (a + b) >>> 1;
      if (v < lo[m]) {
        b = m - 1;
      } else if (v > hi[m]) {
        a = m + 1;
      } else {
        return m;
      }
    }
    return -1;
  }

  /** Whether every value is 0 or 1. */
  boolean isZeroOne() {
    return !isEmpty() && min() >= 0 && max() <= 1;
  }

  Dom intersect(Dom o) {
    Builder b = new Builder();
    int i = 0;
    int j = 0;
    while (i < lo.length && j < o.lo.length) {
      long a = Math.max(lo[i], o.lo[j]);
      long z = Math.min(hi[i], o.hi[j]);
      if (a <= z) {
        b.add(a, z);
      }
      if (hi[i] < o.hi[j]) {
        i++;
      } else {
        j++;
      }
    }
    return b.build();
  }

  Dom intersect(long min, long max) {
    if (!isEmpty() && min <= min() && max >= max()) {
      return this;
    }
    return intersect(range(min, max));
  }

  Dom union(Dom o) {
    Builder b = new Builder();
    int i = 0;
    int j = 0;
    while (i < lo.length || j < o.lo.length) {
      if (j >= o.lo.length || (i < lo.length && lo[i] <= o.lo[j])) {
        b.add(lo[i], hi[i]);
        i++;
      } else {
        b.add(o.lo[j], o.hi[j]);
        j++;
      }
    }
    return b.build();
  }

  Dom minus(Dom o) {
    Builder b = new Builder();
    int j = 0;
    for (int i = 0; i < lo.length; i++) {
      long a = lo[i];
      long z = hi[i];
      while (j < o.lo.length && o.hi[j] < a) {
        j++;
      }
      int k = j;
      while (a <= z && k < o.lo.length && o.lo[k] <= z) {
        if (o.lo[k] > a) {
          b.add(a, o.lo[k] - 1);
        }
        a = Math.max(a, o.hi[k] == Long.MAX_VALUE ? Long.MAX_VALUE : o.hi[k] + 1);
        if (o.hi[k] == Long.MAX_VALUE) {
          a = z + 1;
          break;
        }
        k++;
      }
      if (a <= z) {
        b.add(a, z);
      }
    }
    return b.build();
  }

  Dom minus(long v) {
    if (!contains(v)) {
      return this;
    }
    return minus(value(v));
  }

  /** The values of an intervals' list as a FlatZinc set literal or range. */
  String toFzn() {
    if (isEmpty()) {
      return "{}";
    }
    if (lo.length == 1) {
      return lo[0] + ".." + hi[0];
    }
    StringBuilder s = new StringBuilder("{");
    boolean first = true;
    for (int i = 0; i < lo.length; i++) {
      for (long v = lo[i]; v <= hi[i]; v++) {
        if (!first) {
          s.append(',');
        }
        first = false;
        s.append(v);
      }
    }
    return s.append('}').toString();
  }

  /** Whether {@link #toFzn} would spell out more than the given number of values. */
  boolean largeEnumeration(long limit) {
    return lo.length > 1 && size() > limit;
  }

  /** The values one by one; only for domains of a reasonable size. */
  long[] values() {
    long s = size();
    if (s > Integer.MAX_VALUE - 8) {
      throw new IllegalStateException("domain too large to enumerate");
    }
    long[] v = new long[(int) s];
    int k = 0;
    for (int i = 0; i < lo.length; i++) {
      for (long x = lo[i]; x <= hi[i]; x++) {
        v[k++] = x;
      }
    }
    return v;
  }

  @Override
  public boolean equals(Object o) {
    return o instanceof Dom d && Arrays.equals(lo, d.lo) && Arrays.equals(hi, d.hi);
  }

  @Override
  public int hashCode() {
    return 31 * Arrays.hashCode(lo) + Arrays.hashCode(hi);
  }

  @Override
  public String toString() {
    return toFzn();
  }

  /** Builds a domain from intervals given in increasing order of their lower bounds. */
  static final class Builder {
    private long[] lo = new long[4];
    private long[] hi = new long[4];
    private int n;

    void add(long a, long z) {
      if (a > z) {
        return;
      }
      if (n > 0 && (hi[n - 1] == Long.MAX_VALUE || a <= hi[n - 1] + 1)) {
        hi[n - 1] = Math.max(hi[n - 1], z);
        return;
      }
      if (n == lo.length) {
        lo = Arrays.copyOf(lo, 2 * n);
        hi = Arrays.copyOf(hi, 2 * n);
      }
      lo[n] = a;
      hi[n] = z;
      n++;
    }

    Dom build() {
      return n == 0 ? EMPTY : new Dom(Arrays.copyOf(lo, n), Arrays.copyOf(hi, n));
    }
  }
}
