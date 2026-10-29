/*
 * DivModPowBounds.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints;

/**
 * Bounds reasoning for {@code x div y = z}, {@code x mod y = z} (both rounding towards zero) and
 * {@code x ^ y = z} (with {@code 1 div x^-y} for a negative exponent and no solution for {@code x =
 * 0} then, as MiniZinc's int_pow). Each method narrows a box {xl, xh, yl, yh, zl, zh} to the
 * smallest box holding every solution in it, so every bound has a support with the other variables
 * in their intervals (bounds(Z) consistency). Only the bounds are read, so the same method decides
 * a propagation and checks its explanation.
 *
 * <p>With y fixed to v the relation is monotone in x (div), periodic in x (mod) or monotone on each
 * sign of x (pow), and the solutions in the box are found in constant time; the divisors are
 * enumerated. Divisors larger in magnitude than every x behave alike (quotient 0, remainder x) and
 * are one class, and exponents below -2 or above 31 behave as -1, -2, 30 or 31 of their parity.
 * When more than {@link #ENUMERATION_LIMIT} divisors remain, a weaker interval rule is used for x
 * and z, and the bounds of y are searched from both ends for a supported value.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class DivModPowBounds {

  /** The most divisors enumerated one by one. */
  static final int ENUMERATION_LIMIT = 128;

  private static final long NONE_LOW = Long.MAX_VALUE;
  private static final long NONE_HIGH = Long.MIN_VALUE;

  private DivModPowBounds() {}

  /** A function that narrows a box {xl, xh, yl, yh, zl, zh}, or returns false when it is empty. */
  @FunctionalInterface
  interface Narrowing {
    boolean narrow(long[] box);
  }

  /** The hulls of the supported values found so far. */
  private static final class Hull {
    final long[] b;
    long xl = NONE_LOW;
    long xh = NONE_HIGH;
    long yl = NONE_LOW;
    long yh = NONE_HIGH;
    long zl = NONE_LOW;
    long zh = NONE_HIGH;
    // set by the fixed-divisor methods: the solutions with that divisor
    long sxl;
    long sxh;
    long szl;
    long szh;

    Hull(long[] b) {
      this.b = b;
    }

    void addY(long v) {
      yl = Math.min(yl, v);
      yh = Math.max(yh, v);
    }

    // adds the solutions with the last fixed divisor, of y values lo..hi
    void addLast(long lo, long hi) {
      addY(lo);
      addY(hi);
      xl = Math.min(xl, sxl);
      xh = Math.max(xh, sxh);
      zl = Math.min(zl, szl);
      zh = Math.max(zh, szh);
    }

    boolean store() {
      if (yl > yh) {
        return false;
      }
      b[0] = Math.max(b[0], xl);
      b[1] = Math.min(b[1], xh);
      b[2] = Math.max(b[2], yl);
      b[3] = Math.min(b[3], yh);
      b[4] = Math.max(b[4], zl);
      b[5] = Math.min(b[5], zh);
      return b[0] <= b[1] && b[2] <= b[3] && b[4] <= b[5];
    }
  }

  /** A test of one divisor (or exponent) v that leaves its solutions in the hull's s-fields. */
  @FunctionalInterface
  private interface Fixed {
    boolean solve(Hull h, long v);
  }

  // ---------------------------------------------------------------- div

  /**
   * Narrows the box of {@code x div y = z}.
   *
   * @param b the box {xl, xh, yl, yh, zl, zh}, narrowed in place
   * @return false when it holds no solution
   */
  static boolean div(long[] b) {
    return div(b, ENUMERATION_LIMIT);
  }

  // with at most limit divisors enumerated
  static boolean div(long[] b, int limit) {
    Hull h = new Hull(b);
    long m = Math.max(Math.abs(b[0]), Math.abs(b[1]));
    if (!enumerate(h, m, DivModPowBounds::divFixed, limit)) {
      divCoarse(h);
    }
    // divisors beyond |x|: the quotient is 0
    if (b[4] <= 0 && b[5] >= 0) {
      boolean any = classMember(h, b[2], Math.min(b[3], -m - 1));
      any |= classMember(h, Math.max(b[2], m + 1), b[3]);
      if (any) {
        h.xl = b[0];
        h.xh = b[1];
        h.zl = Math.min(h.zl, 0);
        h.zh = Math.max(h.zh, 0);
      }
    }
    return h.store();
  }

  // the solutions with y = v (v != 0): the quotient is monotone in x
  private static boolean divFixed(Hull h, long v) {
    long[] b = h.b;
    long m = Math.abs(v);
    // trunc(x / m) must be in [ql, qh]
    long ql = v > 0 ? b[4] : -b[5];
    long qh = v > 0 ? b[5] : -b[4];
    long lo = ql > 0 ? ql * m : (ql - 1) * m + 1;
    long hi = qh >= 0 ? (qh + 1) * m - 1 : qh * m;
    long xl = Math.max(b[0], lo);
    long xh = Math.min(b[1], hi);
    if (xl > xh) {
      return false;
    }
    long q1 = xl / v;
    long q2 = xh / v;
    h.sxl = xl;
    h.sxh = xh;
    h.szl = Math.min(q1, q2);
    h.szh = Math.max(q1, q2);
    return true;
  }

  // interval rules for x and z when the divisors are too many to enumerate
  private static void divCoarse(Hull h) {
    long[] b = h.b;
    long[][] parts = {{b[2], Math.min(b[3], -1)}, {Math.max(b[2], 1), b[3]}};
    for (long[] p : parts) {
      if (p[0] > p[1]) {
        continue;
      }
      for (long v : new long[] {p[0], p[1]}) {
        // the quotients at the corners bound those of the part
        h.zl = Math.min(h.zl, Math.min(b[0] / v, b[1] / v));
        h.zh = Math.max(h.zh, Math.max(b[0] / v, b[1] / v));
        // the ends of the x interval of a divisor are monotone in it
        long m = Math.abs(v);
        long ql = v > 0 ? b[4] : -b[5];
        long qh = v > 0 ? b[5] : -b[4];
        h.xl = Math.min(h.xl, ql > 0 ? ql * m : (ql - 1) * m + 1);
        h.xh = Math.max(h.xh, qh >= 0 ? (qh + 1) * m - 1 : qh * m);
      }
    }
  }

  // ---------------------------------------------------------------- mod

  /**
   * Narrows the box of {@code x mod y = z}.
   *
   * @param b the box {xl, xh, yl, yh, zl, zh}, narrowed in place
   * @return false when it holds no solution
   */
  static boolean mod(long[] b) {
    return mod(b, ENUMERATION_LIMIT);
  }

  // with at most limit divisors enumerated
  static boolean mod(long[] b, int limit) {
    Hull h = new Hull(b);
    long m = Math.max(Math.abs(b[0]), Math.abs(b[1]));
    if (!enumerate(h, m, DivModPowBounds::modFixed, limit)) {
      modCoarse(h);
    }
    // divisors beyond |x|: the remainder is x
    long xl = Math.max(b[0], b[4]);
    long xh = Math.min(b[1], b[5]);
    if (xl <= xh) {
      boolean any = classMember(h, b[2], Math.min(b[3], -m - 1));
      any |= classMember(h, Math.max(b[2], m + 1), b[3]);
      if (any) {
        h.xl = Math.min(h.xl, xl);
        h.xh = Math.max(h.xh, xh);
        h.zl = Math.min(h.zl, xl);
        h.zh = Math.max(h.zh, xh);
      }
    }
    return h.store();
  }

  // the solutions with y = v (v != 0): the remainder has the sign of x and depends on |v| only
  private static boolean modFixed(Hull h, long v) {
    long[] b = h.b;
    long m = Math.abs(v);
    long sxl = NONE_LOW;
    long sxh = NONE_HIGH;
    long szl = NONE_LOW;
    long szh = NONE_HIGH;
    // x >= 0, remainder in [max(zl, 0), min(zh, m - 1)]
    long[] r = residues(Math.max(b[0], 0), b[1], Math.max(b[4], 0), Math.min(b[5], m - 1), m);
    if (r != null) {
      sxl = r[0];
      sxh = r[1];
      szl = r[2];
      szh = r[3];
    }
    // x < 0, mirrored: -x >= 1 with remainder in [max(-zh, 0), min(-zl, m - 1)]
    r = residues(Math.max(-b[1], 1), -b[0], Math.max(-b[5], 0), Math.min(-b[4], m - 1), m);
    if (r != null) {
      sxl = Math.min(sxl, -r[1]);
      sxh = Math.max(sxh, -r[0]);
      szl = Math.min(szl, -r[3]);
      szh = Math.max(szh, -r[2]);
    }
    if (sxl > sxh) {
      return false;
    }
    h.sxl = sxl;
    h.sxh = sxh;
    h.szl = szl;
    h.szh = szh;
    return true;
  }

  /**
   * The values of [a, c] (a &gt;= 0) whose remainder by m is in [p, q]: {first, last, smallest
   * remainder, largest remainder}, or null when there are none.
   */
  private static long[] residues(long a, long c, long p, long q, long m) {
    if (a > c || p > q) {
      return null;
    }
    long ra = a % m;
    long first;
    if (ra < p) {
      first = a - ra + p;
    } else if (ra <= q) {
      first = a;
    } else {
      first = a - ra + m + p;
    }
    if (first > c) {
      return null;
    }
    long rc = c % m;
    long last;
    if (rc > q) {
      last = c - rc + q;
    } else if (rc >= p) {
      last = c;
    } else {
      last = c - rc - m + q;
    }
    long r1 = first % m;
    long r2 = last % m;
    if (last - first >= m || r1 > r2) {
      // the remainders wrap around, so every allowed one is met
      return new long[] {first, last, p, q};
    }
    return new long[] {first, last, r1, r2};
  }

  // interval rules for x and z when the divisors are too many to enumerate
  private static void modCoarse(Hull h) {
    long[] b = h.b;
    long m = Math.max(Math.abs(b[2]), Math.abs(b[3]));
    // the remainder has the sign of x and is smaller than |y| and than |x|
    h.zl = b[0] >= 0 ? 0 : Math.max(b[0], 1 - m);
    h.zh = b[1] <= 0 ? 0 : Math.min(b[1], m - 1);
    // a positive remainder needs a larger positive x, a negative one a smaller negative x
    h.xl = b[4] > 0 ? b[4] : b[0];
    h.xh = b[5] < 0 ? b[5] : b[1];
  }

  // ---------------------------------------------------------------- pow

  /**
   * Narrows the box of {@code x ^ y = z}.
   *
   * @param b the box {xl, xh, yl, yh, zl, zh}, narrowed in place
   * @return false when it holds no solution
   */
  static boolean pow(long[] b) {
    Hull h = new Hull(b);
    long yl = b[2];
    long yh = b[3];
    // every exponent behaves as one of -2..31, and the smallest and the largest supported one of
    // each parity class are among these
    long[] ends = {yl, yl + 1, yh - 1, yh};
    for (long n : ends) {
      if (n >= yl && n <= yh && (n < -2 || n > 31) && powFixed(h, n)) {
        h.addLast(n, n);
      }
    }
    for (long n = Math.max(yl, -2); n <= Math.min(yh, 31); n++) {
      if (powFixed(h, n)) {
        h.addLast(n, n);
      }
    }
    return h.store();
  }

  // the solutions with y = n
  private static boolean powFixed(Hull h, long n) {
    long[] b = h.b;
    if (n == 0) {
      if (b[4] > 1 || b[5] < 1) {
        return false;
      }
      setSolutions(h, b[0], b[1], 1, 1);
      return true;
    }
    if (n < 0) {
      return negativeExponent(h, (n & 1) != 0);
    }
    // beyond 29 only x in -1..1 has a power in the int range
    int e = n > 31 ? 30 + (int) (n & 1) : (int) n;
    if ((e & 1) != 0) {
      // increasing
      long xl = Math.max(b[0], floorRoot(b[4] - 1, e) + 1);
      long xh = Math.min(b[1], floorRoot(b[5], e));
      if (xl > xh) {
        return false;
      }
      setSolutions(h, xl, xh, power(xl, e), power(xh, e));
      return true;
    }
    // z = |x|^e with |x| in [r1, r2]
    if (b[5] < 0) {
      return false;
    }
    long r1 = b[4] <= 0 ? 0 : floorRoot(b[4] - 1, e) + 1;
    long r2 = floorRoot(b[5], e);
    long pl = Math.max(b[0], r1);
    long ph = Math.min(b[1], r2);
    long nl = Math.max(b[0], -r2);
    long nh = Math.min(b[1], -r1);
    long xl = NONE_LOW;
    long xh = NONE_HIGH;
    long al = NONE_LOW;
    long ah = NONE_HIGH;
    if (pl <= ph) {
      xl = pl;
      xh = ph;
      al = pl;
      ah = ph;
    }
    if (nl <= nh) {
      xl = Math.min(xl, nl);
      xh = Math.max(xh, nh);
      al = Math.min(al, -nh);
      ah = Math.max(ah, -nl);
    }
    if (xl > xh) {
      return false;
    }
    setSolutions(h, xl, xh, power(al, e), power(ah, e));
    return true;
  }

  // 1 div x^n for n < 0: 1 for x = 1, +-1 for x = -1, 0 for |x| >= 2, none for x = 0
  private static boolean negativeExponent(Hull h, boolean odd) {
    long[] b = h.b;
    long xl = NONE_LOW;
    long xh = NONE_HIGH;
    long zl = NONE_LOW;
    long zh = NONE_HIGH;
    long[][] pieces = {
      {b[0], Math.min(b[1], -2), 0}, {-1, -1, odd ? -1 : 1}, {1, 1, 1}, {Math.max(b[0], 2), b[1], 0}
    };
    for (long[] p : pieces) {
      long lo = Math.max(p[0], b[0]);
      long hi = Math.min(p[1], b[1]);
      if (lo <= hi && p[2] >= b[4] && p[2] <= b[5]) {
        xl = Math.min(xl, lo);
        xh = Math.max(xh, hi);
        zl = Math.min(zl, p[2]);
        zh = Math.max(zh, p[2]);
      }
    }
    if (xl > xh) {
      return false;
    }
    setSolutions(h, xl, xh, zl, zh);
    return true;
  }

  private static void setSolutions(Hull h, long xl, long xh, long zl, long zh) {
    h.sxl = xl;
    h.sxh = xh;
    h.szl = zl;
    h.szh = zh;
  }

  /** v^n for n &gt; 0, saturated to a value outside the int range when it does not fit. */
  static long power(long v, int n) {
    if (v == 0 || v == 1) {
      return v;
    }
    if (v == -1) {
      return (n & 1) == 0 ? 1 : -1;
    }
    long r = 1;
    for (int i = 0; i < n; i++) {
      r *= v;
      if (r > Integer.MAX_VALUE || r < Integer.MIN_VALUE) {
        // |v| >= 2, so the remaining factors only move r further out
        return v > 0 || (n & 1) == 0 ? Long.MAX_VALUE / 2 : Long.MIN_VALUE / 2;
      }
    }
    return r;
  }

  /**
   * The largest r with r^n &lt;= w, for n &gt; 0 where r^n is strictly increasing on the candidate
   * values: n odd, or w and r non-negative (r = -1 when w &lt; 0 and n is even).
   */
  static long floorRoot(long w, int n) {
    if (n == 1) {
      return w;
    }
    if (w < 0 && (n & 1) == 0) {
      return -1;
    }
    double estimate = Math.pow(Math.abs((double) w), 1.0 / n);
    long r = (long) Math.floor(w < 0 ? -estimate : estimate);
    while (power(r + 1, n) <= w) {
      r++;
    }
    while (power(r, n) > w) {
      r--;
    }
    return r;
  }

  // ---------------------------------------------------------------- divisors

  /**
   * Adds the solutions of each divisor v in the box with 0 &lt; |v| &lt;= m, when there are at most
   * limit. Otherwise only the bounds of y are searched, from each end, and false tells the caller
   * to bound x and z itself.
   */
  private static boolean enumerate(Hull h, long m, Fixed f, int limit) {
    long lo = Math.max(h.b[2], -m);
    long hi = Math.min(h.b[3], m);
    if (lo > hi) {
      return true;
    }
    if (hi - lo + 1 <= limit) {
      for (long v = lo; v <= hi; v++) {
        if (v != 0 && f.solve(h, v)) {
          h.addLast(v, v);
        }
      }
      return true;
    }
    // the smallest and the largest supported divisors; past the limit the bound is kept
    long v = lo;
    for (int k = 0; v <= hi && (v == 0 || !f.solve(h, v)); v++, k++) {
      if (k == limit) {
        h.addY(v);
        break;
      }
    }
    if (v <= hi) {
      h.addY(v);
    }
    v = hi;
    for (int k = 0; v >= lo && (v == 0 || !f.solve(h, v)); v--, k++) {
      if (k == limit) {
        h.addY(v);
        break;
      }
    }
    if (v >= lo) {
      h.addY(v);
    }
    return false;
  }

  // adds the bounds of y values lo..hi, the members of a class of divisors that is supported
  private static boolean classMember(Hull h, long lo, long hi) {
    if (lo > hi) {
      return false;
    }
    h.addY(lo);
    h.addY(hi);
    return true;
  }
}
