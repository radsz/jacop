/*
 * MirCut.java
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

package org.jacop.constraints.lp;

import java.util.Arrays;

/**
 * A mixed-integer rounding (MIR) cut of an integer inequality, computed exactly in integers.
 *
 * <p>Given {@code sum c_j x_j <= b} over integer variables with bounds {@code l_j <= x_j <= u_j},
 * each variable is complemented to the bound nearer its LP value ({@code x_j = l_j + x'_j} or
 * {@code x_j = u_j - x'_j}), giving {@code sum c'_j x'_j <= b'} with {@code x' >= 0}. For a divisor
 * {@code d > 0} with {@code r = b' mod d > 0}, the MIR inequality of the row divided by d,
 * multiplied by {@code d - r}, is
 *
 * <pre>
 *   sum_j (floor(c'_j / d) (d - r) + max(0, (c'_j mod d) - r)) x'_j &lt;= floor(b' / d) (d - r),
 * </pre>
 *
 * with integer coefficients only. It holds for every integer {@code x' >= 0} that meets the row, so
 * it holds wherever the row and the bounds do. The bounds must be global (the root bounds), so that
 * the cut is global too. Divisors are taken from the coefficients of the variables strictly inside
 * their bounds in the LP solution, and halved a few times (c-MIR); the cut most violated by the LP
 * solution, relative to its norm, is kept.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class MirCut {

  /** The least efficacy (violation over the Euclidean norm of the cut) a cut must have. */
  static final double MIN_EFFICACY = 1e-3;

  private static final int MAX_DIVISORS = 8;

  // the largest ratio of the weights of a cut, against badly scaled rows in the simplex
  private static final double MAX_RATIO = 1e4;

  // the largest weight of a cut, so that combinations with the rows stay within a long
  private static final long MAX_WEIGHT = 1L << 24;

  /** The columns of the cut. */
  final int[] columns;

  /** The weights of the cut, by column. */
  final long[] weights;

  /** The right side: {@code sum weights x <= rhs}. */
  final long rhs;

  /** The violation of the cut by the LP solution over its norm. */
  final double efficacy;

  /** The Euclidean norm of the weights. */
  final double norm;

  private MirCut(int[] columns, long[] weights, long rhs, double efficacy, double norm) {
    this.columns = columns;
    this.weights = weights;
    this.rhs = rhs;
    this.efficacy = efficacy;
    this.norm = norm;
  }

  /**
   * Returns the best MIR cut of {@code sum c x <= b}, or null when none is violated enough or the
   * arithmetic overflows.
   *
   * @param c the weights by column (not changed)
   * @param b the right side
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @return the cut, or null
   */
  static MirCut of(long[] c, long b, double[] value, long[] lo, long[] hi) {
    try {
      return cut(c, b, value, lo, hi);
    } catch (ArithmeticException _) {
      return null;
    }
  }

  private static MirCut cut(long[] c, long b, double[] value, long[] lo, long[] hi) {
    int n = c.length;
    long[] cc = new long[n];
    boolean[] up = new boolean[n];
    double[] xs = new double[n];
    long[] divisor = new long[n];
    double[] inside = new double[n];
    int count = 0;
    long side = b;
    int size = 0;
    for (int j = 0; j < n; j++) {
      long w = c[j];
      if (w == 0) {
        continue;
      }
      size++;
      double v = Math.clamp(value[j], (double) lo[j], (double) hi[j]);
      up[j] = hi[j] - v < v - lo[j];
      if (up[j]) {
        cc[j] = -w;
        side = Math.subtractExact(side, Math.multiplyExact(w, hi[j]));
        xs[j] = hi[j] - v;
      } else {
        cc[j] = w;
        side = Math.subtractExact(side, Math.multiplyExact(w, lo[j]));
        xs[j] = v - lo[j];
      }
      double in = Math.min(v - lo[j], hi[j] - v);
      if (in > 1e-6) {
        divisor[count] = Math.absExact(w);
        inside[count++] = in;
      }
    }
    if (size < 2 || count == 0) {
      return null;
    }
    // the divisors: the weights of the variables farthest inside their bounds, then halved
    Integer[] order = new Integer[count];
    for (int i = 0; i < count; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (p, q) -> Double.compare(inside[q], inside[p]));
    long bestDivisor = 0;
    double best = MIN_EFFICACY;
    long[] tried = new long[MAX_DIVISORS * 4];
    int triedCount = 0;
    int i = 0;
    int taken = 0;
    while (i < count && taken < MAX_DIVISORS) {
      long first = divisor[order[i]];
      i++;
      if (!contains(tried, triedCount, first)) {
        taken++;
        long d = first;
        for (int halvings = 0; d > 0 && halvings < 4; halvings++) {
          if (!contains(tried, triedCount, d)) {
            tried[triedCount] = d;
            triedCount++;
            double e = efficacy(cc, side, xs, d);
            if (e > best) {
              best = e;
              bestDivisor = d;
            }
          }
          d /= 2;
        }
      }
    }
    if (bestDivisor == 0) {
      return null;
    }
    // the cut over x', then back over x
    long d = bestDivisor;
    long r = Math.floorMod(side, d);
    long k = d - r;
    long right = Math.multiplyExact(Math.floorDiv(side, d), k);
    long[] g = new long[n];
    int nonzero = 0;
    for (int j = 0; j < n; j++) {
      if (cc[j] == 0) {
        continue;
      }
      long gj =
          Math.addExact(
              Math.multiplyExact(Math.floorDiv(cc[j], d), k),
              Math.max(0, Math.floorMod(cc[j], d) - r));
      if (gj == 0) {
        continue;
      }
      if (up[j]) {
        // gj (hi - x)
        g[j] = -gj;
        right = Math.subtractExact(right, Math.multiplyExact(gj, hi[j]));
      } else {
        // gj (x - lo)
        g[j] = gj;
        right = Math.addExact(right, Math.multiplyExact(gj, lo[j]));
      }
      nonzero++;
    }
    if (nonzero < 2) {
      return null;
    }
    long gcd = 0;
    for (long w : g) {
      gcd = gcd(gcd, Math.absExact(w));
    }
    if (gcd == 0) {
      return null;
    }
    int[] columns = new int[nonzero];
    long[] weights = new long[nonzero];
    double activity = 0;
    double norm = 0;
    int q = 0;
    for (int j = 0; j < n; j++) {
      if (g[j] != 0) {
        columns[q] = j;
        long w = g[j] / gcd;
        weights[q] = w;
        q++;
        double weight = (double) w;
        activity += weight * value[j];
        norm += weight * weight;
      }
    }
    // the weights are integers, so the right side rounds down: a Chvatal-Gomory step for free
    long rhs = Math.floorDiv(right, gcd);
    double efficacy = (activity - rhs) / Math.sqrt(norm);
    long largest = 0;
    long smallest = Long.MAX_VALUE;
    for (long w : weights) {
      largest = Math.max(largest, Math.absExact(w));
      smallest = Math.min(smallest, Math.absExact(w));
    }
    if (!(efficacy > MIN_EFFICACY) || largest > MAX_RATIO * smallest || largest > MAX_WEIGHT) {
      return null;
    }
    return new MirCut(columns, weights, rhs, efficacy, Math.sqrt(norm));
  }

  // the violation over the norm of the cut with divisor d, over x' >= 0
  private static double efficacy(long[] cc, long side, double[] xs, long d) {
    long r = Math.floorMod(side, d);
    if (r == 0) {
      return 0;
    }
    long k = d - r;
    double activity = 0;
    double norm = 0;
    for (int j = 0; j < cc.length; j++) {
      if (cc[j] != 0) {
        double gj = (double) Math.floorDiv(cc[j], d) * k + Math.max(0, Math.floorMod(cc[j], d) - r);
        activity += gj * xs[j];
        norm += gj * gj;
      }
    }
    double right = (double) Math.floorDiv(side, d) * k;
    return norm > 0 ? (activity - right) / Math.sqrt(norm) : 0;
  }

  private static boolean contains(long[] a, int size, long v) {
    for (int i = 0; i < size; i++) {
      if (a[i] == v) {
        return true;
      }
    }
    return false;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  @Override
  public String toString() {
    return Arrays.toString(columns)
        + " "
        + Arrays.toString(weights)
        + " <= "
        + rhs
        + " ("
        + efficacy
        + ")";
  }
}
