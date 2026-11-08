/*
 * LoadDistribution.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.prob.constraints;

import java.math.BigInteger;
import java.util.Arrays;
import org.jacop.prob.dist.Dist;
import org.jacop.prob.num.ProbArith;

/**
 * The distribution of a load {@code sum(i, m[i] * W[i])} of independent random weights with
 * multipliers, truncated to the loads {@code 0..cap}: the mass above cap is dropped, which leaves
 * {@code Pr(load <= t)} exact for every {@code t <= cap}. The probabilities are kept as intervals
 * of doubles, every operation rounded outward, so a comparison with a threshold is either certain
 * or ambiguous; an ambiguous one is decided by {@link #exactAtMost}, on BigInteger numerators.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class LoadDistribution {

  final int cap;

  // lo[t] <= Pr(load = t) <= hi[t] for t in 0..cap; top is the largest t with hi[t] > 0
  final double[] lo;
  final double[] hi;
  int top;

  private double[] nextLo;
  private double[] nextHi;

  LoadDistribution(int cap) {
    this.cap = cap;
    lo = new double[cap + 1];
    hi = new double[cap + 1];
    nextLo = new double[cap + 1];
    nextHi = new double[cap + 1];
    clear();
  }

  /** Sets the load to 0 with probability 1. */
  void clear() {
    Arrays.fill(lo, 0, top + 1, 0);
    Arrays.fill(hi, 0, top + 1, 0);
    lo[0] = 1;
    hi[0] = 1;
    top = 0;
  }

  /** Copies another load of the same cap. */
  void copyFrom(LoadDistribution other) {
    Arrays.fill(lo, 0, top + 1, 0);
    Arrays.fill(hi, 0, top + 1, 0);
    System.arraycopy(other.lo, 0, lo, 0, other.top + 1);
    System.arraycopy(other.hi, 0, hi, 0, other.top + 1);
    top = other.top;
  }

  static double down(double d) {
    return d == 0 ? 0 : Math.nextDown(d);
  }

  static double up(double d) {
    return Math.nextUp(d);
  }

  /**
   * Adds {@code m * W} for a random weight W of non-negative values.
   *
   * @param w the distribution of W
   * @param pLo the lower ends of the probabilities of the values of w
   * @param pHi the upper ends
   * @param m the multiplier, at least 1
   */
  void add(Dist w, double[] pLo, double[] pHi, long m) {
    int newTop = -1;
    int size = w.size();
    for (int t = 0; t <= top; t++) {
      double l = lo[t];
      double h = hi[t];
      if (h == 0) {
        continue;
      }
      for (int k = 0; k < size; k++) {
        long s = t + m * w.value(k);
        if (s > cap) {
          break;
        }
        int u = (int) s;
        nextLo[u] = down(nextLo[u] + down(l * pLo[k]));
        nextHi[u] = up(nextHi[u] + up(h * pHi[k]));
        newTop = Math.max(newTop, u);
      }
    }
    Arrays.fill(lo, 0, top + 1, 0);
    Arrays.fill(hi, 0, top + 1, 0);
    System.arraycopy(nextLo, 0, lo, 0, newTop + 1);
    System.arraycopy(nextHi, 0, hi, 0, newTop + 1);
    Arrays.fill(nextLo, 0, newTop + 1, 0);
    Arrays.fill(nextHi, 0, newTop + 1, 0);
    top = newTop;
  }

  /**
   * Returns the enclosure {lo, hi} of {@code Pr(load <= t)}.
   *
   * @param t a load, at most cap
   * @param out an array of length 2 that receives the enclosure
   */
  void atMost(long t, double[] out) {
    double l = 0;
    double h = 0;
    long last = Math.min(t, top);
    for (int u = 0; u <= last; u++) {
      l = down(l + lo[u]);
      h = up(h + hi[u]);
    }
    out[0] = Math.max(0, l);
    out[1] = Math.min(1, h);
  }

  /** The cumulative enclosures: cumLo[t] &lt;= Pr(load &lt;= t) &lt;= cumHi[t] for t in 0..cap. */
  void cumulative(double[] cumLo, double[] cumHi) {
    double l = 0;
    double h = 0;
    for (int u = 0; u <= cap; u++) {
      if (u <= top) {
        l = down(l + lo[u]);
        h = up(h + hi[u]);
      }
      cumLo[u] = Math.max(0, l);
      cumHi[u] = Math.min(1, h);
    }
  }

  /** The enclosures of the probabilities of the values of a distribution. */
  static double[][] enclosures(Dist w) {
    double[] pLo = new double[w.size()];
    double[] pHi = new double[w.size()];
    for (int k = 0; k < w.size(); k++) {
      double[] e = ProbArith.enclosure(w.weight(k), w.den());
      pLo[k] = e[0];
      pHi[k] = e[1];
    }
    return new double[][] {pLo, pHi};
  }

  /**
   * Compares exactly {@code Pr(sum(i, m[i] * W[i]) <= t)} with {@code num / den}.
   *
   * @param w the distributions, of non-negative values
   * @param m the multipliers, at least 0, of the same length
   * @param count the number of terms used, from the start of w and m
   * @param t the load bound
   * @param num the numerator of the threshold
   * @param den the denominator of the threshold, positive
   * @return the sign of the probability minus the threshold
   */
  static int exactAtMost(Dist[] w, long[] m, int count, long t, long num, long den) {
    if (t < 0) {
      return Long.signum(-num);
    }
    int bound = (int) Math.min(t, Integer.MAX_VALUE - 1L);
    BigInteger[] mass = new BigInteger[] {BigInteger.ONE};
    BigInteger total = BigInteger.ONE;
    for (int i = 0; i < count; i++) {
      if (m[i] == 0) {
        continue;
      }
      Dist d = w[i];
      int size = (int) Math.min((long) mass.length - 1 + m[i] * d.max(), bound) + 1;
      BigInteger[] next = new BigInteger[size];
      Arrays.fill(next, BigInteger.ZERO);
      for (int u = 0; u < mass.length; u++) {
        if (mass[u].signum() == 0) {
          continue;
        }
        for (int k = 0; k < d.size(); k++) {
          long s = u + m[i] * d.value(k);
          if (s >= size) {
            break;
          }
          next[(int) s] = next[(int) s].add(mass[u].multiply(BigInteger.valueOf(d.weight(k))));
        }
      }
      mass = next;
      total = total.multiply(BigInteger.valueOf(d.den()));
    }
    BigInteger sum = BigInteger.ZERO;
    for (int u = 0; u < mass.length && u <= bound; u++) {
      sum = sum.add(mass[u]);
    }
    // sum / total against num / den
    return sum.multiply(BigInteger.valueOf(den)).compareTo(total.multiply(BigInteger.valueOf(num)));
  }
}
