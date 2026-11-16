/*
 * CoverCuts.java
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
import java.util.Map;
import java.util.TreeMap;

/**
 * Lifted cover cuts of knapsack rows.
 *
 * <p>A row {@code sum c x <= b} is first relaxed to a 0/1 knapsack over its 0/1 columns: a fixed
 * column moves to the side, any other integer column takes its global bound that makes its term
 * smallest, and a 0/1 column with a negative weight is complemented ({@code y = 1 - x}). In the
 * knapsack {@code sum a y <= b} with {@code a > 0}, a cover {@code C} is a set of items with {@code
 * a(C) > b}, so at most {@code |C| - 1} of them are 1. The cover is chosen greedily by {@code (1 -
 * y*) / a} over the LP solution {@code y*} (H. Crowder, E. L. Johnson and M. Padberg, Solving
 * large-scale zero-one linear programming problems, Operations Research 31(5), 1983) and made
 * minimal by dropping the items of least LP value.
 *
 * <p>The items outside the cover are lifted at once, with a superadditive lifting function of the
 * cover (sequence-independent lifting: Z. Gu, G. L. Nemhauser and M. W. P. Savelsbergh, Sequence
 * independent lifting in mixed integer programming, Journal of Combinatorial Optimization 4(1),
 * 2000, 109-129, and Lifted cover inequalities for 0-1 integer programs: computation, INFORMS
 * Journal on Computing 10(4), 1998, 427-437): any superadditive function below the exact lifting
 * function of the cover lifts all items together. With the cover weights {@code a_1 >= ... >= a_r},
 * {@code mu_h = a_1 + ... + a_h} and the excess {@code lambda = mu_r - b}, the exact function is
 * {@code f(z) = h} for {@code mu_h - lambda < z <= mu_(h+1) - lambda}. The function used here is
 * integral, which keeps the cut's weights integral: {@code g(z)} is the largest {@code h <= r - 1}
 * with {@code z > mu_h - lambda} and {@code z >= mu_(h+1) - a_1}. The first condition gives {@code
 * g <= f}; the second makes {@code g} superadditive, since for {@code g(z1) = h1 >= 1} and {@code
 * g(z2) = h2} the sum {@code z1 + z2 > mu_h1 - lambda + a_2 + ... + a_(h2+1) >= mu_(h1+h2) -
 * lambda}, and likewise for the second condition. It is the integral step of Gu, Nemhauser and
 * Savelsbergh's function and at least Balas' simultaneous lifting ({@code h} for {@code mu_h <= z <
 * mu_(h+1)}; E. Balas, Facets of the knapsack polytope, Mathematical Programming 8, 1975, 146-164).
 *
 * <p>The cut holds over the global bounds it is given, as the MIR cuts of the same rows do, so it
 * holds everywhere in search.
 */
final class CoverCuts {

  private CoverCuts() {}

  // the lifting function of Gu, Nemhauser and Savelsbergh with its fractional steps, scaled to
  // integers (-Dorg.jacop.lp.coverScaled=false: its integral rounding down)
  private static final boolean SCALED =
      !Boolean.FALSE.toString().equals(System.getProperty("org.jacop.lp.coverScaled"));

  /**
   * Returns the most violated lifted cover cut of {@code sum c x <= b}, as a row {@code sum w x <=
   * rhs} over the same columns, or null when the row has no cover, no violated cut, or its
   * arithmetic overflows.
   *
   * @param columns the columns of the row
   * @param c the weight of each column (not changed)
   * @param b the right side
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @return the cut, or null
   */
  static MirCut separate(int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi) {
    try {
      return cut(columns, c, b, value, lo, hi);
    } catch (ArithmeticException e) {
      return null;
    }
  }

  private static MirCut cut(int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi) {
    int n = columns.length;
    int[] item = new int[n];
    long[] a = new long[n];
    boolean[] complemented = new boolean[n];
    double[] y = new double[n];
    int m = 0;
    long side = b;
    for (int k = 0; k < n; k++) {
      long w = c[k];
      int j = columns[k];
      if (w == 0) {
        continue;
      }
      if (lo[j] == hi[j]) {
        side = Math.subtractExact(side, Math.multiplyExact(w, lo[j]));
      } else if (lo[j] == 0 && hi[j] == 1) {
        item[m] = j;
        double v = Math.clamp(value[j], 0.0, 1.0);
        if (w > 0) {
          a[m] = w;
          y[m] = v;
        } else {
          a[m] = Math.negateExact(w);
          y[m] = 1 - v;
          complemented[m] = true;
          side = Math.addExact(side, a[m]);
        }
        m++;
      } else {
        side = Math.subtractExact(side, Math.multiplyExact(w, w > 0 ? lo[j] : hi[j]));
      }
    }
    if (m < 2 || side < 0) {
      return null;
    }
    long total = 0;
    for (int k = 0; k < m; k++) {
      total = Math.addExact(total, a[k]);
    }
    if (total <= side) {
      return null;
    }
    boolean[] inCover = cover(m, a, y, side);
    if (inCover == null) {
      return null;
    }
    long[] coef = lifted(m, a, inCover, side, SCALED);
    int r = 0;
    for (int k = 0; k < m; k++) {
      if (inCover[k]) {
        r++;
      }
    }
    // the cut sum coef y <= r - 1 over the knapsack's items, back over the columns
    long rhs = Math.multiplyExact(r - 1L, coef[m]);
    Map<Integer, Long> weights = new TreeMap<>();
    for (int k = 0; k < m; k++) {
      if (coef[k] == 0) {
        continue;
      }
      if (complemented[k]) {
        rhs = Math.subtractExact(rhs, coef[k]);
        weights.merge(item[k], -coef[k], Math::addExact);
      } else {
        weights.merge(item[k], coef[k], Math::addExact);
      }
    }
    weights.values().removeIf(w -> w == 0);
    if (weights.isEmpty()) {
      return null;
    }
    int[] cs = new int[weights.size()];
    long[] ws = new long[weights.size()];
    int q = 0;
    double activity = 0;
    double norm = 0;
    for (Map.Entry<Integer, Long> e : weights.entrySet()) {
      cs[q] = e.getKey();
      ws[q] = e.getValue();
      activity += ws[q] * value[cs[q]];
      norm += (double) ws[q] * ws[q];
      q++;
    }
    double efficacy = (activity - rhs) / Math.sqrt(norm);
    if (!(efficacy > MirCut.MIN_EFFICACY)) {
      return null;
    }
    return MirCut.row(cs, ws, rhs, efficacy);
  }

  /**
   * Returns a minimal cover of the knapsack {@code sum a y <= side}, or null: items are taken by
   * {@code (1 - y) / a} ascending until their weight exceeds the side, then items of least {@code
   * y} are dropped while the rest still exceeds it.
   */
  static boolean[] cover(int m, long[] a, double[] y, long side) {
    Integer[] order = new Integer[m];
    for (int k = 0; k < m; k++) {
      order[k] = k;
    }
    Arrays.sort(
        order,
        (p, q) -> {
          int t = Double.compare((1 - y[p]) / a[p], (1 - y[q]) / a[q]);
          return t != 0 ? t : Long.compare(a[q], a[p]);
        });
    boolean[] in = new boolean[m];
    long sum = 0;
    int size = 0;
    for (int k = 0; k < m && sum <= side; k++) {
      in[order[k]] = true;
      sum = Math.addExact(sum, a[order[k]]);
      size++;
    }
    if (sum <= side) {
      return null;
    }
    // minimal: drop the items of least LP value first (then the lightest), while still a cover
    Integer[] drop = new Integer[size];
    int d = 0;
    for (int k = 0; k < m; k++) {
      if (in[k]) {
        drop[d++] = k;
      }
    }
    Arrays.sort(
        drop,
        (p, q) -> {
          int t = Double.compare(y[p], y[q]);
          return t != 0 ? t : Long.compare(a[p], a[q]);
        });
    for (int k : drop) {
      if (sum - a[k] > side) {
        in[k] = false;
        sum -= a[k];
      }
    }
    // the cover inequality alone: sum over C of (1 - y) < 1 when violated; lifting can only add
    double slack = 0;
    for (int k = 0; k < m; k++) {
      if (in[k]) {
        slack += 1 - y[k];
      }
    }
    // a cover far from violated rarely becomes violated by lifting (its items outside are light)
    return slack < 2 ? in : null;
  }

  /**
   * Returns the weights of the lifted cover inequality {@code sum coef y <= |C| - 1}: 1 on the
   * cover, the integral superadditive lifting function {@code g} of the class comment outside it.
   *
   * @param m the number of items
   * @param a the weights of the items, positive
   * @param inCover the minimal cover
   * @param side the side of the knapsack, below the weight of the cover
   * @return the weight of each item in the cut
   */
  static long[] lifted(int m, long[] a, boolean[] inCover, long side) {
    return Arrays.copyOf(lifted(m, a, inCover, side, false), m);
  }

  /**
   * Returns the weights of the lifted cover inequality, scaled: {@code sum coef y <= (|C| - 1) s}
   * with the scale {@code s} at index {@code m}. Unscaled ({@code s = 1}) the function is the
   * integral {@code g} of the class comment; scaled, it is the function of Gu, Nemhauser and
   * Savelsbergh itself, {@code h} on {@code [mu_h - lambda + rho_h, mu_(h+1) - lambda]} and {@code
   * h - (mu_h - lambda + rho_h - z) / rho_1} just below, times {@code s = rho_1} so that it stays
   * integral.
   */
  static long[] lifted(int m, long[] a, boolean[] inCover, long side, boolean scaled) {
    int r = 0;
    for (int k = 0; k < m; k++) {
      if (inCover[k]) {
        r++;
      }
    }
    long[] sorted = new long[r];
    int t = 0;
    for (int k = 0; k < m; k++) {
      if (inCover[k]) {
        sorted[t++] = a[k];
      }
    }
    Arrays.sort(sorted);
    // descending: a_1 >= ... >= a_r, mu[h] = a_1 + ... + a_h
    long[] mu = new long[r + 1];
    for (int h = 1; h <= r; h++) {
      mu[h] = Math.addExact(mu[h - 1], sorted[r - h]);
    }
    long lambda = mu[r] - side;
    long a1 = sorted[r - 1];
    // rho[h] = max(0, a_(h+1) - (a_1 - lambda)), h = 0 .. r - 1
    long[] rho = new long[r];
    for (int h = 0; h < r; h++) {
      rho[h] = Math.max(0, sorted[r - 1 - h] - (a1 - lambda));
    }
    long scale = scaled && r >= 2 ? Math.max(1, rho[1]) : 1;
    long[] coef = new long[m + 1];
    coef[m] = scale;
    for (int k = 0; k < m; k++) {
      if (inCover[k]) {
        coef[k] = scale;
        continue;
      }
      long z = a[k];
      if (z > side) {
        // the item never fits: any weight is valid, r keeps the cut tightest
        coef[k] = Math.multiplyExact(r, scale);
        continue;
      }
      if (scale == 1) {
        int h = 0;
        while (h + 1 <= r - 1 && z > mu[h + 1] - lambda && z >= mu[h + 2] - a1) {
          h++;
        }
        coef[k] = h;
        continue;
      }
      // the class of the exact lifting function: the largest h <= r - 1 with z > mu_h - lambda
      int h = 0;
      while (h + 1 <= r - 1 && z > mu[h + 1] - lambda) {
        h++;
      }
      long flat = Math.addExact(mu[h] - lambda, rho[h]);
      coef[k] =
          h == 0 || z >= flat
              ? Math.multiplyExact(h, scale)
              : Math.multiplyExact(h, scale) - (flat - z);
    }
    return coef;
  }
}
