/*
 * CoverCut.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

/**
 * A lifted cover inequality of a knapsack row, computed exactly in integers.
 *
 * <p>The row {@code sum c_j x_j <= b} is first made a 0-1 knapsack {@code sum a_j y_j <= b'} with
 * {@code a_j > 0}: every column that is not 0/1 at the root is replaced by the bound that makes its
 * term smallest, and a 0/1 column with a negative weight is complemented ({@code y_j = 1 - x_j}). A
 * cover {@code C} (a set of items with {@code sum_C a_j > b'}) is found greedily from the LP
 * solution, as by Crowder, Johnson and Padberg (Operations Research 31, 1983), and made minimal,
 * which gives the cover inequality {@code sum_C y_j <= |C| - 1} of Balas (Mathematical Programming
 * 8, 1975). It is lifted to the other items by the superadditive lifting function of Gu, Nemhauser
 * and Savelsbergh ("Sequence independent lifting in mixed integer programming", Journal of
 * Combinatorial Optimization 4, 2000; and "Lifted cover inequalities for 0-1 integer programs:
 * computation", INFORMS Journal on Computing 10, 1998): with the cover sorted so that {@code a_1 >=
 * ... >= a_r}, {@code mu_h = a_1 + ... + a_h}, {@code lambda = mu_r - b'} and {@code rho_h = max(0,
 * a_{h+1} - (a_1 - lambda))},
 *
 * <pre>
 *   g(z) = 0                                       if z &lt;= mu_1 - lambda,
 *   g(z) = h - (mu_h - lambda + rho_h - z) / rho_1  if mu_h - lambda &lt; z &lt;= mu_h - lambda + rho_h,
 *   g(z) = h                                       if mu_h - lambda + rho_h &lt; z &lt;= mu_{h+1} - lambda,
 * </pre>
 *
 * and the item j outside the cover gets the weight {@code g(a_j)}. Since g is superadditive, the
 * weights do not depend on the order of lifting. Every weight is multiplied by {@code rho_1} (or 1
 * when {@code rho_1 = 0}, where g takes integer values only), so the cut has integer weights. An
 * item with {@code a_j > b'} cannot be 1 and gets the weight of {@code |C| - 1}. Items whose weight
 * is far below the largest are dropped, which only weakens the cut, as each term {@code y_j} is at
 * least 0. The bounds must be global (the root bounds), so that the cut is global too.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CoverCut {

  private CoverCut() {}

  /**
   * Returns the lifted cover cut of {@code sum c_k x_columns[k] <= b} most violated by the LP
   * solution, as a row {@code sum weights x <= rhs}, or null when there is no 0-1 knapsack with a
   * cover in the row, the cut is not violated enough, or the arithmetic overflows.
   *
   * @param columns the columns of the row, ascending, each once (not changed)
   * @param c the weights of the columns (not changed)
   * @param b the right side
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @return the cut, or null
   */
  static MirCut of(int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi) {
    try {
      return cut(columns, c, b, value, lo, hi);
    } catch (ArithmeticException _) {
      return null;
    }
  }

  private static MirCut cut(int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi) {
    int size = columns.length;
    long cap = b;
    // the 0/1 items: position in the row, weight a > 0, LP value of y
    int[] item = new int[size];
    long[] a = new long[size];
    double[] y = new double[size];
    int items = 0;
    for (int k = 0; k < size; k++) {
      int j = columns[k];
      if (c[k] == 0) {
        continue;
      }
      if (lo[j] == 0 && hi[j] == 1) {
        item[items] = k;
        if (c[k] > 0) {
          a[items] = c[k];
          y[items] = value[j];
        } else {
          a[items] = Math.negateExact(c[k]);
          y[items] = 1 - value[j];
          cap = Math.addExact(cap, a[items]);
        }
        items++;
      } else {
        cap = Math.subtractExact(cap, Math.multiplyExact(c[k], c[k] > 0 ? lo[j] : hi[j]));
      }
    }
    if (items < 2 || cap < 0) {
      return null;
    }
    final long capacity = cap;
    // the cover, greedily: the items nearest 1 per unit of weight first
    List<Integer> fit = new ArrayList<>();
    long total = 0;
    for (int i = 0; i < items; i++) {
      if (a[i] <= capacity) {
        fit.add(i);
        total = Math.addExact(total, a[i]);
      }
    }
    if (total <= capacity) {
      return null;
    }
    fit.sort(
        Comparator.comparingDouble((Integer i) -> (1 - y[i]) / a[i])
            .thenComparing(i -> -a[i])
            .thenComparing(i -> i));
    boolean[] inCover = new boolean[items];
    long weight = 0;
    List<Integer> cover = new ArrayList<>();
    for (int i : fit) {
      cover.add(i);
      inCover[i] = true;
      weight += a[i];
      if (weight > capacity) {
        break;
      }
    }
    // minimal: drop the items least in the LP solution while the rest is still a cover
    cover.sort(Comparator.comparingDouble((Integer i) -> y[i]).thenComparing(i -> a[i]));
    for (int t = 0; t < cover.size(); t++) {
      int i = cover.get(t);
      if (weight - a[i] > capacity) {
        weight -= a[i];
        inCover[i] = false;
        cover.remove(t--);
      }
    }
    int r = cover.size();
    long[] sorted = new long[r];
    for (int t = 0; t < r; t++) {
      sorted[t] = a[cover.get(t)];
    }
    Arrays.sort(sorted);
    for (int t = 0; t < r / 2; t++) {
      long s = sorted[t];
      sorted[t] = sorted[r - 1 - t];
      sorted[r - 1 - t] = s;
    }
    long lambda = weight - capacity;
    long[] mu = new long[r + 1];
    for (int h = 1; h <= r; h++) {
      mu[h] = mu[h - 1] + sorted[h - 1];
    }
    long[] rho = new long[r];
    for (int h = 0; h < r; h++) {
      rho[h] = Math.max(0, sorted[h] - sorted[0] + lambda);
    }
    // rho[h] is rho_{h} with a_{h+1} = sorted[h]
    long d = rho[1] > 0 ? rho[1] : 1;
    long[] w = new long[items];
    long top = Math.multiplyExact(r - 1L, d);
    for (int i = 0; i < items; i++) {
      w[i] = inCover[i] ? d : a[i] > capacity ? top : lifted(a[i], r, mu, lambda, rho, d);
    }
    long most = 0;
    for (long v : w) {
      most = Math.max(most, v);
    }
    if (most > MirCut.MAX_WEIGHT) {
      return null;
    }
    // terms far below the largest only make the row badly scaled; y >= 0, so they can go
    for (int i = 0; i < items; i++) {
      if (w[i] > 0 && w[i] * MirCut.MAX_RATIO < most) {
        w[i] = 0;
      }
    }
    // back to the columns: w (1 - x) = w - w x
    long rhs = top;
    long[] byPosition = new long[size];
    int nonzero = 0;
    for (int i = 0; i < items; i++) {
      if (w[i] == 0) {
        continue;
      }
      int k = item[i];
      nonzero++;
      if (c[k] > 0) {
        byPosition[k] = w[i];
      } else {
        byPosition[k] = -w[i];
        rhs -= w[i];
      }
    }
    int[] cs = new int[nonzero];
    long[] ws = new long[nonzero];
    double activity = 0;
    double norm = 0;
    for (int k = 0, q = 0; k < size; k++) {
      if (byPosition[k] != 0) {
        cs[q] = columns[k];
        ws[q++] = byPosition[k];
        activity += byPosition[k] * value[columns[k]];
        norm += (double) byPosition[k] * byPosition[k];
      }
    }
    double efficacy = (activity - rhs) / Math.sqrt(norm);
    if (!(efficacy > MirCut.MIN_EFFICACY)) {
      return null;
    }
    return MirCut.row(cs, ws, rhs, efficacy, true);
  }

  // d g(z) for an item of weight z <= the capacity outside the cover
  private static long lifted(long z, int r, long[] mu, long lambda, long[] rho, long d) {
    int h = 0;
    while (h < r - 1 && z > mu[h + 1] - lambda) {
      h++;
    }
    if (h == 0) {
      return 0;
    }
    long start = mu[h] - lambda + rho[h];
    if (z <= start) {
      return h * d - (start - z);
    }
    return h * d;
  }
}
