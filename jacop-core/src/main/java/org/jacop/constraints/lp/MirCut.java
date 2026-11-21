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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

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

  // whether a cut with weights too large or too far apart is scaled down instead of dropped
  static final boolean REDUCE_CUTS = !"false".equals(System.getProperty("org.jacop.lp.reduceCuts"));

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

  /** The separator the cut came from (see {@link LpSources}), or null. */
  String source;

  private MirCut(int[] columns, long[] weights, long rhs, double efficacy, double norm) {
    this.columns = columns;
    this.weights = weights;
    this.rhs = rhs;
    this.efficacy = efficacy;
    this.norm = norm;
  }

  /**
   * Returns a cut {@code sum weights x <= rhs} found by other means than the MIR, such as a rounded
   * capacity cut, to be added like the MIR cuts.
   *
   * @param columns the columns, ascending
   * @param weights the weight of each column
   * @param rhs the side
   * @param efficacy the violation by the LP solution over the norm of the cut
   * @return the cut
   */
  static MirCut row(int[] columns, long[] weights, long rhs, double efficacy) {
    double norm = 0;
    for (long w : weights) {
      norm += (double) w * w;
    }
    return new MirCut(columns, weights, rhs, efficacy, Math.sqrt(norm));
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
    int size = 0;
    for (long w : c) {
      size += w != 0 ? 1 : 0;
    }
    int[] columns = new int[size];
    long[] weights = new long[size];
    for (int j = 0, k = 0; j < c.length; j++) {
      if (c[j] != 0) {
        columns[k] = j;
        weights[k++] = c[j];
      }
    }
    return of(columns, weights, b, value, lo, hi);
  }

  /**
   * Returns the best MIR cut of {@code sum c_k x_columns[k] <= b}, or null when none is violated
   * enough or the arithmetic overflows. The work is linear in the length of the row, not in the
   * number of columns.
   *
   * @param columns the columns of the row, ascending, each once (not changed)
   * @param c the nonzero weights of the columns (not changed)
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

  /**
   * Returns the best MIR cut of {@code sum c_k x_columns[k] <= b} after the substitution of
   * variable bounds (Marchand and Wolsey, "Aggregation and mixed integer rounding to solve MIPs",
   * Operations Research 49(3), 2001; the bound substitution of c-MIR as in SCIP and HiGHS), or null
   * when none is violated enough or the arithmetic overflows. A column {@code x} with a variable
   * upper bound {@code x <= a u} or lower bound {@code x >= a u} over a 0/1 column {@code u} is
   * written as {@code a u - s} or {@code a u + s} with a slack {@code s >= 0}, when that bound is
   * nearer to the LP value of {@code x} than both of its own bounds. The slack is an integer with
   * bounds {@code [0, a - lo(x)]} for an upper and {@code [0, hi(x)]} for a lower bound. The MIR of
   * the substituted row is a cut over the slacks, given back in the columns by {@code s = a u - x}
   * or {@code s = x - a u}. On unit commitment, where the generation of a unit is bounded by its
   * capacity times its commitment, these are the flow cover cuts of the demand rows.
   *
   * @param columns the columns of the row, each once (not changed)
   * @param c the weights of the columns (not changed)
   * @param b the right side
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @param bounds the variable bounds by column
   * @return the cut, or null
   */
  static MirCut ofVariableBounds(
      int[] columns,
      long[] c,
      long b,
      double[] value,
      long[] lo,
      long[] hi,
      VariableBounds bounds) {
    try {
      return variableBoundCut(columns, c, b, value, lo, hi, bounds);
    } catch (ArithmeticException _) {
      return null;
    }
  }

  /** The variable bounds {@code x <= a u} and {@code x >= a u} of columns over 0/1 columns. */
  static final class VariableBounds {
    // by column: the 0/1 columns and factors of its upper and of its lower bounds, or null
    final int[][] upperOver;
    final long[][] upperFactor;
    final int[][] lowerOver;
    final long[][] lowerFactor;
    final int count;

    VariableBounds(
        int[][] upperOver,
        long[][] upperFactor,
        int[][] lowerOver,
        long[][] lowerFactor,
        int count) {
      this.upperOver = upperOver;
      this.upperFactor = upperFactor;
      this.lowerOver = lowerOver;
      this.lowerFactor = lowerFactor;
      this.count = count;
    }

    /**
     * Collects the variable bounds stated by two-column rows {@code x - a u <= 0} (upper) and
     * {@code x - a u >= 0} (lower), in either sign, with {@code a > 0}, u a 0/1 column and x a
     * column with {@code lo >= 0} and {@code hi > 1}.
     *
     * @param n the number of columns
     * @param rows the columns of each row
     * @param weights the weights of each row
     * @param upper the upper side of each row, if any
     * @param lower the lower side of each row, if any
     * @param lo the global lower bounds by column
     * @param hi the global upper bounds by column
     * @return the variable bounds, or null when there are none
     */
    static VariableBounds of(
        int n,
        List<int[]> rows,
        List<long[]> weights,
        List<Long> upper,
        List<Long> lower,
        long[] lo,
        long[] hi) {
      List<List<long[]>> ups = new ArrayList<>(Collections.nCopies(n, null));
      List<List<long[]>> lows = new ArrayList<>(Collections.nCopies(n, null));
      int count = 0;
      for (int i = 0; i < rows.size(); i++) {
        int[] cs = rows.get(i);
        if (cs.length != 2) {
          continue;
        }
        for (int t = 0; t < 2; t++) {
          int x = cs[t];
          int u = cs[1 - t];
          long cx = weights.get(i)[t];
          long cu = weights.get(i)[1 - t];
          if (x >= n
              || u >= n
              || Math.abs(cx) != 1
              || lo[u] != 0
              || hi[u] != 1
              || lo[x] < 0
              || hi[x] <= 1) {
            continue;
          }
          // normalized to x + (cu / cx) u ? 0
          long a = -cu * cx;
          if (a <= 0) {
            continue;
          }
          Long up = upper.get(i);
          Long down = lower.get(i);
          // cx = 1: x - a u <= up; cx = -1: -x + a u <= up, so x - a u >= -up
          Long xUpper = cx == 1 ? up : down == null ? null : -down;
          Long xLower = cx == 1 ? down : up == null ? null : -up;
          if (xUpper != null && xUpper == 0) {
            add(ups, x, u, a);
            count++;
          }
          if (xLower != null && xLower == 0) {
            add(lows, x, u, a);
            count++;
          }
        }
      }
      if (count == 0) {
        return null;
      }
      int[][] uo = new int[n][];
      long[][] uf = new long[n][];
      int[][] lo2 = new int[n][];
      long[][] lf = new long[n][];
      for (int j = 0; j < n; j++) {
        if (ups.get(j) != null) {
          uo[j] = ups.get(j).stream().mapToInt(e -> (int) e[0]).toArray();
          uf[j] = ups.get(j).stream().mapToLong(e -> e[1]).toArray();
        }
        if (lows.get(j) != null) {
          lo2[j] = lows.get(j).stream().mapToInt(e -> (int) e[0]).toArray();
          lf[j] = lows.get(j).stream().mapToLong(e -> e[1]).toArray();
        }
      }
      return new VariableBounds(uo, uf, lo2, lf, count);
    }

    private static void add(List<List<long[]>> list, int x, int u, long a) {
      if (list.get(x) == null) {
        list.set(x, new ArrayList<>(2));
      }
      list.get(x).add(new long[] {u, a});
    }
  }

  private static MirCut variableBoundCut(
      int[] columns,
      long[] c,
      long b,
      double[] value,
      long[] lo,
      long[] hi,
      VariableBounds bounds) {
    int n = columns.length;
    // the substituted row over local terms: a column (kind 0) or the slack of column x over u with
    // factor a, of an upper (kind 1) or a lower (kind 2) bound
    Map<Integer, Integer> local = new HashMap<>();
    List<int[]> terms = new ArrayList<>();
    List<Long> factor = new ArrayList<>();
    List<Long> weight = new ArrayList<>();
    boolean substituted = false;
    for (int t = 0; t < n; t++) {
      int j = columns[t];
      long w = c[t];
      if (w == 0) {
        continue;
      }
      double v = Math.clamp(value[j], (double) lo[j], (double) hi[j]);
      double own = Math.min(v - lo[j], hi[j] - v);
      int kind = 0;
      int over = -1;
      long a = 0;
      double best = own - 1e-9;
      if (j < bounds.upperOver.length && bounds.upperOver[j] != null) {
        for (int k = 0; k < bounds.upperOver[j].length; k++) {
          int u = bounds.upperOver[j][k];
          double d = bounds.upperFactor[j][k] * value[u] - v;
          if (d < best) {
            best = d;
            kind = 1;
            over = u;
            a = bounds.upperFactor[j][k];
          }
        }
      }
      if (j < bounds.lowerOver.length && bounds.lowerOver[j] != null) {
        for (int k = 0; k < bounds.lowerOver[j].length; k++) {
          int u = bounds.lowerOver[j][k];
          double d = v - bounds.lowerFactor[j][k] * value[u];
          if (d < best) {
            best = d;
            kind = 2;
            over = u;
            a = bounds.lowerFactor[j][k];
          }
        }
      }
      if (kind == 0) {
        addTerm(local, terms, factor, weight, j, -1, 0, 0, w);
      } else {
        substituted = true;
        // w x = w a u - w s (upper) or w a u + w s (lower)
        addTerm(local, terms, factor, weight, over, -1, 0, 0, Math.multiplyExact(w, a));
        addTerm(local, terms, factor, weight, j, over, kind, a, kind == 1 ? -w : w);
      }
    }
    if (!substituted) {
      return null;
    }
    int m = terms.size();
    int[] ids = new int[m];
    long[] cs = new long[m];
    double[] lv = new double[m];
    long[] ll = new long[m];
    long[] lh = new long[m];
    for (int q = 0; q < m; q++) {
      int[] term = terms.get(q);
      int j = term[0];
      ids[q] = q;
      cs[q] = weight.get(q);
      if (term[2] == 0) {
        lv[q] = value[j];
        ll[q] = lo[j];
        lh[q] = hi[j];
      } else {
        int u = term[1];
        long a = factor.get(q);
        ll[q] = 0;
        if (term[2] == 1) {
          lv[q] = Math.max(0, a * value[u] - value[j]);
          lh[q] = Math.subtractExact(a, lo[j]);
        } else {
          lv[q] = Math.max(0, value[j] - a * value[u]);
          lh[q] = hi[j];
        }
      }
    }
    long[] g = rawCut(ids, cs, b, lv, ll, lh);
    if (g == null) {
      return null;
    }
    // back in the columns: s = a u - x (upper) or s = x - a u (lower)
    Map<Integer, Long> out = new TreeMap<>();
    for (int q = 0; q < m; q++) {
      if (g[q] == 0) {
        continue;
      }
      int[] term = terms.get(q);
      int j = term[0];
      if (term[2] == 0) {
        out.merge(j, g[q], Math::addExact);
      } else {
        long ga = Math.multiplyExact(g[q], factor.get(q));
        if (term[2] == 1) {
          out.merge(term[1], ga, Math::addExact);
          out.merge(j, -g[q], Math::addExact);
        } else {
          out.merge(j, g[q], Math::addExact);
          out.merge(term[1], -ga, Math::addExact);
        }
      }
    }
    out.values().removeIf(w -> w == 0);
    int[] cutColumns = new int[out.size()];
    long[] cutWeights = new long[out.size()];
    int q = 0;
    for (Map.Entry<Integer, Long> e : out.entrySet()) {
      cutColumns[q] = e.getKey();
      cutWeights[q++] = e.getValue();
    }
    return finishCut(cutColumns, cutWeights, g[m], value, lo, hi, REDUCE_CUTS, 2);
  }

  // adds weight w to the local term of column j (kind 0) or of the slack of j over u (kind 1, 2)
  private static void addTerm(
      Map<Integer, Integer> local,
      List<int[]> terms,
      List<Long> factor,
      List<Long> weight,
      int j,
      int u,
      int kind,
      long a,
      long w) {
    if (kind != 0) {
      terms.add(new int[] {j, u, kind});
      factor.add(a);
      weight.add(w);
      return;
    }
    Integer q = local.get(j);
    if (q == null) {
      local.put(j, terms.size());
      terms.add(new int[] {j, -1, 0});
      factor.add(0L);
      weight.add(w);
    } else {
      weight.set(q, Math.addExact(weight.get(q), w));
    }
  }

  private static MirCut cut(int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi) {
    long[] g = rawCut(columns, c, b, value, lo, hi);
    return g == null ? null : finishCut(columns, g, g[c.length], value, lo, hi, REDUCE_CUTS, 2);
  }

  /**
   * Returns the MIR cut of {@code sum c_k x_columns[k] <= b} over the given columns before the
   * filters on its weights: {@code sum g_k x_columns[k] <= right}, with g aligned with columns
   * (some entries may be zero), or null when none is violated enough or the arithmetic overflows.
   *
   * @param columns the columns of the row, each once (not changed)
   * @param c the weights of the columns (not changed)
   * @param b the right side
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @return {@code {g..., right}}: the weights followed by the right side, or null
   */
  static long[] raw(int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi) {
    return raw(columns, c, b, value, lo, hi, 0);
  }

  /**
   * Returns the MIR cut of {@code sum c_k x_columns[k] <= b} as {@link #raw(int[], long[], long,
   * double[], long[], long[])} does, with one more divisor tried before those of the inside
   * columns: for a row of the tableau, the weight of its basic column, the divisor of the Gomory
   * mixed-integer cut of the row.
   *
   * @param columns the columns of the row, each once (not changed)
   * @param c the weights of the columns (not changed)
   * @param b the right side
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @param first a divisor to try first, or 0 for none
   * @return {@code {g..., right}}: the weights followed by the right side, or null
   */
  static long[] raw(
      int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi, long first) {
    try {
      return rawCut(columns, c, b, value, lo, hi, first);
    } catch (ArithmeticException _) {
      return null;
    }
  }

  private static long[] rawCut(
      int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi) {
    return rawCut(columns, c, b, value, lo, hi, 0);
  }

  private static long[] rawCut(
      int[] columns, long[] c, long b, double[] value, long[] lo, long[] hi, long first) {
    int n = c.length;
    long[] cc = new long[n];
    boolean[] up = new boolean[n];
    double[] xs = new double[n];
    long[] divisor = new long[n];
    double[] inside = new double[n];
    int count = 0;
    long side = b;
    for (int t = 0; t < n; t++) {
      long w = c[t];
      if (w == 0) {
        continue;
      }
      int j = columns[t];
      double v = Math.clamp(value[j], (double) lo[j], (double) hi[j]);
      up[t] = hi[j] - v < v - lo[j];
      if (up[t]) {
        cc[t] = -w;
        side = Math.subtractExact(side, Math.multiplyExact(w, hi[j]));
        xs[t] = hi[j] - v;
      } else {
        cc[t] = w;
        side = Math.subtractExact(side, Math.multiplyExact(w, lo[j]));
        xs[t] = v - lo[j];
      }
      double in = Math.min(v - lo[j], hi[j] - v);
      if (in > 1e-6) {
        divisor[count] = Math.absExact(w);
        inside[count++] = in;
      }
    }
    if (count == 0) {
      return null;
    }
    long d = bestDivisor(cc, side, xs, divisor, inside, count, Math.absExact(first));
    if (d == 0) {
      return null;
    }
    long r = Math.floorMod(side, d);
    long k = d - r;
    long right = Math.multiplyExact(Math.floorDiv(side, d), k);
    long[] g = new long[n + 1];
    for (int t = 0; t < n; t++) {
      if (cc[t] == 0) {
        continue;
      }
      int j = columns[t];
      long gj =
          Math.addExact(
              Math.multiplyExact(Math.floorDiv(cc[t], d), k),
              Math.max(0, Math.floorMod(cc[t], d) - r));
      if (up[t]) {
        g[t] = -gj;
        right = Math.subtractExact(right, Math.multiplyExact(gj, hi[j]));
      } else {
        g[t] = gj;
        right = Math.addExact(right, Math.multiplyExact(gj, lo[j]));
      }
    }
    g[n] = right;
    return g;
  }

  // the divisor of the most efficacious cut among the weights of the inside variables, halved
  private static long bestDivisor(
      long[] cc,
      long side,
      double[] xs,
      long[] divisor,
      double[] inside,
      int count,
      long preferred) {
    Integer[] order = new Integer[count];
    for (int i = 0; i < count; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (p, q) -> Double.compare(inside[q], inside[p]));
    long bestDivisor = 0;
    double best = MIN_EFFICACY;
    long[] tried = new long[MAX_DIVISORS * 4 + 1];
    int triedCount = 0;
    if (preferred > 0) {
      tried[triedCount++] = preferred;
      double e = efficacy(cc, side, xs, preferred);
      if (e > best) {
        best = e;
        bestDivisor = preferred;
      }
    }
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
    return bestDivisor;
  }

  /**
   * Returns the cut {@code sum g_k x_columns[k] <= right}, one term or more, divided by the
   * greatest common divisor of its weights, or null when it is not violated enough by the LP
   * solution or its weights are too large or too far apart. With reduce, weights that are too large
   * or too far apart are scaled down instead (see {@link #reduce}).
   *
   * @param columns the columns, each once (not changed)
   * @param g the weights aligned with columns, some may be zero (not changed)
   * @param right the right side
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @param reduce whether to scale large weights down instead of giving up
   * @return the cut, or null
   */
  static MirCut finish(
      int[] columns, long[] g, long right, double[] value, long[] lo, long[] hi, boolean reduce) {
    try {
      return finishCut(columns, g, right, value, lo, hi, reduce, 1);
    } catch (ArithmeticException _) {
      return null;
    }
  }

  private static MirCut finishCut(
      int[] columns,
      long[] g,
      long right,
      double[] value,
      long[] lo,
      long[] hi,
      boolean reduce,
      int terms) {
    int nonzero = 0;
    long gcd = 0;
    long largest = 0;
    long smallest = Long.MAX_VALUE;
    for (int t = 0; t < columns.length; t++) {
      if (g[t] != 0) {
        nonzero++;
        long a = Math.absExact(g[t]);
        gcd = gcd(gcd, a);
        largest = Math.max(largest, a);
        smallest = Math.min(smallest, a);
      }
    }
    if (nonzero < terms || gcd == 0) {
      return null;
    }
    long[] w = new long[columns.length];
    for (int t = 0; t < columns.length; t++) {
      w[t] = g[t] / gcd;
    }
    // the weights are integers, so the right side rounds down: a Chvatal-Gomory step for free
    long rhs = Math.floorDiv(right, gcd);
    largest /= gcd;
    smallest /= gcd;
    if (reduce && (largest > MAX_WEIGHT || largest > MAX_RATIO * smallest)) {
      // weights below the largest over MAX_RATIO leave the cut at their bounds, then the cut is
      // divided by the least power of two that brings the largest weight within MAX_WEIGHT
      long divisor = 1;
      while (largest / divisor > MAX_WEIGHT) {
        divisor *= 2;
      }
      rhs = reduce(columns, w, rhs, divisor, (double) largest / MAX_RATIO, value, lo, hi);
      return finishCut(columns, w, rhs, value, lo, hi, false, terms);
    }
    int[] cutColumns = new int[nonzero];
    long[] weights = new long[nonzero];
    double activity = 0;
    double norm = 0;
    int q = 0;
    for (int t = 0; t < columns.length; t++) {
      if (w[t] != 0) {
        int j = columns[t];
        cutColumns[q] = j;
        weights[q] = w[t];
        q++;
        double weight = (double) w[t];
        activity += weight * value[j];
        norm += weight * weight;
      }
    }
    double efficacy = (activity - rhs) / Math.sqrt(norm);
    if (!(efficacy > MIN_EFFICACY) || largest > MAX_RATIO * smallest || largest > MAX_WEIGHT) {
      return null;
    }
    return new MirCut(cutColumns, weights, rhs, efficacy, Math.sqrt(norm));
  }

  /**
   * Returns the cut with its weights brought within {@code maxWeight}: the cut itself when they
   * are, otherwise the cut divided by the least power of two that does it, as {@link #reduce} does
   * (exact over the bounds), or null when what is left is not violated enough or the arithmetic
   * overflows. Cuts made in search are capped harder than at the root: their rows enter the integer
   * certificates of every later solve, and weights up to {@code 2^24} make the scaled Farkas
   * multipliers overflow or round into combinations that prove nothing (the 60-item knapsack of
   * PortfolioSplitTest: 70 % of the infeasible solves were left unproven).
   *
   * @param c the cut
   * @param maxWeight the largest weight allowed
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @return the cut, a scaled-down cut, or null
   */
  static MirCut capped(MirCut c, long maxWeight, double[] value, long[] lo, long[] hi) {
    long largest = 0;
    for (long w : c.weights) {
      largest = Math.max(largest, Math.abs(w));
    }
    if (largest <= maxWeight) {
      return c;
    }
    // rounded up, a weight stays within the cap too
    long divisor = 1;
    while (Math.ceilDiv(largest, divisor) > maxWeight) {
      divisor *= 2;
    }
    try {
      long[] w = c.weights.clone();
      long rhs = reduce(c.columns, w, c.rhs, divisor, (double) largest / MAX_RATIO, value, lo, hi);
      MirCut d = finishCut(c.columns, w, rhs, value, lo, hi, false, 1);
      if (d != null) {
        d.source = c.source;
      }
      return d;
    } catch (ArithmeticException _) {
      return null;
    }
  }

  /**
   * Scales {@code sum w_k x_columns[k] <= rhs} down by divisor, exactly and safely: each weight
   * becomes {@code q_k = w_k / divisor} rounded towards the side that keeps the cut tight at the LP
   * solution, and the remainder {@code e_k = w_k - q_k divisor} goes to the right side at the bound
   * where it is smallest ({@code e_k x >= min(e_k lo, e_k hi)}), so that {@code sum q x <=
   * floor((rhs - sum min(e lo, e hi)) / divisor)} holds wherever the cut and the bounds do. Weights
   * that round to zero leave the cut entirely. The weights are replaced in w.
   *
   * @return the new right side
   * @throws ArithmeticException on overflow
   */
  static long reduce(
      int[] columns,
      long[] w,
      long rhs,
      long divisor,
      double least,
      double[] value,
      long[] lo,
      long[] hi) {
    long side = rhs;
    for (int t = 0; t < columns.length; t++) {
      if (w[t] == 0) {
        continue;
      }
      int j = columns[t];
      if (Math.abs((double) w[t]) < least) {
        // w x >= min(w lo, w hi): the term leaves the cut
        side =
            Math.subtractExact(
                side, Math.min(Math.multiplyExact(w[t], lo[j]), Math.multiplyExact(w[t], hi[j])));
        w[t] = 0;
        continue;
      }
      // nearer the lower bound: round down, so e >= 0 and e x >= e lo costs e (x - lo) at x
      boolean nearLo = value[j] - lo[j] <= hi[j] - value[j];
      long q = nearLo ? Math.floorDiv(w[t], divisor) : Math.ceilDiv(w[t], divisor);
      long e = w[t] - q * divisor;
      long rest = Math.min(Math.multiplyExact(e, lo[j]), Math.multiplyExact(e, hi[j]));
      side = Math.subtractExact(side, rest);
      w[t] = q;
    }
    return Math.floorDiv(side, divisor);
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
