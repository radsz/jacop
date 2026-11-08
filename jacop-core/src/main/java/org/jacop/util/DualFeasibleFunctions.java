/*
 * DualFeasibleFunctions.java
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

package org.jacop.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Integer dual feasible functions (DFFs) and the two-dimensional orthogonal packing test built on
 * them.
 *
 * <p>A function f from [0, C] to the non-negative integers is dual feasible for capacity C when
 * every set of sizes with sum at most C keeps a sum at most f(C) after the mapping. Fekete and
 * Schepers showed that a pair of such functions, one per dimension, keeps a packing a packing:
 * rectangles w_i x h_i that fit without overlap in a W x H container still satisfy {@code sum_i
 * f1(w_i) * f2(h_i) <= f1(W) * f2(H)}. The plain area test is the case of two identities; a pair
 * that rounds large items up and drops small ones fails on sets whose area fits but which cannot be
 * packed.
 *
 * <p>The functions here, each scaled to integers so that the test stays exact:
 *
 * <ul>
 *   <li>{@link #fs1(int, int, int) u^(k)} and {@link #fs2(int, int, int) U^(e)} of Fekete and
 *       Schepers [1];
 *   <li>{@link #ccm1(int, int, int) f_CCM1} of Carlier, Clautiaux and Moukrim [3], which {@code
 *       Binpacking} also uses for its bin-count bound.
 * </ul>
 *
 * <p>{@link #packingFails} tries the pairs of these functions [2], as Clautiaux, Jouglet, Carlier
 * and Moukrim do in their constraint programming approach to orthogonal packing [4]. It first skips
 * the sets that Steinberg's theorem [5] proves packable, on which no such test can fail.
 *
 * <p>References:
 *
 * <ol>
 *   <li>S. P. Fekete and J. Schepers. New classes of fast lower bounds for bin packing problems.
 *       Mathematical Programming 91(1):11-31, 2001. doi:10.1007/s101070100243
 *   <li>S. P. Fekete and J. Schepers. A general framework for bounds for higher-dimensional
 *       orthogonal packing problems. Mathematical Methods of Operations Research 60(2):311-329,
 *       2004. doi:10.1007/s001860400376
 *   <li>J. Carlier, F. Clautiaux and A. Moukrim. New reduction procedures and lower bounds for the
 *       two-dimensional bin packing problem with fixed orientation. Computers and Operations
 *       Research 34(8):2223-2250, 2007. doi:10.1016/j.cor.2005.08.012
 *   <li>F. Clautiaux, A. Jouglet, J. Carlier and A. Moukrim. A new constraint programming approach
 *       for the orthogonal packing problem. Computers and Operations Research 35(3):944-959, 2008.
 *       doi:10.1016/j.cor.2006.05.012
 *   <li>A. Steinberg. A strip-packing algorithm with absolute performance bound 2. SIAM Journal on
 *       Computing 26(2):401-409, 1997. doi:10.1137/S0097539793255801
 *   <li>J. Carlier and E. Néron. Computing redundant resources for the resource constrained project
 *       scheduling problem. European Journal of Operational Research 176(3):1452-1463, 2007.
 *       doi:10.1016/j.ejor.2005.09.034
 * </ol>
 *
 * <p>{@link #redundantResources} picks, for one cumulative resource, the functions whose mapped
 * uses form redundant resources in the sense of Carlier and Néron [6]: tasks that run together use
 * at most C, so their mapped uses sum to at most f(C), and a cumulative constraint over the mapped
 * uses and capacity f(C) holds in every solution. Its time table is never stronger than the
 * original one, but its energy rules can be: three tasks that each use 0.4 C cannot all overlap,
 * and u^(2) maps each of them to C / 2.
 *
 * <p>An instance is not thread safe: it keeps work arrays between calls.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class DualFeasibleFunctions {

  /** The largest container side tested; above it the products could overflow a long. */
  public static final int MAX_SIDE = 1 << 20;

  /** The most parameters tried for each of U^(e) and f_CCM1 in a dimension. */
  static final int MAX_PARAMETERS = 4;

  /** The parameters k tried for u^(k). */
  static final int MAX_K = 3;

  private static final int IDENTITY = 0;
  private static final int FS1 = 1;
  private static final int FS2 = 2;
  private static final int CCM1 = 3;

  private static final int MAX_FUNCTIONS = 1 + MAX_K + 2 * MAX_PARAMETERS;

  // per dimension: the functions (kind, parameter), f(C), and the mapped sizes
  private final int[][] kind = new int[2][MAX_FUNCTIONS];
  private final int[][] parameter = new int[2][MAX_FUNCTIONS];
  private final long[][] capacity = new long[2][MAX_FUNCTIONS];
  private final int[] count = new int[2];
  private final long[][][] mapped = new long[2][MAX_FUNCTIONS][0];
  private final int[][] sizes = {new int[0], new int[0]};
  private int[] distinct = new int[0];

  /** Number of tests that got past Steinberg's theorem, for statistics. */
  public long tests;

  /** Number of tests that failed, for statistics. */
  public long failures;

  /**
   * The dual feasible function u^(k) of Fekete and Schepers [1], scaled by C * k: {@code x * k} if
   * {@code (k + 1) * x} is a multiple of C, and {@code floor((k + 1) * x / C) * C} otherwise. It
   * maps C to C * k.
   *
   * @param x a size in [0, c].
   * @param c the capacity.
   * @param k the parameter, at least 1.
   * @return the mapped size.
   */
  public static long fs1(int x, int c, int k) {
    long t = (long) (k + 1) * x;
    if (t % c == 0) {
      return (long) x * k;
    }
    return t / c * c;
  }

  /**
   * The dual feasible function U^(e) of Fekete and Schepers [1]: C for a size above C - e, the size
   * itself from e to C - e, and 0 below e. It maps C to C.
   *
   * @param x a size in [0, c].
   * @param c the capacity.
   * @param e the parameter, from 1 to c / 2.
   * @return the mapped size.
   */
  public static long fs2(int x, int c, int e) {
    if (x > c - e) {
      return c;
    }
    return x < e ? 0 : x;
  }

  /**
   * The dual feasible function f_CCM1 of Carlier, Clautiaux and Moukrim [3]: {@code 2 * (floor(C /
   * l) - floor((C - x) / l))} for a size above C / 2, {@code floor(C / l)} for exactly C / 2, and
   * {@code 2 * floor(x / l)} below C / 2. It maps C to {@code 2 * floor(C / l)}.
   *
   * @param x a size in [0, c].
   * @param c the capacity.
   * @param lambda the parameter, from 1 to c / 2.
   * @return the mapped size.
   */
  public static long ccm1(int x, int c, int lambda) {
    int rest = c - x;
    if (x > rest) {
      return 2L * (c / lambda - rest / lambda);
    } else if (x == rest) {
      return c / lambda;
    }
    return 2L * (x / lambda);
  }

  /**
   * Tells whether a pair of the dual feasible functions shows that the rectangles cannot be packed
   * without overlap in a container, by Fekete and Schepers' condition [2]. Rectangles with a side 0
   * are ignored, and the plain area test is included. Containers with a side above {@link
   * #MAX_SIDE} are not tested.
   *
   * @param width the container's width.
   * @param height the container's height.
   * @param w the rectangles' widths, each at most width.
   * @param h the rectangles' heights, each at most height.
   * @param n the number of rectangles, the first n of w and h.
   * @return true if the rectangles cannot be packed; false says nothing.
   */
  public boolean packingFails(int width, int height, int[] w, int[] h, int n) {
    if (width <= 0 || height <= 0 || width > MAX_SIDE || height > MAX_SIDE) {
      return false;
    }
    if (sizes[0].length < n) {
      sizes[0] = new int[n];
      sizes[1] = new int[n];
    }
    int[] cw = sizes[0];
    int[] ch = sizes[1];
    int m = 0;
    long area = 0;
    int wMax = 0;
    int hMax = 0;
    for (int i = 0; i < n; i++) {
      if (w[i] > 0 && h[i] > 0) {
        cw[m] = w[i];
        ch[m++] = h[i];
        area += (long) w[i] * h[i];
        wMax = Math.max(wMax, w[i]);
        hMax = Math.max(hMax, h[i]);
      }
    }
    long space = (long) width * height;
    if (area > space) {
      return true;
    }
    // Steinberg [5]: such rectangles can be packed, so no necessary condition fails
    long corner = (long) Math.max(2 * wMax - width, 0) * Math.max(2 * hMax - height, 0);
    if (2 * area <= space - corner) {
      return false;
    }
    tests++;
    functions(0, width, cw, m);
    functions(1, height, ch, m);
    long[][] mx = mapped[0];
    long[][] my = mapped[1];
    for (int a = 0; a < count[0]; a++) {
      long[] fx = mx[a];
      for (int b = 0; b < count[1]; b++) {
        if (kind[0][a] == IDENTITY && kind[1][b] == IDENTITY) {
          continue;
        }
        long[] fy = my[b];
        long sum = 0;
        for (int i = 0; i < m; i++) {
          sum += fx[i] * fy[i];
        }
        if (sum > capacity[0][a] * capacity[1][b]) {
          failures++;
          return true;
        }
      }
    }
    return false;
  }

  /**
   * One dual feasible function for a cumulative resource of capacity C, as {@link
   * #redundantResources} chooses it.
   */
  public static final class Resource {

    private final int kind;
    private final int parameter;
    private final int c;
    private final double gain;

    Resource(int kind, int parameter, int c, double gain) {
      this.kind = kind;
      this.parameter = parameter;
      this.c = c;
      this.gain = gain;
    }

    /**
     * The capacity the function maps C to.
     *
     * @return f(C).
     */
    public long capacity() {
      return map(c);
    }

    /**
     * The mapped use. The function is non-decreasing; uses below 0 count as 0 and uses above C as
     * C, which keeps the resource redundant since a task that uses more than C has length 0 in
     * every solution.
     *
     * @param x a resource use.
     * @return f(x).
     */
    public long map(int x) {
      int y = Math.max(0, Math.min(x, c));
      switch (kind) {
        case FS1:
          return fs1(y, c, parameter);
        case FS2:
          return fs2(y, c, parameter);
        case CCM1:
          return ccm1(y, c, parameter);
        default:
          return y;
      }
    }

    /**
     * The energy the mapped uses add over the plain ones, summed over the tasks the function does
     * not map to 0, in units of C / (C * f(C)): {@code sum_j p_j * max(0, f(r_j) * C - r_j *
     * f(C))}.
     *
     * @return the gain used to rank the functions, 0 before ranking.
     */
    public double gain() {
      return gain;
    }

    @Override
    public String toString() {
      String name =
          switch (kind) {
            case FS1 -> "u^(" + parameter + ")";
            case FS2 -> "U^(" + parameter + ")";
            case CCM1 -> "f_CCM1(" + parameter + ")";
            default -> "id";
          };
      return name + " C=" + c + " f(C)=" + capacity();
    }
  }

  /** The largest k tried for u^(k) by {@link #redundantResources}. */
  static final int MAX_K_RESOURCE = 16;

  /**
   * Chooses dual feasible functions that turn a cumulative resource into redundant resources, as
   * Carlier and Néron do for the resource constrained project scheduling problem [6]. It tries
   * u^(k) for k up to 16 and U^(e) and f_CCM1 for every parameter that changes the mapping (with
   * f(C) at most {@link #MAX_SIDE}), keeps a function only if it maps some task's use to a larger
   * share of the capacity than the plain one ({@link Resource#gain()} &gt; 0), and does not map
   * every use to 0 or f(C) (a set of pairwise disjoint tasks, which disjunctive reasoning covers),
   * drops the functions that another kept function dominates on these uses, and returns at most
   * {@code max} of the rest, the largest gain first.
   *
   * @param uses the smallest resource use of each task, each from 0 to c.
   * @param lengths the smallest length of each task.
   * @param c the capacity, from 2 to {@link #MAX_SIDE}.
   * @param max the most functions returned.
   * @return the chosen functions; empty when none adds anything.
   */
  public static List<Resource> redundantResources(int[] uses, int[] lengths, int c, int max) {
    List<Resource> result = new ArrayList<>();
    int n = uses.length;
    if (c < 2 || c > MAX_SIDE || max <= 0 || n < 2) {
      return result;
    }
    List<Resource> candidates = new ArrayList<>();
    int half = c / 2;
    for (int k = 1; k <= MAX_K_RESOURCE && k <= half; k++) {
      candidates.add(new Resource(FS1, k, c, 0));
    }
    int[] lower = new int[n];
    int[] upper = new int[n];
    int nl = 0;
    int nu = 0;
    for (int x : uses) {
      if (x >= 1 && x <= half) {
        lower[nl++] = x;
        upper[nu++] = x;
      } else if (x > half && c - x + 1 <= half) {
        upper[nu++] = c - x + 1;
      }
    }
    for (int p : distinctSorted(lower, nl)) {
      candidates.add(new Resource(CCM1, p, c, 0));
    }
    for (int p : distinctSorted(upper, nu)) {
      candidates.add(new Resource(FS2, p, c, 0));
    }
    List<long[]> vectors = new ArrayList<>();
    List<Resource> scored = new ArrayList<>();
    for (Resource f : candidates) {
      long cap = f.capacity();
      if (cap > MAX_SIDE) {
        continue;
      }
      long[] v = new long[n];
      double gain = 0;
      boolean between = false;
      for (int j = 0; j < n; j++) {
        v[j] = f.map(uses[j]);
        if (v[j] > 0 && v[j] < cap) {
          between = true;
        }
        long d = v[j] * c - (long) uses[j] * cap;
        if (v[j] > 0 && d > 0) {
          gain += (double) d * Math.max(lengths[j], 0);
        }
      }
      if (gain > 0 && between) {
        scored.add(new Resource(f.kind, f.parameter, c, gain));
        vectors.add(v);
      }
    }
    // a function whose every mapped share is at most another's adds nothing to that other one
    int m = scored.size();
    boolean[] dropped = new boolean[m];
    for (int a = 0; a < m; a++) {
      for (int b = 0; b < m && !dropped[a]; b++) {
        if (a != b
            && !dropped[b]
            && dominates(
                vectors.get(b),
                scored.get(b).capacity(),
                vectors.get(a),
                scored.get(a).capacity(),
                b < a)) {
          dropped[a] = true;
        }
      }
    }
    for (int a = 0; a < m; a++) {
      if (!dropped[a]) {
        result.add(scored.get(a));
      }
    }
    result.sort((x, y) -> Double.compare(y.gain, x.gain));
    return result.size() > max ? new ArrayList<>(result.subList(0, max)) : result;
  }

  // whether a / capA >= b / capB everywhere; equal shares count as domination only when tie is set,
  // so that of two functions with the same shares one is kept
  private static boolean dominates(long[] a, long capA, long[] b, long capB, boolean tie) {
    boolean strict = false;
    for (int j = 0; j < a.length; j++) {
      long l = a[j] * capB;
      long r = b[j] * capA;
      if (l < r) {
        return false;
      }
      if (l > r) {
        strict = true;
      }
    }
    return strict || tie;
  }

  private static int[] distinctSorted(int[] values, int n) {
    return Arrays.stream(values, 0, n).distinct().sorted().toArray();
  }

  // the functions tried in dimension d for the n sizes s (all positive) and capacity c, and the
  // sizes they map to
  private void functions(int d, int c, int[] s, int n) {
    int m = 0;
    kind[d][m++] = IDENTITY;
    if (c / 2 > 0) {
      for (int k = 1; k <= MAX_K; k++) {
        kind[d][m] = FS1;
        parameter[d][m++] = k;
      }
      // the parameters that change the mapping, the largest first: the sizes up to c / 2, and
      // for U^(e) also c - x + 1 for a size x above c / 2
      int nd = thresholds(c, s, n, false);
      for (int i = nd - 1; i >= 0 && i >= nd - MAX_PARAMETERS; i--) {
        kind[d][m] = CCM1;
        parameter[d][m++] = distinct[i];
      }
      nd = thresholds(c, s, n, true);
      for (int i = nd - 1; i >= 0 && i >= nd - MAX_PARAMETERS; i--) {
        kind[d][m] = FS2;
        parameter[d][m++] = distinct[i];
      }
    }
    // the mapped sizes; a function that maps these sizes as the identity does, up to scale, gives
    // the same test as the identity and is dropped
    int kept = 0;
    for (int f = 0; f < m; f++) {
      int fk = kind[d][f];
      int p = parameter[d][f];
      kind[d][kept] = fk;
      parameter[d][kept] = p;
      if (mapped[d][kept].length < n) {
        mapped[d][kept] = new long[Math.max(n, 2 * mapped[d][kept].length)];
      }
      long[] v = mapped[d][kept];
      long cap;
      switch (fk) {
        case FS1:
          cap = (long) c * p;
          for (int i = 0; i < n; i++) {
            v[i] = fs1(s[i], c, p);
          }
          break;
        case FS2:
          cap = c;
          for (int i = 0; i < n; i++) {
            v[i] = fs2(s[i], c, p);
          }
          break;
        case CCM1:
          cap = 2L * (c / p);
          for (int i = 0; i < n; i++) {
            v[i] = ccm1(s[i], c, p);
          }
          break;
        default:
          cap = c;
          for (int i = 0; i < n; i++) {
            v[i] = s[i];
          }
      }
      capacity[d][kept] = cap;
      if (fk == IDENTITY || !proportional(v, s, n, cap, c)) {
        kept++;
      }
    }
    count[d] = kept;
  }

  // whether v[i] / cap = s[i] / c for every i
  private static boolean proportional(long[] v, int[] s, int n, long cap, int c) {
    for (int i = 0; i < n; i++) {
      if (v[i] * c != s[i] * cap) {
        return false;
      }
    }
    return true;
  }

  // the distinct parameters from 1 to c / 2 in ascending order, into distinct; returns their number
  private int thresholds(int c, int[] s, int n, boolean complements) {
    if (distinct.length < n) {
      distinct = new int[n];
    }
    int half = c / 2;
    int m = 0;
    for (int i = 0; i < n; i++) {
      int x = s[i];
      if (x <= half) {
        distinct[m++] = x;
      } else if (complements && c - x + 1 <= half) {
        distinct[m++] = c - x + 1;
      }
    }
    Arrays.sort(distinct, 0, m);
    int u = 0;
    for (int i = 0; i < m; i++) {
      if (u == 0 || distinct[u - 1] != distinct[i]) {
        distinct[u++] = distinct[i];
      }
    }
    return u;
  }
}
