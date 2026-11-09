/*
 * LpExactFuzz.java
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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.Locale;
import java.util.Random;
import org.jacop.jalp.RevisedDualSimplex;

/**
 * Differential fuzzer of JaCoP's LP engines (dense DualSimplex, JaLP behind JalpSimplex, and JaLP's
 * RevisedDualSimplex directly) against an exact rational simplex.
 *
 * <p>Each case is a seeded LP of one of several families (random, degenerate, parallel rows and
 * columns, wide scales, equations, big-M rows, infeasible, unbounded) and a seeded sequence of the
 * operations search makes on it: chunked solves with small pivot limits, branching bound changes
 * and backtracks, row bound changes, cuts added and removed, bases saved and restored, copies, and
 * on JaLP new costs with the primal simplex, exact clean-up, presolve and crash bases. After every
 * solve that ends (not at the limit) the answer is checked against the exact reference of the LP as
 * it then stands: the status, the objective, the primal solution, the duals (their Lagrangian bound
 * must reach the optimum), and the Farkas row of an infeasibility (checked exactly).
 *
 * <p>The kit with a command line driver and the campaign results: osolpro
 * benchmarks/jalp-allsolutions. {@link LpSolverExactTest} runs a few hundred cases.
 */
final class LpExactFuzz {

  private LpExactFuzz() {}

  // ---------------------------------------------------------------- exact rationals

  /** An exact rational, normalized with a positive denominator. */
  record Q(BigInteger n, BigInteger d) implements Comparable<Q> {
    static final Q ZERO = new Q(BigInteger.ZERO, BigInteger.ONE);
    static final Q ONE = new Q(BigInteger.ONE, BigInteger.ONE);

    static Q of(BigInteger n, BigInteger d) {
      if (d.signum() == 0) {
        throw new ArithmeticException("zero denominator");
      }
      if (d.signum() < 0) {
        n = n.negate();
        d = d.negate();
      }
      BigInteger g = n.gcd(d);
      if (!g.equals(BigInteger.ONE) && g.signum() != 0) {
        n = n.divide(g);
        d = d.divide(g);
      }
      return new Q(n, n.signum() == 0 ? BigInteger.ONE : d);
    }

    // exactly the value of the double: its significand times a power of two
    static Q of(double v) {
      if (!Double.isFinite(v)) {
        throw new NumberFormatException("not a finite number: " + v);
      }
      if (v == 0) {
        return ZERO;
      }
      long bits = Double.doubleToLongBits(v);
      int exponent = (int) ((bits >> 52) & 0x7ff);
      long significand = bits & 0xfffffffffffffL;
      if (exponent == 0) {
        exponent = 1;
      } else {
        significand |= 1L << 52;
      }
      exponent -= 1075;
      BigInteger n = BigInteger.valueOf(v < 0 ? -significand : significand);
      return exponent >= 0
          ? new Q(n.shiftLeft(exponent), BigInteger.ONE)
          : of(n, BigInteger.ONE.shiftLeft(-exponent));
    }

    Q add(Q o) {
      return of(n.multiply(o.d).add(o.n.multiply(d)), d.multiply(o.d));
    }

    Q sub(Q o) {
      return of(n.multiply(o.d).subtract(o.n.multiply(d)), d.multiply(o.d));
    }

    Q mul(Q o) {
      return n.signum() == 0 || o.n.signum() == 0 ? ZERO : of(n.multiply(o.n), d.multiply(o.d));
    }

    Q div(Q o) {
      return of(n.multiply(o.d), d.multiply(o.n));
    }

    Q neg() {
      return new Q(n.negate(), d);
    }

    int signum() {
      return n.signum();
    }

    double dbl() {
      return new BigDecimal(n)
          .divide(new BigDecimal(d), java.math.MathContext.DECIMAL64)
          .doubleValue();
    }

    @Override
    public int compareTo(Q o) {
      return n.multiply(o.d).compareTo(o.n.multiply(d));
    }
  }

  // ---------------------------------------------------------------- the LP as it stands

  static final double INF = Double.POSITIVE_INFINITY;

  /** min c x, rowLo <= A x <= rowHi, lo <= x <= hi; rows sparse. */
  static final class Lp {
    int n;
    List<int[]> cols = new ArrayList<>();
    List<double[]> vals = new ArrayList<>();
    double[] cost;
    double[] lo;
    double[] hi;
    // bounds of rows, by row; kept in lists so that rows can be added and removed
    List<double[]> rowBounds = new ArrayList<>();

    int m() {
      return cols.size();
    }

    Lp copy() {
      Lp q = new Lp();
      q.n = n;
      q.cols = new ArrayList<>(cols);
      q.vals = new ArrayList<>(vals);
      q.cost = cost.clone();
      q.lo = lo.clone();
      q.hi = hi.clone();
      for (double[] b : rowBounds) {
        q.rowBounds.add(b.clone());
      }
      return q;
    }

    double[][] dense() {
      double[][] a = new double[m()][n];
      for (int i = 0; i < m(); i++) {
        for (int e = 0; e < cols.get(i).length; e++) {
          a[i][cols.get(i)[e]] += vals.get(i)[e];
        }
      }
      return a;
    }

    String dump() {
      StringBuilder b = new StringBuilder();
      b.append("n=").append(n).append(" m=").append(m()).append('\n');
      for (int i = 0; i < m(); i++) {
        b.append("row ").append(i).append(' ').append(Arrays.toString(cols.get(i)));
        b.append(Arrays.toString(vals.get(i)))
            .append(" in ")
            .append(Arrays.toString(rowBounds.get(i)));
        b.append('\n');
      }
      for (int j = 0; j < n; j++) {
        b.append("col ").append(j).append(" c=").append(cost[j]);
        b.append(" [").append(lo[j]).append(", ").append(hi[j]).append("]\n");
      }
      return b.toString();
    }
  }

  // ---------------------------------------------------------------- exact reference

  static final int R_OPTIMAL = 0;
  static final int R_INFEASIBLE = 1;
  static final int R_UNBOUNDED = 3;

  /** The exact answer: status and optimum. */
  record Ref(int status, Q opt) {}

  /**
   * Solves the LP exactly: standard form (every bounded variable shifted, free ones split, boxed
   * ones with a bound row), two phases, Bland's rule, dense rational tableau.
   */
  static Ref exact(Lp p) {
    return exact(p, p.cost, p.lo, p.hi, rowLo(p), rowHi(p));
  }

  static double[] rowLo(Lp p) {
    double[] r = new double[p.m()];
    for (int i = 0; i < r.length; i++) {
      r[i] = p.rowBounds.get(i)[0];
    }
    return r;
  }

  static double[] rowHi(Lp p) {
    double[] r = new double[p.m()];
    for (int i = 0; i < r.length; i++) {
      r[i] = p.rowBounds.get(i)[1];
    }
    return r;
  }

  static Ref exact(Lp p, double[] cost, double[] lo, double[] hi, double[] rlo, double[] rhi) {
    int n = p.n;
    int m = p.m();
    // variables: x then row activities s
    double[] l = concat(lo, rlo, n, m);
    double[] u = concat(hi, rhi, n, m);
    for (int k = 0; k < l.length; k++) {
      if (l[k] > u[k]) {
        return new Ref(R_INFEASIBLE, null);
      }
    }
    Standard s = new Standard(l, u);
    int rows = m + s.boxes;
    Q[][] a = zeros(rows, s.columns + s.boxes);
    Q[] b = zeros(1, rows)[0];
    // rows: sum_j a_ij x_j - s_i = 0
    for (int i = 0; i < m; i++) {
      Q rhs = Q.ZERO;
      int[] c = p.cols.get(i);
      double[] w = p.vals.get(i);
      for (int e = 0; e < c.length; e++) {
        Q aw = Q.of(w[e]);
        rhs = rhs.sub(aw.mul(s.shift[c[e]]));
        s.put(a[i], c[e], aw);
      }
      b[i] = rhs.add(s.shift[n + i]);
      s.put(a[i], n + i, Q.ONE.neg());
    }
    s.boxRows(l, u, a, b, m);
    Q[] c = zeros(1, s.columns + s.boxes)[0];
    Q c0 = Q.ZERO;
    for (int j = 0; j < n; j++) {
      Q cj = Q.of(cost[j]);
      if (cj.signum() != 0) {
        c0 = c0.add(cj.mul(s.shift[j]));
        s.put(c, j, cj);
      }
    }
    Ref r = simplex(a, b, c);
    return r.status == R_OPTIMAL ? new Ref(R_OPTIMAL, r.opt.add(c0)) : r;
  }

  private static double[] concat(double[] x, double[] y, int n, int m) {
    double[] r = new double[n + m];
    System.arraycopy(x, 0, r, 0, n);
    System.arraycopy(y, 0, r, n, m);
    return r;
  }

  private static Q[][] zeros(int rows, int cols) {
    Q[][] a = new Q[rows][cols];
    for (Q[] r : a) {
      Arrays.fill(r, Q.ZERO);
    }
    return a;
  }

  /**
   * The standard form of the variables: variable k = shift + sign * y over its first standard
   * column, a free variable is y - y' over two columns, and each boxed one has a box row with a
   * slack column after all the others.
   */
  private static final class Standard {
    final int[] first;
    final int[] count;
    final Q[] shift;
    final int[] sign;
    final int columns;
    final int boxes;

    Standard(double[] l, double[] u) {
      int v = l.length;
      first = new int[v];
      count = new int[v];
      shift = new Q[v];
      sign = new int[v];
      int y = 0;
      int box = 0;
      for (int k = 0; k < v; k++) {
        first[k] = y;
        count[k] = 1;
        sign[k] = 1;
        if (l[k] > -INF) {
          shift[k] = Q.of(l[k]);
          if (u[k] < INF) {
            box++;
          }
        } else if (u[k] < INF) {
          shift[k] = Q.of(u[k]);
          sign[k] = -1;
        } else {
          shift[k] = Q.ZERO;
          count[k] = 2;
        }
        y += count[k];
      }
      columns = y;
      boxes = box;
    }

    // adds w times variable k to a row over the standard columns
    void put(Q[] row, int k, Q w) {
      row[first[k]] = row[first[k]].add(w.mul(Q.of(sign[k])));
      if (count[k] == 2) {
        row[first[k] + 1] = row[first[k] + 1].sub(w);
      }
    }

    // y + slack = u - l for each boxed variable
    void boxRows(double[] l, double[] u, Q[][] a, Q[] b, int m) {
      int r = m;
      for (int k = 0; k < l.length; k++) {
        if (l[k] > -INF && u[k] < INF) {
          a[r][first[k]] = Q.ONE;
          a[r][columns + r - m] = Q.ONE;
          b[r] = Q.of(u[k]).sub(Q.of(l[k]));
          r++;
        }
      }
    }
  }

  /** min c y, A y = b, y >= 0, solved exactly with two phases and Bland's rule. */
  static Ref simplex(Q[][] a0, Q[] b0, Q[] c) {
    int m = a0.length;
    int n = c.length;
    int w = n + m; // with artificials
    Q[][] t = new Q[m + 1][];
    int[] basis = new int[m];
    for (int i = 0; i < m; i++) {
      t[i] = tableauRow(a0[i], b0[i], i, n, w);
      basis[i] = n + i;
    }
    // phase 1: minimize the sum of the artificials
    Q[] obj = zeros(1, w + 1)[0];
    for (int i = 0; i < m; i++) {
      subtract(obj, Q.ONE, t[i], n);
      obj[w] = obj[w].sub(t[i][w]);
    }
    t[m] = obj; // reduced costs; t[m][w] = -objective
    if (!iterate(t, basis, m, w, w)) {
      throw new IllegalStateException("phase 1 unbounded");
    }
    if (t[m][w].signum() != 0) {
      return new Ref(R_INFEASIBLE, null);
    }
    // drive artificials out of the basis
    for (int i = 0; i < m; i++) {
      int q = basis[i] >= n ? firstNonzero(t[i], n) : -1;
      if (q >= 0) {
        pivot(t, basis, i, q, m, w);
      }
    }
    // phase 2 over the columns 0..n-1 only (artificials barred)
    Q[] z = zeros(1, w + 1)[0];
    System.arraycopy(c, 0, z, 0, n);
    for (int i = 0; i < m; i++) {
      int p = basis[i];
      if (p < n && c[p].signum() != 0) {
        subtract(z, c[p], t[i], w + 1);
      }
    }
    t[m] = z;
    if (!iterate(t, basis, m, w, n)) {
      return new Ref(R_UNBOUNDED, null);
    }
    return new Ref(R_OPTIMAL, t[m][w].neg());
  }

  // row i of the first tableau: the row with b >= 0, then its artificial, then b
  private static Q[] tableauRow(Q[] a, Q b, int i, int n, int w) {
    boolean neg = b.signum() < 0;
    Q[] row = new Q[w + 1];
    for (int j = 0; j < n; j++) {
      row[j] = neg ? a[j].neg() : a[j];
    }
    for (int j = n; j < w; j++) {
      row[j] = j - n == i ? Q.ONE : Q.ZERO;
    }
    row[w] = neg ? b.neg() : b;
    return row;
  }

  // x[j] -= f * y[j] for j below len
  private static void subtract(Q[] x, Q f, Q[] y, int len) {
    for (int j = 0; j < len; j++) {
      if (y[j].signum() != 0) {
        x[j] = x[j].sub(f.mul(y[j]));
      }
    }
  }

  private static int firstNonzero(Q[] row, int len) {
    for (int j = 0; j < len; j++) {
      if (row[j].signum() != 0) {
        return j;
      }
    }
    return -1;
  }

  // Bland's rule over the columns below allowed; false when unbounded
  private static boolean iterate(Q[][] t, int[] basis, int m, int w, int allowed) {
    while (true) {
      int q = -1;
      for (int j = 0; j < allowed && q < 0; j++) {
        if (t[m][j].signum() < 0) {
          q = j;
        }
      }
      if (q < 0) {
        return true;
      }
      int r = leaving(t, basis, q, m, w);
      if (r < 0) {
        return false;
      }
      pivot(t, basis, r, q, m, w);
    }
  }

  // the row of the smallest ratio, the smallest basic column on ties; -1 when none
  private static int leaving(Q[][] t, int[] basis, int q, int m, int w) {
    int r = -1;
    Q best = null;
    for (int i = 0; i < m; i++) {
      if (t[i][q].signum() > 0) {
        Q ratio = t[i][w].div(t[i][q]);
        int cmp = best == null ? -1 : ratio.compareTo(best);
        if (cmp < 0 || (cmp == 0 && basis[i] < basis[r])) {
          best = ratio;
          r = i;
        }
      }
    }
    return r;
  }

  private static void pivot(Q[][] t, int[] basis, int r, int q, int m, int w) {
    Q piv = t[r][q];
    for (int j = 0; j <= w; j++) {
      if (t[r][j].signum() != 0) {
        t[r][j] = t[r][j].div(piv);
      }
    }
    for (int i = 0; i <= m; i++) {
      if (i != r && t[i][q].signum() != 0) {
        subtract(t[i], t[i][q], t[r], w + 1);
      }
    }
    basis[r] = q;
  }

  /** Whether the LP has a ray: d in the recession cone of the bounds with c d < 0. */
  static boolean dualInfeasible(Lp p) {
    double[] lo = new double[p.n];
    double[] hi = new double[p.n];
    for (int j = 0; j < p.n; j++) {
      lo[j] = p.lo[j] > -INF ? 0 : -1;
      hi[j] = p.hi[j] < INF ? 0 : 1;
    }
    double[] rlo = new double[p.m()];
    double[] rhi = new double[p.m()];
    for (int i = 0; i < p.m(); i++) {
      rlo[i] = p.rowBounds.get(i)[0] > -INF ? 0 : -INF;
      rhi[i] = p.rowBounds.get(i)[1] < INF ? 0 : INF;
    }
    Ref r = exact(p, p.cost, lo, hi, rlo, rhi);
    return r.status == R_OPTIMAL && r.opt.signum() < 0;
  }

  /**
   * The interval of y (A x - s) over the bounds, exactly: a Farkas row proves infeasibility when it
   * excludes 0. Returns {min, max} with null for an infinite end.
   */
  static Q[] farkasRange(Lp p, double[] y) {
    double size = size(p, y);
    Q[] coef = combination(p, y, new Q[p.n], false);
    Q min = Q.ZERO;
    Q max = Q.ZERO;
    boolean minInf = false;
    boolean maxInf = false;
    for (int k = 0; k < p.n + p.m(); k++) {
      Q a = coefficient(p, coef, y, k, true);
      if (negligible(a, size)) {
        continue;
      }
      double forMin = a.signum() > 0 ? lower(p, k) : upper(p, k);
      double forMax = a.signum() > 0 ? upper(p, k) : lower(p, k);
      if (Double.isInfinite(forMin)) {
        minInf = true;
      } else {
        min = min.add(a.mul(Q.of(forMin)));
      }
      if (Double.isInfinite(forMax)) {
        maxInf = true;
      } else {
        max = max.add(a.mul(Q.of(forMax)));
      }
    }
    return new Q[] {minInf ? null : min, maxInf ? null : max};
  }

  // start (zero where null) plus, or with subtract minus, the rows combined with multipliers y
  private static Q[] combination(Lp p, double[] y, Q[] start, boolean subtract) {
    Q[] coef = new Q[p.n];
    for (int j = 0; j < p.n; j++) {
      coef[j] = start[j] == null ? Q.ZERO : start[j];
    }
    for (int i = 0; i < p.m() && i < y.length; i++) {
      if (y[i] == 0) {
        continue;
      }
      Q yi = Q.of(subtract ? -y[i] : y[i]);
      for (int e = 0; e < p.cols.get(i).length; e++) {
        int j = p.cols.get(i)[e];
        coef[j] = coef[j].add(yi.mul(Q.of(p.vals.get(i)[e])));
      }
    }
    return coef;
  }

  // the coefficient of column k, or of the activity of row k - n (y or -y)
  private static Q coefficient(Lp p, Q[] coef, double[] y, int k, boolean negate) {
    if (k < p.n) {
      return coef[k];
    }
    int i = k - p.n;
    if (i >= y.length) {
      return Q.ZERO;
    }
    return Q.of(negate ? -y[i] : y[i]);
  }

  private static double lower(Lp p, int k) {
    return k < p.n ? p.lo[k] : p.rowBounds.get(k - p.n)[0];
  }

  private static double upper(Lp p, int k) {
    return k < p.n ? p.hi[k] : p.rowBounds.get(k - p.n)[1];
  }

  // a coefficient left by round-off in the combination
  private static boolean negligible(Q a, double size) {
    return a.signum() == 0 || Math.abs(a.dbl()) <= 1e-9 * size;
  }

  // the magnitude of a combination of the rows with multipliers y (and of the costs)
  static double size(Lp p, double[] y) {
    double s = 1;
    for (double c : p.cost) {
      s = Math.max(s, Math.abs(c));
    }
    for (int i = 0; i < p.m() && i < y.length; i++) {
      for (double v : p.vals.get(i)) {
        s += Math.abs(y[i] * v);
      }
    }
    return s;
  }

  /** The Lagrangian bound of duals y: min over the bounds of c x - y (A x - s). */
  static Q lagrangian(Lp p, double[] y) {
    double size = size(p, y);
    Q[] start = new Q[p.n];
    for (int j = 0; j < p.n; j++) {
      start[j] = Q.of(p.cost[j]);
    }
    Q[] d = combination(p, y, start, true);
    Q bound = Q.ZERO;
    for (int k = 0; k < p.n + p.m(); k++) {
      Q a = coefficient(p, d, y, k, false);
      if (negligible(a, size)) {
        continue;
      }
      double at = a.signum() > 0 ? lower(p, k) : upper(p, k);
      if (Double.isInfinite(at)) {
        return null;
      }
      bound = bound.add(a.mul(Q.of(at)));
    }
    return bound;
  }

  // ---------------------------------------------------------------- generators

  static final String RANDOM = "random";
  static final String DEGENERATE = "degenerate";
  static final String PARALLEL = "parallel";
  static final String SCALES = "scales";
  static final String EQUATIONS = "equations";
  static final String BIGM = "bigm";
  static final String INFEASIBLE = "infeasible";
  static final String UNBOUNDED = "unbounded";
  static final String TINY = "tiny";
  static final String KNAPSACK = "knapsack";

  static final String[] FAMILIES = {
    RANDOM, DEGENERATE, PARALLEL, SCALES, EQUATIONS, BIGM, INFEASIBLE, UNBOUNDED, TINY, KNAPSACK
  };

  /** Numbers 0..n-1 taken out at random one by one. */
  private static final class Pool {
    final int[] left;
    int size;

    Pool(int n) {
      left = new int[n];
      for (int j = 0; j < n; j++) {
        left[j] = j;
      }
      size = n;
    }

    int take(Random rnd) {
      int i = rnd.nextInt(size);
      int v = left[i];
      System.arraycopy(left, i + 1, left, i, size - i - 1);
      size--;
      return v;
    }
  }

  static Lp generate(Random rnd, String family, boolean bounded) {
    Lp p = new Lp();
    int n = 2 + rnd.nextInt(TINY.equals(family) ? 3 : 12);
    int m = 1 + rnd.nextInt(TINY.equals(family) ? 3 : 10);
    p.n = n;
    p.cost = new double[n];
    p.lo = new double[n];
    p.hi = new double[n];
    double[] x0 = new double[n]; // a point most rows are built around
    for (int j = 0; j < n; j++) {
      x0[j] = column(p, j, rnd, family, bounded);
    }
    for (int i = 0; i < m; i++) {
      row(p, x0, rnd, family);
    }
    if (PARALLEL.equals(family) && rnd.nextBoolean()) {
      parallelColumn(p, rnd);
    }
    if (INFEASIBLE.equals(family) && p.m() > 0) {
      contradictingRow(p, rnd);
    }
    if (UNBOUNDED.equals(family)) {
      int j = rnd.nextInt(n);
      p.lo[j] = -INF;
      p.hi[j] = INF;
      p.cost[j] = rnd.nextBoolean() ? 1 : -1;
    }
    if (rnd.nextInt(8) == 0) {
      Arrays.fill(p.cost, 0); // satisfaction: feasibility only, as in JaCoP without an objective
    }
    return p;
  }

  // the bounds and cost of column j; returns its value in the point the rows are built around
  private static double column(Lp p, int j, Random rnd, String family, boolean bounded) {
    int l = rnd.nextInt(11) - 5;
    int w = rnd.nextInt(8);
    // 0 boxed, 1 fixed, 2 no upper bound, 3 no lower bound, 4 free
    int kind;
    if (!bounded) {
      kind = rnd.nextInt(5);
    } else {
      kind = rnd.nextInt(6) == 0 ? 1 : 0;
    }
    p.lo[j] = kind == 3 || kind == 4 ? -INF : l;
    if (kind == 2 || kind == 4) {
      p.hi[j] = INF;
    } else {
      p.hi[j] = kind == 1 ? l : (double) l + w;
    }
    if (BIGM.equals(family) && rnd.nextBoolean()) {
      p.lo[j] = 0;
      p.hi[j] = 1;
    }
    double x = pointIn(p.lo[j], p.hi[j], rnd);
    p.cost[j] = (double) rnd.nextInt(11) - 5;
    return x;
  }

  // an integer point in [lo, hi], near the finite bound when the other one is infinite
  private static double pointIn(double lo, double hi, Random rnd) {
    if (lo > -INF && hi < INF) {
      return lo + rnd.nextInt((int) (hi - lo) + 1);
    }
    if (lo > -INF) {
      return lo + rnd.nextInt(4);
    }
    if (hi < INF) {
      return hi - rnd.nextInt(4);
    }
    return (double) rnd.nextInt(9) - 4;
  }

  // a row over a few columns, its bounds through or near x0, and maybe a parallel row
  private static void row(Lp p, double[] x0, Random rnd, String family) {
    double rs = SCALES.equals(family) ? Math.pow(10, rnd.nextInt(9) - 4.0) : 1;
    int k = 1 + rnd.nextInt(Math.min(p.n, 6));
    int[] c = new int[k];
    double[] v = new double[k];
    double act = coefficients(c, v, x0, rnd, family, rs);
    Arrays.sort(c);
    p.cols.add(c);
    p.vals.add(v);
    // 0 at least b, 1 at most b, 2 equal to b, 3 ranged
    int kind = rnd.nextInt(4);
    boolean through = DEGENERATE.equals(family) || EQUATIONS.equals(family) || rnd.nextInt(3) == 0;
    double b = through ? act : (rnd.nextInt(21) - 10) * rs;
    if (EQUATIONS.equals(family) && rnd.nextInt(4) != 0) {
      kind = 2;
    }
    if (KNAPSACK.equals(family)) {
      kind = 1;
      b = rnd.nextInt(60);
    }
    double lo = kind == 1 ? -INF : b;
    double hi =
        switch (kind) {
          case 0 -> INF;
          case 2 -> b;
          default -> {
            double ranged = b + rnd.nextInt(4) * rs;
            yield kind == 1 ? b : ranged;
          }
        };
    p.rowBounds.add(new double[] {lo, hi});
    if (PARALLEL.equals(family) && rnd.nextBoolean()) {
      parallelRow(p, c, v, lo, hi, rnd);
    }
  }

  // the columns and weights of a row, drawn at random; returns its activity at x0
  private static double coefficients(
      int[] c, double[] v, double[] x0, Random rnd, String family, double rs) {
    Pool pool = new Pool(x0.length);
    double act = 0;
    for (int e = 0; e < c.length; e++) {
      c[e] = pool.take(rnd);
      int a = rnd.nextInt(19) - 9;
      if (a == 0) {
        a = 1;
      }
      v[e] = a * rs;
      if (BIGM.equals(family) && e == 0 && rnd.nextBoolean()) {
        v[e] = -1000 * rs;
      }
      if (KNAPSACK.equals(family)) {
        v[e] = 1.0 + rnd.nextInt(50);
      }
      act += v[e] * x0[c[e]];
    }
    return act;
  }

  // a multiple of a row, possibly with other bounds
  private static void parallelRow(Lp p, int[] c, double[] v, double lo, double hi, Random rnd) {
    double f = (double) rnd.nextInt(7) - 3;
    if (f == 0) {
      f = 2;
    }
    double[] v2 = v.clone();
    for (int e = 0; e < v2.length; e++) {
      v2[e] *= f;
    }
    p.cols.add(c.clone());
    p.vals.add(v2);
    double l2 = lo * f;
    double h2 = hi * f;
    if (f < 0) {
      double t = l2;
      l2 = h2;
      h2 = t;
    }
    if (rnd.nextBoolean()) {
      l2 += rnd.nextInt(3) - 1;
    }
    p.rowBounds.add(new double[] {Math.min(l2, h2), h2});
  }

  // a column parallel to another: same rows, scaled
  private static void parallelColumn(Lp p, Random rnd) {
    int j = rnd.nextInt(p.n - 1);
    int k = p.n - 1;
    double f = rnd.nextBoolean() ? 2 : -1;
    for (int i = 0; i < p.m(); i++) {
      int[] c = p.cols.get(i);
      double[] v = p.vals.get(i);
      int ej = Arrays.binarySearch(c, j);
      int ek = Arrays.binarySearch(c, k);
      if (ej >= 0 && ek >= 0) {
        v[ek] = v[ej] * f;
      }
    }
    p.cost[k] = p.cost[j] * f;
  }

  // the negation of a row with bounds that contradict it
  private static void contradictingRow(Lp p, Random rnd) {
    int i = rnd.nextInt(p.m());
    double[] bi = p.rowBounds.get(i);
    p.cols.add(p.cols.get(i).clone());
    double[] v = p.vals.get(i).clone();
    for (int e = 0; e < v.length; e++) {
      v[e] = -v[e];
    }
    p.vals.add(v);
    double top = bi[1] < INF ? bi[1] : bi[0] + 10;
    p.rowBounds.add(new double[] {-top + rnd.nextInt(3) - 3, INF});
    // -a x >= -top + delta, i.e. a x <= top - delta: infeasible when it meets a x >= lo
    p.rowBounds.get(p.m() - 1)[0] = -(bi[0] > -INF ? bi[0] : top) + 1 + rnd.nextInt(3);
  }

  // ---------------------------------------------------------------- engines

  /** One engine under test, through the operations LinearRelaxation uses. */
  interface Engine {
    void setBounds(int j, double lo, double hi);

    int solve(int limit);

    int status(int s);

    double objective();

    double value(int j);

    double[] duals();

    double[] farkas();

    void addRows(int[][] c, double[][] v, double[] lo, double[] hi);

    int[] removeRows(int[] rows);

    Object save();

    boolean restore(Object b);

    Engine copy();

    long pivots();

    default boolean primal() {
      return false;
    }

    default boolean givenDuals() {
      return true;
    }

    default void setCost(double[] c) {
      throw new UnsupportedOperationException();
    }

    default int solvePrimal(int limit) {
      throw new UnsupportedOperationException();
    }
  }

  static final class Solver implements Engine {
    final LpSolver s;

    Solver(LpSolver s) {
      this.s = s;
    }

    public void setBounds(int j, double lo, double hi) {
      s.setBounds(j, lo, hi);
    }

    public int solve(int limit) {
      return s.solve(limit);
    }

    public int status(int st) {
      return st;
    }

    public double objective() {
      return s.objective();
    }

    public double value(int j) {
      return s.value(j);
    }

    public double[] duals() {
      return s.duals();
    }

    public double[] farkas() {
      return s.farkas();
    }

    public void addRows(int[][] c, double[][] v, double[] lo, double[] hi) {
      s.addRows(c, v, lo, hi);
    }

    public int[] removeRows(int[] rows) {
      return s.removeRows(rows);
    }

    public Object save() {
      return s.saveBasis();
    }

    public boolean restore(Object b) {
      return s.restoreBasis(b);
    }

    public Engine copy() {
      return new Solver(s.copy());
    }

    public long pivots() {
      return s.pivots();
    }
  }

  static final class Jalp implements Engine {
    final RevisedDualSimplex s;
    final boolean given;

    Jalp(RevisedDualSimplex s, boolean given) {
      this.s = s;
      this.given = given;
    }

    public void setBounds(int j, double lo, double hi) {
      s.setBounds(j, lo, hi);
    }

    public int solve(int limit) {
      return s.solve(limit);
    }

    public int status(int st) {
      return st;
    }

    public double objective() {
      return s.objective();
    }

    public double value(int j) {
      return s.value(j);
    }

    public double[] duals() {
      return given ? s.givenDuals() : s.duals();
    }

    public double[] farkas() {
      return s.farkas();
    }

    public void addRows(int[][] c, double[][] v, double[] lo, double[] hi) {
      s.addRows(c, v, lo, hi);
    }

    public int[] removeRows(int[] rows) {
      return s.removeRows(rows);
    }

    public Object save() {
      return s.saveBasis();
    }

    public boolean restore(Object b) {
      return b instanceof RevisedDualSimplex.Basis x && s.restoreBasis(x);
    }

    public Engine copy() {
      return new Jalp(s.copy(), given);
    }

    public long pivots() {
      return s.pivots();
    }

    @Override
    public boolean primal() {
      return true;
    }

    @Override
    public boolean givenDuals() {
      return given;
    }

    @Override
    public void setCost(double[] c) {
      s.setCost(c);
    }

    @Override
    public int solvePrimal(int limit) {
      return s.solvePrimal(limit);
    }
  }

  // ---------------------------------------------------------------- a case

  static final class Finding extends RuntimeException {
    Finding(String m) {
      super(m, null, false, false);
    }
  }

  static int checks;
  static int[] statusCount = new int[4];

  static String engineName(int e) {
    return switch (e) {
      case 0 -> "dense";
      case 1 -> "jalp";
      default -> "rds";
    };
  }

  static Engine build(Lp p, int engine, Random rnd, StringBuilder log) {
    int[][] c = p.cols.toArray(new int[0][]);
    double[][] v = p.vals.toArray(new double[0][]);
    double[] lo = rowLo(p);
    double[] hi = rowHi(p);
    Engine e =
        switch (engine) {
          case 0 -> new Solver(new DualSimplex(p.dense(), lo, hi, p.cost));
          case 1 -> new Solver(new JalpSimplex(c, v, lo, hi, p.cost));
          default -> buildJalp(c, v, lo, hi, p.cost, rnd, log);
        };
    for (int j = 0; j < p.n; j++) {
      e.setBounds(j, p.lo[j], p.hi[j]);
    }
    return e;
  }

  private static Engine buildJalp(
      int[][] c,
      double[][] v,
      double[] lo,
      double[] hi,
      double[] cost,
      Random rnd,
      StringBuilder log) {
    boolean scale = rnd.nextInt(4) != 0;
    RevisedDualSimplex s = new RevisedDualSimplex(c, v, lo, hi, cost, scale);
    boolean exact = rnd.nextBoolean();
    s.setExact(exact);
    boolean presolve = rnd.nextBoolean();
    s.setPresolve(presolve);
    // the kinds of slack rows a crash basis may give away: 0 equations, 1 ranged, 2 all
    int crash = rnd.nextInt(3) == 0 ? rnd.nextInt(3) : -1;
    if (crash >= 0) {
      s.setCrash(crash);
    }
    log.append(
        String.format(" scale=%s exact=%s presolve=%s crash=%d", scale, exact, presolve, crash));
    return new Jalp(s, rnd.nextBoolean());
  }

  static final String SOLVE = "solve";
  static final String NONE = "none";

  /** Runs one case; returns null when clean, else the finding. */
  static String runCase(long seed, int engine) {
    Random rnd = new Random(seed);
    String family = FAMILIES[rnd.nextInt(FAMILIES.length)];
    boolean bounded = engine != 2 || rnd.nextBoolean();
    if (bounded && UNBOUNDED.equals(family)) {
      family = RANDOM;
    }
    Lp p = generate(rnd, family, bounded);
    StringBuilder log = new StringBuilder(family);
    Engine e;
    try {
      e = build(p, engine, rnd, log);
    } catch (RuntimeException ex) {
      return "CRASH build " + ex;
    }
    afterUnbounded = false;
    Case k = new Case(rnd, e, p.copy(), log, engine);
    try {
      k.run();
    } catch (Finding f) {
      return f.getMessage()
          + (afterUnbounded ? " [after-unbounded]" : "")
          + (bounded ? " [bounded]" : "")
          + "\n  trace: "
          + log
          + "\n"
          + k.cur.dump();
    } catch (RuntimeException ex) {
      StringBuilder st = new StringBuilder();
      for (StackTraceElement el : ex.getStackTrace()) {
        if (st.length() < 600) {
          st.append("\n    at ").append(el);
        }
      }
      return "CRASH " + ex + st + "\n  trace: " + log + "\n" + k.cur.dump();
    }
    return null;
  }

  /** The state of one case: the engine, the LP as it stands, and the levels of the search. */
  private static final class Case {
    final Random rnd;
    final StringBuilder log;
    final int engine;
    Engine e;
    Lp cur;
    Deque<double[][]> stack = new ArrayDeque<>(); // saved column and row bounds
    final Deque<Object> bases = new ArrayDeque<>();

    Case(Random rnd, Engine e, Lp cur, StringBuilder log, int engine) {
      this.rnd = rnd;
      this.e = e;
      this.cur = cur;
      this.log = log;
      this.engine = engine;
    }

    void run() {
      int ops = 10 + rnd.nextInt(50);
      for (int op = 0; op < ops; op++) {
        String what = step(rnd.nextInt(10), op);
        if (what != null) {
          log.append("\n  ").append(what);
          if (SOLVE.equals(what)) {
            check(e, cur, solveChunks(e, rnd, false), what, engine);
          }
        }
      }
    }

    // one operation; returns what it was, or null when it checked its own solve
    String step(int kind, int op) {
      if (kind <= 3 || op == 0) {
        return SOLVE;
      }
      return switch (kind) {
        case 4 -> branch();
        case 5 -> stack.isEmpty() ? SOLVE : backtrack();
        case 6 -> cut();
        case 7 -> cur.m() > 0 ? removeRows() : SOLVE;
        case 8 -> cur.m() > 0 ? moveRow() : SOLVE;
        default -> copyOrNewCosts();
      };
    }

    // branch on a column: tighten one bound towards an integer near its value
    String branch() {
      int j = rnd.nextInt(cur.n);
      stack.push(new double[][] {cur.lo.clone(), cur.hi.clone(), rowLo(cur), rowHi(cur)});
      bases.push(rnd.nextBoolean() ? e.save() : NONE);
      double val = Math.floor(e.value(j));
      if (!Double.isFinite(val) || Math.abs(val) > 1000) {
        // the values of an unbounded or failed solve are no guide
        val = (double) rnd.nextInt(21) - 10;
      }
      if (rnd.nextBoolean()) {
        double floor = cur.lo[j] > -INF ? cur.lo[j] : val;
        double h = Math.min(cur.hi[j], val);
        cur.hi[j] = Math.max(h, floor);
      } else {
        double ceiling = cur.hi[j] < INF ? cur.hi[j] : val + 1;
        double l = Math.max(cur.lo[j], val + 1);
        cur.lo[j] = Math.min(l, ceiling);
      }
      e.setBounds(j, cur.lo[j], cur.hi[j]);
      return "branch x" + j + " [" + cur.lo[j] + "," + cur.hi[j] + "]";
    }

    // backtrack: the bounds of the level above, and its basis when it was kept
    String backtrack() {
      double[][] s = stack.pop();
      Object b = bases.pop();
      for (int j = 0; j < cur.n; j++) {
        if (cur.lo[j] != s[0][j] || cur.hi[j] != s[1][j]) {
          cur.lo[j] = s[0][j];
          cur.hi[j] = s[1][j];
          e.setBounds(j, cur.lo[j], cur.hi[j]);
        }
      }
      for (int i = 0; i < Math.min(cur.m(), s[2].length); i++) {
        double[] rb = cur.rowBounds.get(i);
        if (rb[0] != s[2][i] || rb[1] != s[3][i]) {
          rb[0] = s[2][i];
          rb[1] = s[3][i];
          e.setBounds(cur.n + i, rb[0], rb[1]);
        }
      }
      boolean restored = !NONE.equals(b) && rnd.nextBoolean() && e.restore(b);
      return "backtrack restored=" + restored;
    }

    // a cut: a random row through or near the current point
    String cut() {
      int k = 1 + rnd.nextInt(Math.min(cur.n, 5));
      int[] c = new int[k];
      double[] v = new double[k];
      Pool pool = new Pool(cur.n);
      double act = 0;
      for (int q = 0; q < k; q++) {
        c[q] = pool.take(rnd);
        v[q] = (double) rnd.nextInt(13) - 6;
        if (v[q] == 0) {
          v[q] = 1;
        }
        double x = e.value(c[q]);
        act += v[q] * (Double.isFinite(x) && Math.abs(x) <= 1000 ? x : 0);
      }
      Arrays.sort(c);
      double hi = Math.floor(act) - rnd.nextInt(2);
      double[] lo = {-INF};
      double[] hiA = {hi};
      if (rnd.nextInt(4) == 0) {
        lo[0] = hi - rnd.nextInt(3);
      }
      e.addRows(new int[][] {c}, new double[][] {v}, lo, hiA);
      cur.cols.add(c);
      cur.vals.add(v);
      cur.rowBounds.add(new double[] {lo[0], hiA[0]});
      return "cut " + Arrays.toString(c) + Arrays.toString(v) + " <= " + hi;
    }

    // remove a few rows (only those with basic slacks go)
    String removeRows() {
      int k = 1 + rnd.nextInt(Math.min(3, cur.m()));
      int[] rows = new int[k];
      for (int q = 0; q < k; q++) {
        rows[q] = rnd.nextInt(cur.m());
      }
      rows = Arrays.stream(rows).distinct().sorted().toArray();
      int[] kept = e.removeRows(rows);
      if (kept != null) {
        keepRows(kept);
      }
      return "remove "
          + Arrays.toString(rows)
          + " -> "
          + (kept == null ? NONE : kept.length + " rows");
    }

    private void keepRows(int[] kept) {
      Lp next = cur.copy();
      next.cols = new ArrayList<>();
      next.vals = new ArrayList<>();
      next.rowBounds = new ArrayList<>();
      for (int old : kept) {
        next.cols.add(cur.cols.get(old));
        next.vals.add(cur.vals.get(old));
        next.rowBounds.add(cur.rowBounds.get(old).clone());
      }
      cur = next;
      // the saved row bounds of the levels above: by the old row of each new row
      Deque<double[][]> moved = new ArrayDeque<>();
      for (double[][] s : stack) {
        double[] rl = new double[kept.length];
        double[] rh = new double[kept.length];
        for (int i = 0; i < kept.length; i++) {
          rl[i] = kept[i] < s[2].length ? s[2][kept[i]] : cur.rowBounds.get(i)[0];
          rh[i] = kept[i] < s[3].length ? s[3][kept[i]] : cur.rowBounds.get(i)[1];
        }
        moved.addLast(new double[][] {s[0], s[1], rl, rh});
      }
      stack = moved;
    }

    // move the bounds of a row (as presolve/probing or a changed objective bound would)
    String moveRow() {
      int i = rnd.nextInt(cur.m());
      double[] rb = cur.rowBounds.get(i);
      if (rnd.nextBoolean() && rb[1] < INF) {
        rb[1] -= rnd.nextInt(3);
        rb[0] = Math.min(rb[0], rb[1]);
      } else if (rb[0] > -INF) {
        rb[0] += rnd.nextInt(3);
        rb[1] = Math.max(rb[0], rb[1]);
      }
      e.setBounds(cur.n + i, rb[0], rb[1]);
      return "row " + i + " bounds " + Arrays.toString(rb);
    }

    // a copy of the engine, or new costs solved by the primal simplex (checked here)
    String copyOrNewCosts() {
      if (rnd.nextBoolean()) {
        e = e.copy();
        return "copy";
      }
      if (!e.primal()) {
        return SOLVE;
      }
      for (int j = 0; j < cur.n; j++) {
        cur.cost[j] = rnd.nextInt(3) == 0 ? cur.cost[j] : rnd.nextInt(11) - 5.0;
      }
      e.setCost(cur.cost.clone());
      check(e, cur, solveChunks(e, rnd, true), "setCost+primal", engine);
      return null;
    }
  }

  static final int CAP = 200_000;

  static int solveChunks(Engine e, Random rnd, boolean primal) {
    int total = 0;
    int chunk = rnd.nextInt(3) == 0 ? 1 + rnd.nextInt(7) : 1_000_000;
    while (true) {
      long before = e.pivots();
      int s = primal ? e.solvePrimal(chunk) : e.solve(chunk);
      total += (int) (e.pivots() - before) + 1;
      if (s != RevisedDualSimplex.LIMIT) {
        return s;
      }
      if (total > CAP) {
        return -1;
      }
      if (chunk == 1_000_000) {
        return -2; // a limit without the pivot limit: numerics gave up
      }
    }
  }

  static boolean afterUnbounded;

  static void check(Engine e, Lp p, int status, String what, int engine) {
    checks++;
    if (status == -1) {
      throw new Finding("STALL " + what + " more than " + CAP + " pivots");
    }
    Ref ref = exact(p);
    statusCount[ref.status]++;
    if (status == -2) {
      checkGaveUp(p, ref, what, engine);
      return;
    }
    if (status == R_OPTIMAL && ref.status == R_INFEASIBLE && violation(e, p) <= 1) {
      tolerated++; // infeasible by less than the tolerance: the point is accepted
      return;
    }
    if (status != ref.status) {
      checkOtherStatus(e, p, status, ref, what);
    } else if (status == R_INFEASIBLE) {
      checkFarkas(e, p, what);
    } else if (status == R_OPTIMAL) {
      checkOptimum(e, p, ref.opt.dbl(), what);
    } else {
      afterUnbounded |= status == R_UNBOUNDED;
    }
  }

  // LIMIT before the pivot limit: allowed for numerics (JalpSimplex maps UNBOUNDED to it)
  private static void checkGaveUp(Lp p, Ref ref, String what, int engine) {
    if (engine == 1 && ref.status != R_OPTIMAL && ref.status != R_INFEASIBLE) {
      return;
    }
    if (engine == 1 && ref.status == R_INFEASIBLE && dualInfeasible(p)) {
      return;
    }
    throw new Finding("GAVE_UP " + what + " ref " + ref.status + optimum(ref));
  }

  private static String optimum(Ref ref) {
    return ref.opt == null ? "" : " opt " + ref.opt.dbl();
  }

  private static String range(Q[] r) {
    return "["
        + (r[0] == null ? "-inf" : r[0].dbl())
        + ", "
        + (r[1] == null ? "inf" : r[1].dbl())
        + "]";
  }

  // a status other than the exact one: wrong unless both say there is no optimum
  private static void checkOtherStatus(Engine e, Lp p, int status, Ref ref, String what) {
    boolean both = status == R_UNBOUNDED && ref.status == R_INFEASIBLE && dualInfeasible(p);
    if (both) {
      return;
    }
    String extra = status == R_INFEASIBLE ? " farkas " + range(farkasRange(p, e.farkas())) : "";
    afterUnbounded |= status == R_UNBOUNDED;
    throw new Finding(
        "STATUS " + what + " got " + status + " ref " + ref.status + optimum(ref) + extra);
  }

  private static void checkFarkas(Engine e, Lp p, String what) {
    Q[] r = farkasRange(p, e.farkas());
    boolean proves = (r[0] != null && r[0].signum() > 0) || (r[1] != null && r[1].signum() < 0);
    if (!proves) {
      throw new Finding("FARKAS " + what + " does not prove infeasibility exactly: " + range(r));
    }
  }

  private static double largestValue(Engine e, Lp p) {
    double xs = 1;
    for (int j = 0; j < p.n; j++) {
      xs = Math.max(xs, Math.abs(e.value(j)));
    }
    return xs;
  }

  private static void checkOptimum(Engine e, Lp p, double opt, String what) {
    double z = 0;
    for (int j = 0; j < p.n; j++) {
      z += p.cost[j] * e.value(j); // the dense simplex reports c x for its perturbed costs
    }
    double scale = 1 + Math.abs(opt);
    double xs = largestValue(e, p);
    double objTol = 1e-6 * scale * Math.clamp(xs, 1, 1e3);
    if (Math.abs(z - opt) > objTol) {
      throw new Finding(
          String.format(Locale.ROOT, "OBJECTIVE %s got %.12g ref %.12g", what, z, opt));
    }
    checkPrimal(e, p, xs, what);
    // the duals: their Lagrangian bound is a valid lower bound by weak duality; it must reach the
    // optimum (LinearRelaxation's bound and reduced-cost fixing are made from them)
    if (e.givenDuals() && p.m() > 0) {
      checkDuals(e, p, opt, scale * Math.clamp(xs, 1, 1e3), what);
    }
  }

  // primal feasibility of the answer
  private static void checkPrimal(Engine e, Lp p, double xs, String what) {
    for (int j = 0; j < p.n; j++) {
      double x = e.value(j);
      double tol = 1e-6 * Math.max(1, Math.abs(x));
      if (!(x >= p.lo[j] - tol && x <= p.hi[j] + tol)) {
        throw new Finding(
            "PRIMAL " + what + " x" + j + "=" + x + " outside [" + p.lo[j] + "," + p.hi[j] + "]");
      }
    }
    for (int i = 0; i < p.m(); i++) {
      double s = activity(e, p, i);
      double tol = 1e-6 * norm(p, i) * xs;
      double[] rb = p.rowBounds.get(i);
      if (!(s >= rb[0] - tol && s <= rb[1] + tol)) {
        throw new Finding(
            "PRIMAL " + what + " row " + i + " activity " + s + " outside " + Arrays.toString(rb));
      }
    }
  }

  private static double activity(Engine e, Lp p, int i) {
    double s = 0;
    for (int k = 0; k < p.cols.get(i).length; k++) {
      s += p.vals.get(i)[k] * e.value(p.cols.get(i)[k]);
    }
    return s;
  }

  private static double norm(Lp p, int i) {
    double norm = 1;
    for (double v : p.vals.get(i)) {
      norm = Math.max(norm, Math.abs(v));
    }
    return norm;
  }

  private static void checkDuals(Engine e, Lp p, double opt, double size, String what) {
    double[] y = e.duals();
    Q l = lagrangian(p, y);
    if (l == null) {
      throw new Finding(
          "DUALS "
              + what
              + " Lagrangian bound -inf at an optimum "
              + opt
              + " y="
              + Arrays.toString(y));
    }
    if (opt - l.dbl() > 1e-5 * size) {
      throw new Finding(
          String.format(
              Locale.ROOT,
              "DUALS %s Lagrangian bound %.12g below optimum %.12g",
              what,
              l.dbl(),
              opt));
    }
  }

  // the largest violation of the bounds and rows by the engine's point, relative to the tolerance
  // the checks allow (1e-6 of the magnitudes); above 1 it is outside the tolerance
  static double violation(Engine e, Lp p) {
    double xs = largestValue(e, p);
    double worst = 0;
    for (int j = 0; j < p.n; j++) {
      double x = e.value(j);
      double tol = 1e-6 * Math.max(1, Math.abs(x));
      double v = Math.max(p.lo[j] - x, x - p.hi[j]);
      worst = Math.max(worst, Double.isNaN(v) ? 1e300 : v / tol);
    }
    for (int i = 0; i < p.m(); i++) {
      double s = activity(e, p, i);
      double tol = 1e-6 * norm(p, i) * xs;
      double[] rb = p.rowBounds.get(i);
      double v = Math.max(rb[0] - s, s - rb[1]);
      worst = Math.max(worst, Double.isNaN(v) ? 1e300 : v / tol);
    }
    return worst;
  }

  static int tolerated;
}
