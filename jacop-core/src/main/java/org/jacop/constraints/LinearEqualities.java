/*
 * LinearIntDomSumsetTest.java
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

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.util.IntLattice;

/**
 * Lattice reasoning over a set of linear equalities Σ a_i x_i = b on integer variables, done once,
 * before search. It is not a constraint: the equalities themselves must be imposed as well.
 *
 * <p>Each equality is first divided by the GCD of its coefficients; it is infeasible when that GCD
 * does not divide b. An equality with a variable of coefficient ±1 that occurs in no other equality
 * only defines that variable, and is set aside; this is repeated. The remaining equalities are
 * split into connected components by shared variables, and the integer solutions of each component
 * are computed as a particular solution x0 plus the lattice of the homogeneous system, by a Hermite
 * normal form ({@link IntLattice}). That proves a component infeasible over the integers, or gives
 * for each variable x_j the congruence x_j ≡ x0_j (mod g_j), where g_j is the GCD of the j-th
 * coordinates of the lattice basis, and g_j = 0 fixes x_j. Bounds propagation of the single
 * equalities sees neither. Then the equalities set aside give their defined variable the congruence
 * that the congruences of the other variables imply. A congruence removes the values outside its
 * residue class from a domain of at most 256 values, and rounds the bounds of a larger domain into
 * the class.
 *
 * <p>Optionally, a component is reformulated as Aardal, Hurkens and Lenstra do for market split
 * problems ("Solving a system of linear Diophantine equations with lower and upper bounds on the
 * variables", Math. of OR 25(3), 2000; Aardal, Bixby, Hurkens, Lenstra and Smeltink, IPCO 1999):
 * the lattice basis is LLL-reduced, x0 is moved close to the centre of the box of domains, and new
 * variables λ give x = x0 + Σ_k λ_k q_k, imposed as one equality per variable. A search on λ, last
 * (longest) basis vector first, branches on directions in which the box is thin, which is what
 * makes such systems easy for branch and bound in the λ space while they are hard in the x space
 * (Cornuéjols and Dawande, IPCO 1998 / INFORMS J. Computing 11(2), 1999). The domains of λ are the
 * ranges of λ = (B Bᵀ)⁻¹ B (x - x0) over the box, with B the basis, computed in floating point and
 * widened by one.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LinearEqualities {

  /** One equality Σ a_i x_i = b. */
  public static final class Row {

    private final IntVar[] x;

    private final int[] a;

    private final int b;

    /**
     * It creates the equality Σ a_i x_i = b.
     *
     * @param x the variables.
     * @param a the coefficients.
     * @param b the right-hand side.
     */
    public Row(IntVar[] x, int[] a, int b) {
      this.x = x;
      this.a = a;
      this.b = b;
    }

    /**
     * It returns the variables.
     *
     * @return the variables, not copied.
     */
    public IntVar[] x() {
      return x;
    }

    /**
     * It returns the coefficients.
     *
     * @return the coefficients, not copied.
     */
    public int[] a() {
      return a;
    }

    /**
     * It returns the right-hand side.
     *
     * @return the right-hand side.
     */
    public int b() {
      return b;
    }
  }

  /**
   * Domain size above which a congruence only tightens the bounds. Every hole is one more interval
   * in the domain, which slows each later domain operation, and a few far apart values of a large
   * domain (a value or a big M) change the LP encodings and the search more than they prune.
   */
  private static final long MAX_HOLES_DOMAIN = 256;

  private final Store store;

  private int maxVars = 300;

  private int maxRows = 300;

  private Predicate<List<Row>> reformulate = c -> false;

  // the equalities, normalised, by variable index
  private final List<int[]> vars = new ArrayList<>();
  private final List<long[]> coefs = new ArrayList<>();
  private final List<Long> rhs = new ArrayList<>();

  private final Map<IntVar, Integer> index = new IdentityHashMap<>();
  private final List<IntVar> variables = new ArrayList<>();

  // the congruence of each variable: x ≡ residue (mod modulus); modulus 1 is none, 0 fixes it
  private long[] modulus;
  private long[] residue;

  /** Statistics: the components given a Hermite normal form. */
  public int components;

  /** Statistics: the equalities in those components. */
  public int componentRows;

  /** Statistics: the equalities set aside as definitions. */
  public int definitions;

  /** Statistics: the variables whose domain a congruence changed. */
  public int prunedVariables;

  /** Statistics: the values removed by congruences. */
  public long prunedValues;

  /** The variables λ of the reformulated components, each component's last basis vector first. */
  public final List<IntVar> lattice = new ArrayList<>();

  /** The equalities imposed by the reformulation. */
  public final List<Constraint> posted = new ArrayList<>();

  /**
   * It creates the reasoning for one store.
   *
   * @param store the store of the variables.
   */
  public LinearEqualities(Store store) {
    this.store = store;
  }

  /**
   * It sets the largest component given a Hermite normal form.
   *
   * @param vars the most variables.
   * @param rows the most equalities.
   */
  public void setLimits(int vars, int rows) {
    this.maxVars = vars;
    this.maxRows = rows;
  }

  /**
   * It switches the Aardal-Hurkens-Lenstra reformulation on.
   *
   * @param on true to reformulate the components.
   */
  public void setReformulate(boolean on) {
    this.reformulate = c -> on;
  }

  /**
   * It switches the Aardal-Hurkens-Lenstra reformulation on for the components that a filter
   * accepts.
   *
   * @param filter given the equalities of a component, normalised (divided by their GCD, fixed
   *     variables moved to the right-hand side), it tells whether to reformulate it.
   */
  public void setReformulate(Predicate<List<Row>> filter) {
    this.reformulate = filter;
  }

  /**
   * It reasons over the equalities and prunes the domains at the current level.
   *
   * @param equalities the equalities.
   * @throws org.jacop.core.FailException when they have no integer solution within the domains.
   */
  public void apply(List<Row> equalities) {
    for (Row r : equalities) {
      add(r);
    }
    int n = variables.size();
    modulus = new long[n];
    residue = new long[n];
    Arrays.fill(modulus, 1);
    int m = vars.size();
    if (m == 0) {
      return;
    }
    // the rows that contain each variable
    List<List<Integer>> rowsOf = new ArrayList<>();
    for (int j = 0; j < n; j++) {
      rowsOf.add(new ArrayList<>());
    }
    int[] occurs = new int[n];
    for (int r = 0; r < m; r++) {
      for (int j : vars.get(r)) {
        rowsOf.get(j).add(r);
        occurs[j]++;
      }
    }
    boolean[] alive = new boolean[m];
    Arrays.fill(alive, true);
    int[] defined = new int[m];
    Arrays.fill(defined, -1);
    List<Integer> peeled = new ArrayList<>();
    Deque<Integer> queue = new ArrayDeque<>();
    for (int r = 0; r < m; r++) {
      queue.add(r);
    }
    while (!queue.isEmpty()) {
      int r = queue.poll();
      if (!alive[r]) {
        continue;
      }
      int[] v = vars.get(r);
      long[] c = coefs.get(r);
      for (int k = 0; k < v.length; k++) {
        if (Math.abs(c[k]) == 1 && occurs[v[k]] == 1) {
          alive[r] = false;
          defined[r] = k;
          peeled.add(r);
          for (int j : v) {
            if (--occurs[j] == 1) {
              for (int q : rowsOf.get(j)) {
                if (alive[q]) {
                  queue.add(q);
                }
              }
            }
          }
          break;
        }
      }
    }
    definitions = peeled.size();
    solveComponents(alive, rowsOf);
    // the definitions, last set aside first: their other variables are known by then
    for (int p = peeled.size() - 1; p >= 0; p--) {
      define(peeled.get(p), defined[peeled.get(p)]);
    }
    for (int j = 0; j < n; j++) {
      if (modulus[j] != 1) {
        prune(variables.get(j), modulus[j], residue[j]);
      }
    }
    for (Constraint c : posted) {
      store.impose(c);
    }
  }

  private void add(Row r) {
    Map<Integer, Long> terms = new LinkedHashMap<>();
    long b = r.b();
    try {
      for (int i = 0; i < r.x().length; i++) {
        IntVar x = r.x()[i];
        long a = r.a()[i];
        if (a == 0) {
          continue;
        }
        if (x.singleton()) {
          b = Math.subtractExact(b, Math.multiplyExact(a, (long) x.value()));
        } else {
          terms.merge(variable(x), a, Long::sum);
        }
      }
    } catch (ArithmeticException _) {
      return;
    }
    terms.values().removeIf(a -> a == 0);
    if (terms.isEmpty()) {
      if (b != 0) {
        throw Store.failException;
      }
      return;
    }
    long g = 0;
    for (long a : terms.values()) {
      g = gcd(g, Math.abs(a));
    }
    if (b % g != 0) {
      throw Store.failException;
    }
    int[] v = new int[terms.size()];
    long[] c = new long[terms.size()];
    int k = 0;
    for (Map.Entry<Integer, Long> e : terms.entrySet()) {
      v[k] = e.getKey();
      c[k++] = e.getValue() / g;
    }
    vars.add(v);
    coefs.add(c);
    rhs.add(b / g);
  }

  private int variable(IntVar x) {
    return index.computeIfAbsent(
        x,
        y -> {
          variables.add(y);
          return variables.size() - 1;
        });
  }

  private void solveComponents(boolean[] alive, List<List<Integer>> rowsOf) {
    int m = vars.size();
    boolean[] done = new boolean[m];
    for (int start = 0; start < m; start++) {
      if (!alive[start] || done[start]) {
        continue;
      }
      // the rows and variables of the component of row start
      List<Integer> rows = new ArrayList<>();
      Map<Integer, Integer> local = new LinkedHashMap<>();
      Deque<Integer> queue = new ArrayDeque<>();
      queue.add(start);
      done[start] = true;
      while (!queue.isEmpty()) {
        int r = queue.poll();
        rows.add(r);
        for (int j : vars.get(r)) {
          if (local.putIfAbsent(j, local.size()) == null) {
            for (int q : rowsOf.get(j)) {
              if (alive[q] && !done[q]) {
                done[q] = true;
                queue.add(q);
              }
            }
          }
        }
      }
      if (rows.size() > maxRows || local.size() > maxVars) {
        continue;
      }
      solve(rows, local);
    }
  }

  private void solve(List<Integer> rows, Map<Integer, Integer> local) {
    int n = local.size();
    long[][] a = new long[rows.size()][n];
    long[] b = new long[rows.size()];
    for (int i = 0; i < rows.size(); i++) {
      int r = rows.get(i);
      int[] v = vars.get(r);
      long[] c = coefs.get(r);
      for (int k = 0; k < v.length; k++) {
        a[i][local.get(v[k])] = c[k];
      }
      b[i] = rhs.get(r);
    }
    IntLattice.Solutions s;
    try {
      s = IntLattice.solve(a, b, n);
    } catch (ArithmeticException _) {
      // entries too large: no deduction from this component
      return;
    }
    if (s == null) {
      throw Store.failException;
    }
    components++;
    componentRows += rows.size();
    int[] global = new int[n];
    for (Map.Entry<Integer, Integer> e : local.entrySet()) {
      global[e.getValue()] = e.getKey();
    }
    BigInteger[][] basis = s.basis();
    for (int j = 0; j < n; j++) {
      BigInteger g = BigInteger.ZERO;
      for (BigInteger[] q : basis) {
        g = g.gcd(q[j]);
        if (g.equals(BigInteger.ONE)) {
          break;
        }
      }
      if (g.equals(BigInteger.ONE) || g.bitLength() > 62) {
        continue;
      }
      long mod = g.longValueExact();
      BigInteger r = mod == 0 ? s.x0()[j] : s.x0()[j].mod(g);
      if (r.bitLength() > 62) {
        continue;
      }
      modulus[global[j]] = mod;
      residue[global[j]] = r.longValueExact();
    }
    if (basis.length > 0 && reformulate.test(rowsOf(rows))) {
      reformulate(s, global);
    }
  }

  private List<Row> rowsOf(List<Integer> rows) {
    List<Row> out = new ArrayList<>();
    for (int r : rows) {
      int[] v = vars.get(r);
      long[] c = coefs.get(r);
      IntVar[] x = new IntVar[v.length];
      int[] a = new int[v.length];
      for (int k = 0; k < v.length; k++) {
        x[k] = variables.get(v[k]);
        a[k] = (int) Math.max(Integer.MIN_VALUE, Math.min(Integer.MAX_VALUE, c[k]));
      }
      out.add(
          new Row(
              x, a, (int) Math.max(Integer.MIN_VALUE, Math.min(Integer.MAX_VALUE, rhs.get(r)))));
    }
    return out;
  }

  // x_v = c (b - Σ a_u x_u) with c = ±1: the congruence of the sum
  private void define(int r, int k) {
    int[] v = vars.get(r);
    long[] c = coefs.get(r);
    long sign = c[k];
    try {
      long g = 0;
      long rest = rhs.get(r);
      for (int i = 0; i < v.length; i++) {
        if (i == k) {
          continue;
        }
        g = gcd(g, Math.multiplyExact(Math.abs(c[i]), modulus[v[i]]));
        rest = Math.subtractExact(rest, Math.multiplyExact(c[i], residue[v[i]]));
        if (g == 1) {
          return;
        }
      }
      long value = Math.multiplyExact(sign, rest);
      modulus[v[k]] = g;
      residue[v[k]] = g == 0 ? value : Math.floorMod(value, g);
    } catch (ArithmeticException _) {
      // no congruence
    }
  }

  private void prune(IntVar x, long mod, long res) {
    int before = x.getSize();
    if (Boolean.getBoolean("tmp.lattice")) {
      System.err.println("PRUNE " + x + " mod " + mod + " res " + res);
    }
    if (mod == 0) {
      if (res < x.min() || res > x.max()) {
        throw Store.failException;
      }
      x.domain.in(store.level, x, (int) res, (int) res);
    } else {
      long first = x.min() + Math.floorMod(res - x.min(), mod);
      long last = x.max() - Math.floorMod(x.max() - res, mod);
      if (first > last) {
        throw Store.failException;
      }
      if (before <= MAX_HOLES_DOMAIN) {
        IntervalDomain d = new IntervalDomain((int) ((last - first) / mod) + 2);
        for (long v = first; v <= last; v += mod) {
          d.unionAdapt((int) v, (int) v);
        }
        x.domain.in(store.level, x, d);
      } else {
        x.domain.in(store.level, x, (int) first, (int) last);
      }
    }
    if (x.getSize() < before) {
      prunedVariables++;
      prunedValues += before - x.getSize();
    }
  }

  private void reformulate(IntLattice.Solutions s, int[] global) {
    BigInteger[][] basis = s.basis();
    BigInteger[] x0 = s.x0().clone();
    int n = x0.length;
    int d = basis.length;
    IntLattice.reduce(basis, 100_000);
    double[] centre = new double[n];
    double[] lo = new double[n];
    double[] hi = new double[n];
    for (int j = 0; j < n; j++) {
      IntVar x = variables.get(global[j]);
      lo[j] = x.min();
      hi[j] = x.max();
      centre[j] = (lo[j] + hi[j]) / 2;
    }
    IntLattice.closest(x0, basis, centre);
    for (int j = 0; j < n; j++) {
      if (x0[j].bitLength() > 30) {
        return;
      }
      for (BigInteger[] q : basis) {
        if (q[j].bitLength() > 30) {
          return;
        }
      }
    }
    double[][] bm = new double[d][n];
    for (int k = 0; k < d; k++) {
      for (int j = 0; j < n; j++) {
        bm[k][j] = basis[k][j].doubleValue();
      }
    }
    double[][] inverse = leftInverse(bm);
    if (inverse == null) {
      return;
    }
    int[] lmin = new int[d];
    int[] lmax = new int[d];
    for (int k = 0; k < d; k++) {
      double mn = 0;
      double mx = 0;
      double scale = 0;
      for (int j = 0; j < n; j++) {
        double x = x0[j].doubleValue();
        double u = inverse[k][j] * (lo[j] - x);
        double v = inverse[k][j] * (hi[j] - x);
        mn += Math.min(u, v);
        mx += Math.max(u, v);
        scale += Math.abs(u) + Math.abs(v);
      }
      double eps = 1e-6 * (1 + scale);
      double a = Math.floor(mn - eps) - 1;
      double b = Math.ceil(mx + eps) + 1;
      if (!(a > -1e8 && b < 1e8)) {
        return;
      }
      lmin[k] = (int) a;
      lmax[k] = (int) b;
    }
    IntVar[] lambda = new IntVar[d];
    for (int k = 0; k < d; k++) {
      lambda[k] = new IntVar(store, "_lattice" + lattice.size() + "_" + k, lmin[k], lmax[k]);
    }
    for (int k = d - 1; k >= 0; k--) {
      lattice.add(lambda[k]);
    }
    for (int j = 0; j < n; j++) {
      List<IntVar> xs = new ArrayList<>();
      List<Integer> ws = new ArrayList<>();
      xs.add(variables.get(global[j]));
      ws.add(1);
      for (int k = 0; k < d; k++) {
        int q = basis[k][j].intValueExact();
        if (q != 0) {
          xs.add(lambda[k]);
          ws.add(-q);
        }
      }
      if (xs.size() > 1) {
        posted.add(new LinearInt(xs, ws, "==", x0[j].intValueExact()));
      }
    }
  }

  // (B Bᵀ)⁻¹ B by Gaussian elimination with partial pivoting; null when singular
  private static double[][] leftInverse(double[][] bm) {
    int d = bm.length;
    int n = bm[0].length;
    double[][] g = new double[d][d];
    for (int i = 0; i < d; i++) {
      for (int k = 0; k < d; k++) {
        double s = 0;
        for (int j = 0; j < n; j++) {
          s += bm[i][j] * bm[k][j];
        }
        g[i][k] = s;
      }
    }
    double[][] rhsm = new double[d][];
    for (int i = 0; i < d; i++) {
      rhsm[i] = bm[i].clone();
    }
    for (int c = 0; c < d; c++) {
      int p = c;
      for (int i = c + 1; i < d; i++) {
        if (Math.abs(g[i][c]) > Math.abs(g[p][c])) {
          p = i;
        }
      }
      if (Math.abs(g[p][c]) < 1e-9) {
        return null;
      }
      double[] t = g[c];
      g[c] = g[p];
      g[p] = t;
      t = rhsm[c];
      rhsm[c] = rhsm[p];
      rhsm[p] = t;
      for (int i = 0; i < d; i++) {
        if (i != c && g[i][c] != 0) {
          double f = g[i][c] / g[c][c];
          for (int k = c; k < d; k++) {
            g[i][k] -= f * g[c][k];
          }
          for (int j = 0; j < n; j++) {
            rhsm[i][j] -= f * rhsm[c][j];
          }
        }
      }
    }
    for (int i = 0; i < d; i++) {
      for (int j = 0; j < n; j++) {
        rhsm[i][j] /= g[i][i];
      }
    }
    return rhsm;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return Math.abs(a);
  }
}
