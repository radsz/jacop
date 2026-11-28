/*
 * FloatNewton.java
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
 * in material form or in the copies or in parts of the copies.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.constraints;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.linear.Linear;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.ConsistencyListener;

/**
 * Interval Newton contractor (Hansen-Sengupta operator with a midpoint-inverse preconditioner and
 * Gauss-Seidel) on the square system of equations that the float constraints of a model form.
 *
 * <p>Every supported primitive constraint is read as one equation g(x) = 0 over its variables:
 * linear equalities, x + y = z, x * y = z (also division and square root, which JaCoP posts as
 * products), c * x = z, x + c = z, x = y, x^n = z, exp(x) = z (also ln), sin(x) = z and cos(x) = z.
 * When the equations over the non-fixed float variables reachable from the given variables are as
 * many as those variables, the system is square and the contractor runs after propagation at every
 * search node: with the box X, its midpoint m, an interval Jacobian J(X) and Y an approximate
 * inverse of the midpoint of J(X), it narrows X to the solutions of Y J(X) (x - m) = -Y g(m), one
 * row at a time. g(m) and J(X) are evaluated in interval arithmetic with outward rounding, so no
 * solution is removed; Y needs no rigour.
 *
 * <p>References: E. Hansen and S. Sengupta, "Bounding solutions of systems of equations using
 * interval analysis", BIT 21(2), 1981; R. B. Kearfott, <i>Rigorous Global Search: Continuous
 * Problems</i>, Kluwer, 1996; R. E. Moore, R. B. Kearfott, M. J. Cloud, <i>Introduction to Interval
 * Analysis</i>, SIAM, 2009.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class FloatNewton implements ConsistencyListener {

  /** Largest square system handled (the preconditioner is dense). */
  public static final int MAX_SIZE = 400;

  /** Newton steps at a node while the box shrinks by more than RATIO of its width. */
  private static final int MAX_STEPS = 4;

  private static final double RATIO = 0.1;

  private final Store store;

  /** The unknowns of the system. */
  private FloatVar[] unknowns;

  private final Map<FloatVar, Integer> index = new HashMap<>();

  private final List<Equation> equations = new ArrayList<>();

  private ConsistencyListener[] children;

  private boolean square;

  /** Number of Newton steps. */
  public long steps;

  /** Number of steps that narrowed a domain. */
  public long narrowings;

  /** Number of steps that proved the box has no solution. */
  public long failures;

  /**
   * It creates the contractor over the system reachable from the given variables.
   *
   * @param store the store
   * @param vars the variables (usually the search variables)
   */
  public FloatNewton(Store store, FloatVar[] vars) {
    this.store = store;
    build(vars);
  }

  /**
   * It tells whether the reachable equations form a square system handled by the contractor.
   *
   * @return true if the contractor runs
   */
  public boolean isSquare() {
    return square;
  }

  /**
   * It returns the number of unknowns of the system.
   *
   * @return the size of the system, 0 if it is not square
   */
  public int size() {
    return square ? unknowns.length : 0;
  }

  private void build(FloatVar[] vars) {
    Set<FloatVar> seen = new LinkedHashSet<>();
    Set<Constraint> constraints = new LinkedHashSet<>();
    ArrayDeque<FloatVar> queue = new ArrayDeque<>();
    for (FloatVar v : vars) {
      if (seen.add(v)) {
        queue.add(v);
      }
    }
    while (!queue.isEmpty()) {
      FloatVar v = queue.poll();
      Constraint[][] model = v.dom().modelConstraints;
      if (model == null) {
        continue;
      }
      for (int e = 0; e < model.length; e++) {
        Constraint[] cs = model[e];
        if (cs == null) {
          continue;
        }
        int n = v.dom().modelConstraintsToEvaluate[e];
        for (int i = 0; i < n; i++) {
          Constraint c = cs[i];
          if (!constraints.add(c)) {
            continue;
          }
          for (Var w : c.arguments()) {
            if (w instanceof FloatVar f && seen.add(f)) {
              queue.add(f);
            }
          }
        }
      }
    }
    List<FloatVar> free = new ArrayList<>();
    for (FloatVar v : seen) {
      if (!v.singleton()) {
        index.put(v, free.size());
        free.add(v);
      }
    }
    unknowns = free.toArray(new FloatVar[0]);
    for (Constraint c : constraints) {
      Equation eq = equation(c);
      if (eq != null && eq.vars.length > 0) {
        equations.add(eq);
      }
    }
    square =
        unknowns.length > 0 && unknowns.length <= MAX_SIZE && equations.size() == unknowns.length;
  }

  /** Term of an equation: variable, or the constant value of a fixed variable. */
  private int term(FloatVar v) {
    Integer i = index.get(v);
    return i == null ? -1 : i;
  }

  private Equation equation(Constraint c) {
    if (c instanceof Linear l) {
      if (l.relationType != Linear.EQ) {
        return null;
      }
      return new LinearEq(l.list, l.weights, l.sum);
    }
    if (c instanceof PplusQeqR s) {
      return new LinearEq(new FloatVar[] {s.p, s.q, s.r}, new double[] {1, 1, -1}, 0);
    }
    if (c instanceof PplusCeqR s) {
      return new LinearEq(new FloatVar[] {s.p, s.r}, new double[] {1, -1}, -s.c);
    }
    if (c instanceof PmulCeqR s) {
      return new LinearEq(new FloatVar[] {s.p, s.r}, new double[] {s.c, -1}, 0);
    }
    if (c instanceof PeqQ s) {
      return new LinearEq(new FloatVar[] {s.p, s.q}, new double[] {1, -1}, 0);
    }
    if (c instanceof PmulQeqR s) {
      return new Product(s.p, s.q, s.r);
    }
    if (c instanceof PowPeqR s) {
      return new Power(s.p, s.n, s.r);
    }
    if (c instanceof ExpPeqR s) {
      return new Unary(s.p, s.q, Unary.EXP);
    }
    if (c instanceof SinPeqR s) {
      return new Unary(s.p, s.q, Unary.SIN);
    }
    if (c instanceof CosPeqR s) {
      return new Unary(s.p, s.q, Unary.COS);
    }
    return null;
  }

  @Override
  public boolean executeAfterConsistency(boolean consistent) {
    boolean result = consistent && (!square || contract());
    if (children != null) {
      for (ConsistencyListener child : children) {
        result = child.executeAfterConsistency(result);
      }
    }
    return result;
  }

  private boolean contract() {
    int n = unknowns.length;
    double[] lo = new double[n];
    double[] hi = new double[n];
    for (int step = 0; step < MAX_STEPS; step++) {
      double before = 0;
      for (int i = 0; i < n; i++) {
        lo[i] = unknowns[i].min();
        hi[i] = unknowns[i].max();
        if (!Double.isFinite(lo[i]) || !Double.isFinite(hi[i])) {
          return true;
        }
        before = Math.max(before, hi[i] - lo[i]);
      }
      if (before == 0) {
        return true;
      }
      steps++;
      int r = newtonStep(lo, hi);
      if (r < 0) {
        failures++;
        return false;
      }
      if (r == 0) {
        return true;
      }
      double reduced = 0;
      try {
        for (int i = 0; i < n; i++) {
          FloatVar v = unknowns[i];
          double width = v.max() - v.min();
          if (lo[i] > v.min() || hi[i] < v.max()) {
            v.domain.in(store.level, v, Math.max(lo[i], v.min()), Math.min(hi[i], v.max()));
            reduced = Math.max(reduced, (width - (v.max() - v.min())) / Math.max(width, 1e-300));
          }
        }
        narrowings++;
        if (!store.consistency()) {
          failures++;
          return false;
        }
      } catch (FailException e) {
        failures++;
        return false;
      }
      if (reduced < RATIO) {
        return true;
      }
    }
    return true;
  }

  /**
   * One Hansen-Sengupta step on the box [lo, hi], narrowed in place.
   *
   * @return -1 if the box has no solution, 0 if nothing changed, 1 if the box was narrowed
   */
  private int newtonStep(double[] lo, double[] hi) {
    int n = unknowns.length;
    double[] mid = new double[n];
    for (int i = 0; i < n; i++) {
      mid[i] = lo[i] + 0.5 * (hi[i] - lo[i]);
      if (mid[i] < lo[i] || mid[i] > hi[i]) {
        mid[i] = lo[i];
      }
    }
    double[] gLo = new double[n];
    double[] gHi = new double[n];
    // jacobian rows: entries (column, lo, hi)
    int[][] cols = new int[n][];
    double[][] jLo = new double[n][];
    double[][] jHi = new double[n][];
    double[][] jMid = new double[n][n];
    for (int e = 0; e < n; e++) {
      Equation eq = equations.get(e);
      double[] g = eq.value(mid, this);
      gLo[e] = g[0];
      gHi[e] = g[1];
      int k = eq.vars.length;
      cols[e] = eq.vars;
      jLo[e] = new double[k];
      jHi[e] = new double[k];
      eq.gradient(lo, hi, jLo[e], jHi[e], this);
      for (int t = 0; t < k; t++) {
        if (!Double.isFinite(jLo[e][t]) || !Double.isFinite(jHi[e][t])) {
          return 0;
        }
        jMid[e][eq.vars[t]] += 0.5 * (jLo[e][t] + jHi[e][t]);
      }
      if (!(gLo[e] <= gHi[e])) {
        return 0;
      }
    }
    double[][] y = invert(jMid);
    if (y == null) {
      return 0;
    }
    // A = Y J (interval), b = Y g(m) (interval)
    double[][] aLo = new double[n][n];
    double[][] aHi = new double[n][n];
    double[] bLo = new double[n];
    double[] bHi = new double[n];
    for (int i = 0; i < n; i++) {
      double[] yi = y[i];
      double[] rowLo = aLo[i];
      double[] rowHi = aHi[i];
      double sLo = 0;
      double sHi = 0;
      for (int e = 0; e < n; e++) {
        double c = yi[e];
        if (c == 0) {
          continue;
        }
        sLo = Iv.down(sLo + Iv.mulLo(c, gLo[e], gHi[e]));
        sHi = Iv.up(sHi + Iv.mulHi(c, gLo[e], gHi[e]));
        int[] cs = cols[e];
        for (int t = 0; t < cs.length; t++) {
          int j = cs[t];
          rowLo[j] = Iv.down(rowLo[j] + Iv.mulLo(c, jLo[e][t], jHi[e][t]));
          rowHi[j] = Iv.up(rowHi[j] + Iv.mulHi(c, jLo[e][t], jHi[e][t]));
        }
      }
      bLo[i] = sLo;
      bHi[i] = sHi;
    }
    boolean changed = false;
    for (int i = 0; i < n; i++) {
      double dLo = aLo[i][i];
      double dHi = aHi[i][i];
      if (dLo <= 0 && dHi >= 0) {
        continue;
      }
      // num = -b_i - sum_{j != i} A_ij (x_j - m_j)
      double numLo = -bHi[i];
      double numHi = -bLo[i];
      for (int j = 0; j < n; j++) {
        if (j == i || (aLo[i][j] == 0 && aHi[i][j] == 0)) {
          continue;
        }
        double xl = Iv.down(lo[j] - mid[j]);
        double xh = Iv.up(hi[j] - mid[j]);
        double pl = Iv.mulIntervalLo(aLo[i][j], aHi[i][j], xl, xh);
        double ph = Iv.mulIntervalHi(aLo[i][j], aHi[i][j], xl, xh);
        numLo = Iv.down(numLo - ph);
        numHi = Iv.up(numHi - pl);
      }
      if (!Double.isFinite(numLo) || !Double.isFinite(numHi)) {
        continue;
      }
      double qLo = Iv.divLo(numLo, numHi, dLo, dHi);
      double qHi = Iv.divHi(numLo, numHi, dLo, dHi);
      double nl = Iv.down(mid[i] + qLo);
      double nh = Iv.up(mid[i] + qHi);
      if (nl > hi[i] || nh < lo[i]) {
        return -1;
      }
      if (nl > lo[i]) {
        lo[i] = nl;
        changed = true;
      }
      if (nh < hi[i]) {
        hi[i] = nh;
        changed = true;
      }
    }
    return changed ? 1 : 0;
  }

  /** Inverse by Gauss-Jordan elimination with partial pivoting, null if (nearly) singular. */
  static double[][] invert(double[][] m) {
    int n = m.length;
    double[][] a = new double[n][];
    double[][] inv = new double[n][n];
    for (int i = 0; i < n; i++) {
      a[i] = m[i].clone();
      inv[i][i] = 1;
    }
    for (int c = 0; c < n; c++) {
      int p = c;
      for (int r = c + 1; r < n; r++) {
        if (Math.abs(a[r][c]) > Math.abs(a[p][c])) {
          p = r;
        }
      }
      if (Math.abs(a[p][c]) < 1e-300 || !Double.isFinite(a[p][c])) {
        return null;
      }
      double[] t = a[p];
      a[p] = a[c];
      a[c] = t;
      t = inv[p];
      inv[p] = inv[c];
      inv[c] = t;
      double d = a[c][c];
      for (int k = 0; k < n; k++) {
        a[c][k] /= d;
        inv[c][k] /= d;
      }
      for (int r = 0; r < n; r++) {
        if (r == c) {
          continue;
        }
        double f = a[r][c];
        if (f == 0) {
          continue;
        }
        for (int k = 0; k < n; k++) {
          a[r][k] -= f * a[c][k];
          inv[r][k] -= f * inv[c][k];
        }
      }
    }
    for (double[] row : inv) {
      for (double v : row) {
        if (!Double.isFinite(v)) {
          return null;
        }
      }
    }
    return inv;
  }

  /** Value of a variable at the midpoint: its index or its fixed value. */
  double[] at(FloatVar v, double[] point) {
    int i = term(v);
    if (i < 0) {
      return new double[] {v.min(), v.max()};
    }
    return new double[] {point[i], point[i]};
  }

  double[] box(FloatVar v, double[] lo, double[] hi) {
    int i = term(v);
    if (i < 0) {
      return new double[] {v.min(), v.max()};
    }
    return new double[] {lo[i], hi[i]};
  }

  /** An equation g(x) = 0 with its value at a point and its gradient over a box. */
  abstract class Equation {

    /** Distinct unknowns of the equation (indices). */
    int[] vars;

    /** Sets vars from the unknowns among the given variables. */
    void setVars(FloatVar... vs) {
      LinkedHashSet<Integer> s = new LinkedHashSet<>();
      for (FloatVar v : vs) {
        int i = term(v);
        if (i >= 0) {
          s.add(i);
        }
      }
      vars = s.stream().mapToInt(Integer::intValue).toArray();
    }

    int position(FloatVar v) {
      int i = term(v);
      for (int t = 0; t < vars.length; t++) {
        if (vars[t] == i) {
          return t;
        }
      }
      return -1;
    }

    /** Encloses g(point), the point holding the midpoints of the unknowns. */
    abstract double[] value(double[] point, FloatNewton n);

    /** Encloses the partial derivatives of g over the box in gLo/gHi, in the order of vars. */
    abstract void gradient(double[] lo, double[] hi, double[] gLo, double[] gHi, FloatNewton n);

    /** Adds [l, h] to the derivative with respect to v. */
    void addDerivative(FloatVar v, double l, double h, double[] gLo, double[] gHi) {
      int t = position(v);
      if (t >= 0) {
        gLo[t] = Iv.down(gLo[t] + l);
        gHi[t] = Iv.up(gHi[t] + h);
      }
    }
  }

  /** sum w_i x_i - c = 0. */
  final class LinearEq extends Equation {
    final FloatVar[] xs;
    final double[] ws;
    final double c;

    LinearEq(FloatVar[] xs, double[] ws, double c) {
      this.xs = xs;
      this.ws = ws;
      this.c = c;
      setVars(xs);
    }

    @Override
    double[] value(double[] point, FloatNewton n) {
      double l = -c;
      double h = -c;
      for (int i = 0; i < xs.length; i++) {
        double[] x = n.at(xs[i], point);
        l = Iv.down(l + Iv.mulLo(ws[i], x[0], x[1]));
        h = Iv.up(h + Iv.mulHi(ws[i], x[0], x[1]));
      }
      return new double[] {l, h};
    }

    @Override
    void gradient(double[] lo, double[] hi, double[] gLo, double[] gHi, FloatNewton n) {
      for (int i = 0; i < xs.length; i++) {
        addDerivative(xs[i], ws[i], ws[i], gLo, gHi);
      }
    }
  }

  /** p * q - r = 0. */
  final class Product extends Equation {
    final FloatVar p;
    final FloatVar q;
    final FloatVar r;

    Product(FloatVar p, FloatVar q, FloatVar r) {
      this.p = p;
      this.q = q;
      this.r = r;
      setVars(p, q, r);
    }

    @Override
    double[] value(double[] point, FloatNewton n) {
      double[] a = n.at(p, point);
      double[] b = n.at(q, point);
      double[] z = n.at(r, point);
      double l = Iv.mulIntervalLo(a[0], a[1], b[0], b[1]);
      double h = Iv.mulIntervalHi(a[0], a[1], b[0], b[1]);
      return new double[] {Iv.down(l - z[1]), Iv.up(h - z[0])};
    }

    @Override
    void gradient(double[] lo, double[] hi, double[] gLo, double[] gHi, FloatNewton n) {
      double[] a = n.box(p, lo, hi);
      double[] b = n.box(q, lo, hi);
      addDerivative(p, b[0], b[1], gLo, gHi);
      addDerivative(q, a[0], a[1], gLo, gHi);
      addDerivative(r, -1, -1, gLo, gHi);
    }
  }

  /** p^e - r = 0 for a constant e greater than 0. */
  final class Power extends Equation {
    final FloatVar p;
    final double e;
    final FloatVar r;

    Power(FloatVar p, double e, FloatVar r) {
      this.p = p;
      this.e = e;
      this.r = r;
      setVars(p, r);
    }

    @Override
    double[] value(double[] point, FloatNewton n) {
      double[] a = n.at(p, point);
      double[] z = n.at(r, point);
      double[] v = Iv.pow(a[0], a[1], e);
      return new double[] {Iv.down(v[0] - z[1]), Iv.up(v[1] - z[0])};
    }

    @Override
    void gradient(double[] lo, double[] hi, double[] gLo, double[] gHi, FloatNewton n) {
      double[] a = n.box(p, lo, hi);
      double[] d;
      if (e == 1) {
        d = new double[] {1, 1};
      } else {
        double[] v = Iv.pow(a[0], a[1], e - 1);
        d = new double[] {Iv.mulLo(e, v[0], v[1]), Iv.mulHi(e, v[0], v[1])};
      }
      addDerivative(p, d[0], d[1], gLo, gHi);
      addDerivative(r, -1, -1, gLo, gHi);
    }
  }

  /** f(p) - q = 0 for f = exp, sin or cos. */
  final class Unary extends Equation {
    static final int EXP = 0;
    static final int SIN = 1;
    static final int COS = 2;
    final FloatVar p;
    final FloatVar q;
    final int f;

    Unary(FloatVar p, FloatVar q, int f) {
      this.p = p;
      this.q = q;
      this.f = f;
      setVars(p, q);
    }

    private double[] apply(int g, double l, double h) {
      return switch (g) {
        case EXP -> Iv.exp(l, h);
        case SIN -> Iv.sin(l, h);
        default -> Iv.cos(l, h);
      };
    }

    @Override
    double[] value(double[] point, FloatNewton n) {
      double[] a = n.at(p, point);
      double[] z = n.at(q, point);
      double[] v = apply(f, a[0], a[1]);
      return new double[] {Iv.down(v[0] - z[1]), Iv.up(v[1] - z[0])};
    }

    @Override
    void gradient(double[] lo, double[] hi, double[] gLo, double[] gHi, FloatNewton n) {
      double[] a = n.box(p, lo, hi);
      double[] d;
      if (f == EXP) {
        d = Iv.exp(a[0], a[1]);
      } else if (f == SIN) {
        d = Iv.cos(a[0], a[1]);
      } else {
        double[] s = Iv.sin(a[0], a[1]);
        d = new double[] {-s[1], -s[0]};
      }
      addDerivative(p, d[0], d[1], gLo, gHi);
      addDerivative(q, -1, -1, gLo, gHi);
    }
  }

  @Override
  public void setChildrenListeners(ConsistencyListener[] children) {
    this.children = children;
  }

  @Override
  public void setChildrenListeners(ConsistencyListener child) {
    this.children = new ConsistencyListener[] {child};
  }

  /** Interval operations with outward rounding (each result moved out by one ulp or more). */
  static final class Iv {

    private Iv() {}

    static double down(double x) {
      return Double.isNaN(x) ? Double.NEGATIVE_INFINITY : Math.nextDown(x);
    }

    static double up(double x) {
      return Double.isNaN(x) ? Double.POSITIVE_INFINITY : Math.nextUp(x);
    }

    static double mulLo(double c, double l, double h) {
      return down(c >= 0 ? c * l : c * h);
    }

    static double mulHi(double c, double l, double h) {
      return up(c >= 0 ? c * h : c * l);
    }

    static double mulIntervalLo(double al, double ah, double bl, double bh) {
      double m =
          Math.min(Math.min(prod(al, bl), prod(al, bh)), Math.min(prod(ah, bl), prod(ah, bh)));
      return down(m);
    }

    static double mulIntervalHi(double al, double ah, double bl, double bh) {
      double m =
          Math.max(Math.max(prod(al, bl), prod(al, bh)), Math.max(prod(ah, bl), prod(ah, bh)));
      return up(m);
    }

    private static double prod(double a, double b) {
      return a == 0 || b == 0 ? 0 : a * b;
    }

    /** Lower bound of [nl, nh] / [dl, dh] for a divisor without 0. */
    static double divLo(double nl, double nh, double dl, double dh) {
      return down(Math.min(Math.min(nl / dl, nl / dh), Math.min(nh / dl, nh / dh)));
    }

    static double divHi(double nl, double nh, double dl, double dh) {
      return up(Math.max(Math.max(nl / dl, nl / dh), Math.max(nh / dl, nh / dh)));
    }

    /** x^e (Math.pow is within 1 ulp; results move out by 2 ulps). */
    static double[] pow(double l, double h, double e) {
      boolean integral = e == Math.rint(e) && Math.abs(e) < 1e15;
      if (!integral) {
        l = Math.max(l, 0);
        if (h < 0) {
          return new double[] {Double.NaN, Double.NaN};
        }
      }
      if (e == 0) {
        return new double[] {1, 1};
      }
      if (e < 0) {
        if (l <= 0 && h >= 0) {
          return new double[] {Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY};
        }
        double[] v = pow(l, h, -e);
        if (v[0] <= 0 && v[1] >= 0) {
          return new double[] {Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY};
        }
        return new double[] {
          down(down(Math.min(1 / v[0], 1 / v[1]))), up(up(Math.max(1 / v[0], 1 / v[1])))
        };
      }
      double pl = Math.pow(l, e);
      double ph = Math.pow(h, e);
      double min;
      double max;
      boolean even = integral && ((long) e) % 2 == 0;
      if (even && l < 0 && h > 0) {
        min = 0;
        max = Math.max(pl, ph);
      } else {
        min = Math.min(pl, ph);
        max = Math.max(pl, ph);
      }
      return new double[] {min == 0 ? 0 : down(down(min)), up(up(max))};
    }

    static double[] exp(double l, double h) {
      return new double[] {Math.max(0, down(down(Math.exp(l)))), up(up(Math.exp(h)))};
    }

    static double[] sin(double l, double h) {
      return cos(
          l - Math.PI / 2, h - Math.PI / 2, Math.ulp(Math.max(Math.abs(l), Math.abs(h))) * 4);
    }

    static double[] cos(double l, double h) {
      return cos(l, h, 0);
    }

    /** cos over [l, h] where the bounds may carry an absolute error up to slack. */
    private static double[] cos(double l, double h, double slack) {
      if (!(h - l < 2 * Math.PI) || !Double.isFinite(l) || !Double.isFinite(h)) {
        return new double[] {-1, 1};
      }
      double eps = slack + 1e-12 * Math.max(1, Math.max(Math.abs(l), Math.abs(h)));
      double cl = Math.cos(l);
      double ch = Math.cos(h);
      double min = Math.min(cl, ch) - eps;
      double max = Math.max(cl, ch) + eps;
      // maxima at 2k pi, minima at (2k + 1) pi
      if (Math.floor((h + eps) / (2 * Math.PI)) > Math.floor((l - eps) / (2 * Math.PI))
          || Math.abs(Math.IEEEremainder(l, 2 * Math.PI)) <= eps
          || Math.abs(Math.IEEEremainder(h, 2 * Math.PI)) <= eps) {
        max = 1;
      }
      if (Math.floor((h - Math.PI + eps) / (2 * Math.PI))
              > Math.floor((l - Math.PI - eps) / (2 * Math.PI))
          || Math.abs(Math.IEEEremainder(l - Math.PI, 2 * Math.PI)) <= eps
          || Math.abs(Math.IEEEremainder(h - Math.PI, 2 * Math.PI)) <= eps) {
        min = -1;
      }
      return new double[] {Math.max(-1, min), Math.min(1, max)};
    }
  }
}
