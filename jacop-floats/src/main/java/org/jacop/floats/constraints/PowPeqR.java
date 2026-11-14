/*
 * PowPeqR.java
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

package org.jacop.floats.constraints;

import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Constraint P^n = R for floats, with a constant exponent n &gt; 0.
 *
 * <p>For an integer exponent the power is defined for every P: an odd power is increasing, and an
 * even power is decreasing for P &lt;= 0 and increasing for P &gt;= 0, so that R &gt;= 0 and P lies
 * in the union [-R^(1/n)] ∪ [R^(1/n)] of two intervals (the hole around zero is kept in the domain
 * of P). For a non-integer exponent P must be non-negative and the power is increasing. Both
 * directions are projected to the interval hull of the exact image, rounded outward, which is hull
 * (2B) consistency of the relation, as in the relational interval arithmetic of Benhamou and Older
 * and the projection functions of HC4:
 *
 * <ul>
 *   <li>F. Benhamou and W. Older, "Applying interval arithmetic to real, integer and Boolean
 *       constraints", Journal of Logic Programming 32(1), 1997, pp. 1-24.
 *   <li>F. Benhamou, F. Goualard, L. Granvilliers and J.-F. Puget, "Revising hull and box
 *       consistency", ICLP 1999, pp. 230-244.
 * </ul>
 *
 * <p>Decomposing x^n as exp(n * ln |x|), as the FlatZinc front end did before, loses the sign of x
 * and the hole around zero, and an odd power with x of unknown sign did not propagate at all.
 * {@link Math#pow} is within one ulp of the exact result, so every computed bound is moved one ulp
 * outward. The n-th roots are computed with {@link Math#pow} too, and then checked by raising them
 * back to the n-th power, because 1/n is itself rounded.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class PowPeqR extends Constraint
    implements SatisfiedPresent, FloatDerivableConstraint, Copyable<PowPeqR> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable p in constraint p^n = r. */
  public final FloatVar p;

  /** It specifies the constant exponent n in constraint p^n = r. */
  public final double n;

  /** It specifies variable r in constraint p^n = r. */
  public final FloatVar r;

  /** True when n is an integer. */
  private final boolean integral;

  /** True when n is an even integer. */
  private final boolean even;

  /**
   * It constructs a constraint P^n = R.
   *
   * @param p the base.
   * @param n the exponent, a finite number greater than zero.
   * @param r the power.
   */
  public PowPeqR(FloatVar p, double n, FloatVar r) {

    checkInputForNullness(new String[] {"p", "r"}, new Object[] {p, r});
    if (!(n > 0) || Double.isInfinite(n)) {
      throw new IllegalArgumentException(
          "Exponent of PowPeqR must be finite and greater than zero, but is " + n);
    }

    numberId = idNumber.incrementAndGet();

    this.p = p;
    this.n = n;
    this.r = r;
    this.integral = n == Math.rint(n);
    this.even = integral && Math.rint(n / 2) * 2 == n;

    setScope(p, r);
  }

  @Override
  public void consistency(Store store) {

    if (!integral) {
      // a non-integer power of a negative number is undefined
      p.domain.inMin(store.level, p, 0.0);
    }

    do {
      store.propagationHasOccurred = false;

      double lo = p.min();
      double hi = p.max();
      double rMin;
      double rMax;
      if (!even || lo >= 0) {
        rMin = powDown(lo);
        rMax = powUp(hi);
      } else if (hi <= 0) {
        rMin = powDown(-hi);
        rMax = powUp(-lo);
      } else {
        rMin = 0.0;
        rMax = powUp(Math.max(-lo, hi));
      }
      r.domain.in(store.level, r, rMin, rMax);

      if (even) {
        double a = rootDown(Math.max(r.min(), 0.0));
        double b = rootUp(r.max());
        if (a <= 0.0) {
          p.domain.in(store.level, p, -b, b);
        } else {
          FloatIntervalDomain dom = new FloatIntervalDomain(-b, -a);
          dom.unionAdapt(a, b);
          p.domain.in(store.level, p, dom);
        }
      } else {
        p.domain.in(store.level, p, signedRootDown(r.min()), signedRootUp(r.max()));
      }

    } while (store.propagationHasOccurred);
  }

  /** Computes x^n, for x &gt;= 0 or, when n is an integer, for any x. */
  private double pow(double x) {
    if (x == 0.0 || x == 1.0) {
      return x;
    }
    return Math.pow(x, n);
  }

  /** Computes a lower bound of the exact x^n. */
  private double powDown(double x) {
    double v = pow(x);
    return v == x && (x == 0.0 || x == 1.0) ? v : FloatDomain.down(v);
  }

  /** Computes an upper bound of the exact x^n. */
  private double powUp(double x) {
    double v = pow(x);
    return v == x && (x == 0.0 || x == 1.0) ? v : FloatDomain.up(v);
  }

  /** Computes the rounded n-th root of t &gt;= 0. */
  private double root(double t) {
    if (n == 2) {
      return Math.sqrt(t);
    }
    if (n == 3) {
      return Math.cbrt(t);
    }
    return Math.pow(t, 1.0 / n);
  }

  /**
   * Computes a lower bound of the exact n-th root of t &gt;= 0: a value whose n-th power, rounded
   * up, is still at most t.
   */
  private double rootDown(double t) {
    if (t <= 0.0) {
      return 0.0;
    }
    if (t == Double.POSITIVE_INFINITY) {
      return Double.POSITIVE_INFINITY;
    }
    double l = FloatDomain.down(root(t));
    double step = Math.ulp(l);
    while (l > 0.0 && powUp(l) > t) {
      l -= step;
      step *= 2;
    }
    return Math.max(l, 0.0);
  }

  /**
   * Computes an upper bound of the exact n-th root of t &gt;= 0: a value whose n-th power, rounded
   * down, is at least t.
   */
  private double rootUp(double t) {
    if (t <= 0.0) {
      return 0.0;
    }
    if (t == Double.POSITIVE_INFINITY) {
      return Double.POSITIVE_INFINITY;
    }
    double u = FloatDomain.up(root(t));
    double step = Math.ulp(u);
    while (u < Double.POSITIVE_INFINITY && powDown(u) < t) {
      u += step;
      step *= 2;
    }
    return u;
  }

  /** Computes a lower bound of the real n-th root of t (of any sign for an odd n). */
  private double signedRootDown(double t) {
    return t < 0 ? (integral ? -rootUp(-t) : 0.0) : rootDown(t);
  }

  /** Computes an upper bound of the real n-th root of t (of any sign for an odd n). */
  private double signedRootUp(double t) {
    if (t < 0 && !integral) {
      // r = p^n >= 0 for a non-negative p; the forward step has already failed or pruned r
      return 0.0;
    }
    return t < 0 ? -rootDown(-t) : rootUp(t);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    return AbstractTrigConstraint.satisfiedWithTrigFunctionStatic(p, r, x -> Math.pow(x, n));
  }

  @Override
  public String toString() {
    return id() + " : PowPeqR(" + p + ", " + n + ", " + r + " )";
  }

  /**
   * Computes the derivative of this constraint with respect to a variable.
   *
   * @param store the constraint store
   * @param f the function variable for which to compute the derivative
   * @param vars the set of variables involved in the derivative computation
   * @param x the variable with respect to which the derivative is computed
   * @return the derivative variable, or null if f is not part of this constraint
   */
  @Override
  public FloatVar derivative(Store store, FloatVar f, Set<FloatVar> vars, FloatVar x) {

    if (f.equals(r)) {
      // f = p^n, f' = n * p^(n-1) * d(p)
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(Derivative.getDerivative(store, p, vars, x), slope(store), v));
      return v;
    } else if (f.equals(p)) {
      // f = r^(1/n), f' = d(r) / (n * p^(n-1))
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(
          new PdivQeqR(Derivative.getDerivative(store, r, vars, x), slope(store), v));
      return v;
    }
    return null;
  }

  /** Creates a variable for n * p^(n-1). */
  private FloatVar slope(Store store) {
    FloatVar s = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
    if (n == 1) {
      return new FloatVar(store, 1.0, 1.0);
    }
    FloatVar t;
    if (n == 2) {
      t = p;
    } else {
      t = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(new PowPeqR(p, n - 1, t));
    }
    Derivative.poseDerivativeConstraint(new PmulCeqR(t, n, s));
    return s;
  }

  @Override
  public PowPeqR copy(VarMap map) {
    return new PowPeqR(map.get(p), n, map.get(r));
  }
}
