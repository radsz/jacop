/*
 * HyperbolicPeqR.java
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

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Constraint f(P) = R for the hyperbolic functions f = sinh, cosh and tanh.
 *
 * <p>sinh and tanh are increasing bijections, so both directions are bounds of monotone functions;
 * cosh is decreasing for P &lt;= 0 and increasing for P &gt;= 0, so P lies in the union of two
 * intervals symmetric around zero. The inverse functions are constraints of the same class with the
 * arguments swapped: asinh(X) = Y is sinh(Y) = X, atanh(X) = Y is tanh(Y) = X, and acosh(X) = Y is
 * cosh(Y) = X with Y &gt;= 0. Both directions are projected to the interval hull of the exact
 * image, rounded outward (hull consistency, the projections of HC4):
 *
 * <ul>
 *   <li>F. Benhamou and W. Older, "Applying interval arithmetic to real, integer and Boolean
 *       constraints", Journal of Logic Programming 32(1), 1997, pp. 1-24.
 *   <li>F. Benhamou, F. Goualard, L. Granvilliers and J.-F. Puget, "Revising hull and box
 *       consistency", ICLP 1999, pp. 230-244.
 * </ul>
 *
 * <p>The MiniZinc library used to define these functions by exp and ln, with P occurring twice,
 * which loses hull consistency (dependency problem). {@link Math#sinh}, {@link Math#cosh} and
 * {@link Math#tanh} are within 2.5 ulps of the exact value, so forward bounds are moved three ulps
 * outward; the inverse images are first approximated with logarithms and then checked with the
 * forward function, so their rounding does not matter.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class HyperbolicPeqR extends Constraint
    implements SatisfiedPresent, Copyable<HyperbolicPeqR> {

  /** The hyperbolic function of the constraint. */
  public enum Function {
    /** Hyperbolic sine. */
    SINH,
    /** Hyperbolic cosine. */
    COSH,
    /** Hyperbolic tangent. */
    TANH
  }

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** Ulps of error of the forward functions, rounded up. */
  private static final int ULPS = 3;

  /** It specifies variable p in constraint f(p) = r. */
  public final FloatVar p;

  /** It specifies variable r in constraint f(p) = r. */
  public final FloatVar r;

  /** It specifies function f in constraint f(p) = r. */
  public final Function function;

  /**
   * It constructs a constraint f(P) = R.
   *
   * @param p the argument.
   * @param function the hyperbolic function.
   * @param r the result.
   */
  public HyperbolicPeqR(FloatVar p, Function function, FloatVar r) {
    checkInputForNullness(new String[] {"p", "function", "r"}, new Object[] {p, function, r});
    numberId = idNumber.incrementAndGet();
    this.p = p;
    this.function = function;
    this.r = r;
    setScope(p, r);
  }

  @Override
  public void consistency(Store store) {
    if (function == Function.TANH) {
      r.domain.in(store.level, r, -1.0, 1.0);
    } else if (function == Function.COSH) {
      r.domain.inMin(store.level, r, 1.0);
    }

    do {
      store.propagationHasOccurred = false;

      double lo = p.min();
      double hi = p.max();
      if (function != Function.COSH || lo >= 0) {
        r.domain.in(store.level, r, lowerImage(lo), upperImage(hi));
      } else if (hi <= 0) {
        r.domain.in(store.level, r, lowerImage(-hi), upperImage(-lo));
      } else {
        r.domain.in(store.level, r, 1.0, upperImage(Math.max(-lo, hi)));
      }

      if (function == Function.COSH) {
        double a = inverseDown(Math.max(r.min(), 1.0));
        double b = inverseUp(r.max());
        if (a <= 0.0) {
          p.domain.in(store.level, p, -b, b);
        } else {
          FloatIntervalDomain dom = new FloatIntervalDomain(-b, -a);
          dom.unionAdapt(a, b);
          p.domain.in(store.level, p, dom);
        }
      } else {
        p.domain.in(store.level, p, inverseDown(r.min()), inverseUp(r.max()));
      }
    } while (store.propagationHasOccurred);
  }

  /** Computes the rounded apply(x); cosh is only used for x &gt;= 0. */
  private double apply(double x) {
    return switch (function) {
      case SINH -> Math.sinh(x);
      case COSH -> Math.cosh(x);
      case TANH -> Math.tanh(x);
    };
  }

  /** Computes a lower bound of the exact apply(x), on the increasing branch. */
  private double lowerImage(double x) {
    if (x == 0.0) {
      return function == Function.COSH ? 1.0 : 0.0;
    }
    double v = apply(x);
    for (int i = 0; i < ULPS; i++) {
      v = Math.nextDown(v);
    }
    if (function == Function.TANH) {
      return Math.max(v, -1.0);
    }
    return function == Function.COSH ? Math.max(v, 1.0) : v;
  }

  /** Computes an upper bound of the exact apply(x), on the increasing branch. */
  private double upperImage(double x) {
    if (x == 0.0) {
      return function == Function.COSH ? 1.0 : 0.0;
    }
    double v = apply(x);
    for (int i = 0; i < ULPS; i++) {
      v = Math.nextUp(v);
    }
    return function == Function.TANH ? Math.min(v, 1.0) : v;
  }

  /** Computes an approximation of the inverse of f at t, on the increasing branch. */
  private double inverse(double t) {
    return switch (function) {
      case SINH -> {
        double a = Math.abs(t);
        double v = a > 1e150 ? Math.log(2) + Math.log(a) : Math.log(a + Math.sqrt(a * a + 1));
        yield Math.copySign(v, t);
      }
      case COSH -> t > 1e150 ? Math.log(2) + Math.log(t) : Math.log(t + Math.sqrt(t * t - 1));
      case TANH -> 0.5 * Math.log((1 + t) / (1 - t));
    };
  }

  /** Tells whether t is at or below the range of f (tanh only reaches (-1, 1)). */
  private boolean belowRange(double t) {
    return function == Function.TANH ? t <= -1.0 : t == Double.NEGATIVE_INFINITY;
  }

  /** Tells whether t is at or above the range of f. */
  private boolean aboveRange(double t) {
    return function == Function.TANH ? t >= 1.0 : t == Double.POSITIVE_INFINITY;
  }

  /**
   * Computes a lower bound of the exact inverse of f at t: a value whose image, rounded up, is
   * still at most t.
   */
  private double inverseDown(double t) {
    if (belowRange(t)) {
      return Double.NEGATIVE_INFINITY;
    }
    if (aboveRange(t)) {
      return Double.POSITIVE_INFINITY;
    }
    if (function == Function.COSH && t <= 1.0) {
      return 0.0;
    }
    double l = Math.nextDown(inverse(t));
    double step = Math.max(Math.ulp(l), Double.MIN_NORMAL);
    while (l > (function == Function.COSH ? 0.0 : Double.NEGATIVE_INFINITY) && upperImage(l) > t) {
      l -= step;
      step *= 2;
    }
    return function == Function.COSH ? Math.max(l, 0.0) : l;
  }

  /**
   * Computes an upper bound of the exact inverse of f at t: a value whose image, rounded down, is
   * at least t.
   */
  private double inverseUp(double t) {
    if (belowRange(t)) {
      return Double.NEGATIVE_INFINITY;
    }
    if (aboveRange(t)) {
      return Double.POSITIVE_INFINITY;
    }
    if (function == Function.COSH && t <= 1.0) {
      return 0.0;
    }
    double u = Math.nextUp(inverse(t));
    double step = Math.max(Math.ulp(u), Double.MIN_NORMAL);
    while (u < Double.POSITIVE_INFINITY && lowerImage(u) < t) {
      u += step;
      step *= 2;
    }
    return u;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    return switch (function) {
      case SINH -> AbstractTrigConstraint.satisfiedWithTrigFunctionStatic(p, r, Math::sinh);
      case COSH -> AbstractTrigConstraint.satisfiedWithTrigFunctionStatic(p, r, Math::cosh);
      case TANH -> AbstractTrigConstraint.satisfiedWithTrigFunctionStatic(p, r, Math::tanh);
    };
  }

  @Override
  public String toString() {
    return id() + " : HyperbolicPeqR(" + p + ", " + function + ", " + r + " )";
  }

  @Override
  public HyperbolicPeqR copy(VarMap map) {
    return new HyperbolicPeqR(map.get(p), function, map.get(r));
  }
}
