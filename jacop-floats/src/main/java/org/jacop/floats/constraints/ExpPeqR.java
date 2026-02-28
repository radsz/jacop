/*
 * ExpPeqR.java
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.InternalException;

/**
 * Constraints exp(P) #= Q for P and Q floats.
 *
 * <p>Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ExpPeqR extends Constraint implements SatisfiedPresent, FloatDerivableConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a left hand variable in equality constraint. */
  public final FloatVar p;

  /** It specifies a right hand variable in equality constraint. */
  public final FloatVar q;

  /**
   * It constructs constraint P = Q.
   *
   * @param p variable p.
   * @param q variable q.
   */
  public ExpPeqR(FloatVar p, FloatVar q) {

    checkInputForNullness(new String[] {"p", "q"}, new Object[] {p, q});

    numberId = idNumber.incrementAndGet();

    this.p = p;
    this.q = q;

    setScope(p, q);
  }

  @Override
  public void consistency(Store store) {

    do {
      double[] pBounds = computeFirstBoundsFromSecond();
      p.domain.in(store.level, p, pBounds[0], pBounds[1]);

      store.propagationHasOccurred = false;

      double[] qBounds = computeSecondBoundsFromFirst();
      q.domain.in(store.level, q, qBounds[0], qBounds[1]);

    } while (store.propagationHasOccurred);
  }

  /** Returns {pMin, pMax} for exp(p)=q. */
  private double[] computeFirstBoundsFromSecond() {
    if (q.min() == 1.0 && q.max() == 1.0) {
      return new double[] {0.0, 0.0};
    }
    double pMin;
    if (q.min() > 0) {
      pMin = java.lang.Math.log(q.min());
      if (Double.isNaN(pMin) || Double.isInfinite(pMin)) {
        throw new InternalException("Floating-point overflow in constraint " + this);
      }
      pMin = FloatDomain.down(pMin);
    } else if (q.max() > 0) {
      pMin = FloatDomain.MIN_FLOAT;
    } else {
      throw Store.failException;
    }
    double pMax = java.lang.Math.log(q.max());
    if (Double.isNaN(pMax) || Double.isInfinite(pMax)) {
      throw new InternalException("Floating-point overflow in constraint " + this);
    }
    pMax = FloatDomain.up(pMax);
    return new double[] {pMin, pMax};
  }

  /** Returns {qMin, qMax} for exp(p)=q. */
  private double[] computeSecondBoundsFromFirst() {
    if (p.min() == p.max() && p.min() == 0.0) {
      return new double[] {1.0, 1.0};
    }
    double qMin = java.lang.Math.exp(p.min());
    if (Double.isNaN(qMin) || Double.isInfinite(qMin)) {
      throw new InternalException("Floating-point overflow in constraint " + this);
    }
    qMin = FloatDomain.down(qMin);

    double qMax = java.lang.Math.exp(p.max());
    if (Double.isNaN(qMax) || Double.isInfinite(qMax)) {
      throw new InternalException("Floating-point overflow in constraint " + this);
    }
    qMax = FloatDomain.up(qMax);
    return new double[] {qMin, qMax};
  }

  @Override
  public boolean satisfied() {
    return grounded() && java.lang.Math.exp(p.min()) - q.max() <= FloatDomain.precision();
  }

  @Override
  public String toString() {
    return id() + " : ExpPeqR(" + p + ", " + q + " )";
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
  public FloatVar derivative(Store store, FloatVar f, Set<FloatVar> vars, FloatVar x) {

    if (f.equals(q)) {
      // f = exp(p)
      // f' = d(p)*exp(p)
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(Derivative.getDerivative(store, p, vars, x), f, v));
      return v;

    } else if (f.equals(p)) {
      // f = ln(q)
      // f' = (1/q)*d(q)
      FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(new PdivQeqR(new FloatVar(store, 1.0, 1.0), q, v1));
      Derivative.poseDerivativeConstraint(
          new PminusQeqR(Derivative.getDerivative(store, q, vars, x), v1, v));
      return v;
    }

    return null;
  }
}
