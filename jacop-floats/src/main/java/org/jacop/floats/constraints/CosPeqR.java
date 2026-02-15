/*
 * CosPeqR.java
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
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.InternalException;

/**
 * Constraints cos(P) = R.
 *
 * <p>Bounds consistency can be used; third parameter of constructor controls this.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CosPeqR extends AbstractTrigConstraint
    implements SatisfiedPresent, FloatDerivableConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs cos(P) = Q constraints.
   *
   * @param p variable P
   * @param q variable Q
   */
  public CosPeqR(FloatVar p, FloatVar q) {
    super(p, q);
    numberId = idNumber.incrementAndGet();
  }

  @Override
  protected void boundConsistency(Store store) {

    if (spansFullPeriod()) {
      return;
    }

    do {

      store.propagationHasOccurred = false;

      if (satisfied()) {
        return;
      }

      double[] bounds = getNormalizedBounds();
      double min = bounds[0];
      double max = bounds[1];

      int intervalForMin = intervalNo(min);
      int intervalForMax = intervalNo(max);

      double qMin;
      double qMax;
      switch (intervalForMin) {
        case 1:
          switch (intervalForMax) {
            case 1:
              qMin = Math.cos(max);
              qMax = Math.cos(min);
              qMin = FloatDomain.down(qMin);
              qMax = FloatDomain.up(qMax);
              break;
            case 2:
              qMin = -1.0;
              qMax = Math.max(Math.cos(min), Math.cos(max));
              qMax = FloatDomain.up(qMax);
              break;
            case 3:
            case 4:
              qMin = -1.0;
              qMax = 1.0;
              break;
            default:
              throw new InternalException(
                  "Selected impossible case in sin, cos, asin or acos constraint");
          }
          break;

        case 2:
          switch (intervalForMax) {
            case 2:
              qMin = Math.cos(min);
              qMax = Math.cos(max);
              qMin = FloatDomain.down(qMin);
              qMax = FloatDomain.up(qMax);
              break;
            case 3:
              qMin = Math.min(Math.cos(min), Math.cos(max));
              qMax = 1.0;
              qMin = FloatDomain.down(qMin);
              break;
            case 4:
              qMin = -1.0;
              qMax = 1.0;
              break;
            default:
              throw new InternalException(
                  "Selected impossible case in sin, cos, asin or acos constraint");
          }
          break;

        case 3:
          switch (intervalForMax) {
            case 3:
              qMin = Math.cos(max);
              qMax = Math.cos(min);
              qMin = FloatDomain.down(qMin);
              qMax = FloatDomain.up(qMax);
              break;
            case 4:
              qMin = -1.0;
              qMax = Math.max(Math.cos(min), Math.cos(max));
              qMax = FloatDomain.up(qMax);
              break;
            default:
              throw new InternalException(
                  "Selected impossible case in sin, cos, asin or acos constraint");
          }
          break;

        case 4:
          switch (intervalForMax) {
            case 4:
              qMin = Math.cos(min);
              qMax = Math.cos(max);
              qMin = FloatDomain.down(qMin);
              qMax = FloatDomain.up(qMax);
              break;

            default:
              throw new InternalException(
                  "Selected impossible case in sin, cos, asin or acos constraint");
          }
          break;

        default:
          throw new InternalException(
              "Selected impossible case in sin, cos, asin or acos constraint");
      }

      q.domain.in(store.level, q, qMin, qMax);

      // p update using acos (range 0..PI)
      updatePDomain(store, qMin, qMax, Math::acos, 0.0, FloatDomain.PI);

    } while (store.propagationHasOccurred);
  }

  int intervalNo(double d) {
    if (d >= -2.0 * FloatDomain.PI && d <= -FloatDomain.PI) {
      return 1;
    }
    if (d >= -FloatDomain.PI && d <= 0.0) {
      return 2;
    }
    if (d >= 0.0 && d <= FloatDomain.PI) {
      return 3;
    }
    if (d >= FloatDomain.PI && d <= 2 * FloatDomain.PI) {
      return 4; // should not return this
    } else {
      return 0; // should not return this
    }
  }

  @Override
  public boolean satisfied() {
    return satisfiedWithTrigFunction(Math::cos);
  }

  @Override
  public String toString() {

    return id() + " : CosPeqR(" + p + ", " + q + " )";
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
      // f = cos(p)
      // f' = -sin(p) * d(p)
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(new SinPeqR(p, v1));
      Derivative.poseDerivativeConstraint(new PmulCeqR(v1, -1.0, v2));
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(v2, Derivative.getDerivative(store, p, vars, x), v));
      return v;
    } else if (f.equals(p)) {
      // f = acos(q)
      // f' = d(q) * (-1/sqrt(1-q^2))
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v3 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v4 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(new PmulQeqR(q, q, v1));
      Derivative.poseDerivativeConstraint(new PminusQeqR(new FloatVar(store, 1.0, 1.0), v1, v2));
      Derivative.poseDerivativeConstraint(new SqrtPeqR(v2, v3));
      Derivative.poseDerivativeConstraint(new PdivQeqR(new FloatVar(store, -1.0, -1.0), v3, v4));
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(Derivative.getDerivative(store, q, vars, x), v4, v));
      return v;
    }

    return null;
  }
}
