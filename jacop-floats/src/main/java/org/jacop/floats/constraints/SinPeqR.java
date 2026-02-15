/*
 * SinPeqR.java
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
 * Constraints sin(P) = R.
 *
 * <p>Bounds consistency can be used; third parameter of constructor controls this.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class SinPeqR extends AbstractTrigConstraint
    implements SatisfiedPresent, FloatDerivableConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final int INCREASING = 0;
  private static final int DECREASING = 1;
  private static final int PEAK = 2;
  private static final int TROUGH = 3;
  private static final int FULL_RANGE = 4;

  /**
   * It constructs sin(P) = Q constraints.
   *
   * @param p variable P
   * @param q variable Q
   */
  public SinPeqR(FloatVar p, FloatVar q) {
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

      int category = classifyBounds(intervalForMin, intervalForMax);
      double qMin;
      double qMax;
      switch (category) {
        case INCREASING:
          qMin = FloatDomain.down(Math.sin(min));
          qMax = FloatDomain.up(Math.sin(max));
          break;
        case DECREASING:
          qMin = FloatDomain.down(Math.sin(max));
          qMax = FloatDomain.up(Math.sin(min));
          break;
        case PEAK:
          qMin = FloatDomain.down(Math.min(Math.sin(min), Math.sin(max)));
          qMax = 1.0;
          break;
        case TROUGH:
          qMin = -1.0;
          qMax = FloatDomain.up(Math.max(Math.sin(min), Math.sin(max)));
          break;
        default: // FULL_RANGE
          qMin = -1.0;
          qMax = 1.0;
          break;
      }

      q.domain.in(store.level, q, qMin, qMax);

      // p update using asin (range -PI/2..PI/2)
      // asin is increasing, so swap qMin/qMax: pMin = asin(qMin), pMax = asin(qMax)
      updatePDomain(store, qMax, qMin, Math::asin, -FloatDomain.PI / 2, FloatDomain.PI / 2);

    } while (store.propagationHasOccurred);
  }

  int intervalNo(double d) {
    if (d >= -2.0 * FloatDomain.PI && d <= -1.5 * FloatDomain.PI) {
      return 1;
    }
    if (d >= -1.5 * FloatDomain.PI && d <= -0.5 * FloatDomain.PI) {
      return 2;
    }
    if (d >= -0.5 * FloatDomain.PI && d <= 0.5 * FloatDomain.PI) {
      return 3;
    }
    if (d >= 0.5 * FloatDomain.PI && d <= 1.5 * FloatDomain.PI) {
      return 4;
    }
    if (d >= 1.5 * FloatDomain.PI && d <= 2.0 * FloatDomain.PI) {
      return 5; // should not return this
    } else {
      return 0; // should not return this
    }
  }

  /**
   * Classifies the bound-computation pattern for a pair of sin intervals.
   *
   * <p>Odd intervals (1, 3, 5) are increasing; even intervals (2, 4) are decreasing. When min and
   * max fall in the same interval the function is monotone. Adjacent intervals cross a peak
   * (odd-to-even) or trough (even-to-odd). Wider spans cover the full range.
   */
  private static int classifyBounds(int intervalForMin, int intervalForMax) {
    if (intervalForMax < intervalForMin) {
      throw new InternalException("Selected impossible case in sin, cos, asin or acos constraint");
    }
    int diff = intervalForMax - intervalForMin;
    if (diff == 0) {
      return (intervalForMin % 2 == 1) ? INCREASING : DECREASING;
    }
    if (diff == 1) {
      return (intervalForMin % 2 == 1) ? PEAK : TROUGH;
    }
    return FULL_RANGE;
  }

  @Override
  public boolean satisfied() {
    return satisfiedWithTrigFunction(Math::sin);
  }

  @Override
  public String toString() {

    return id() + " : SinPeqR(" + p + ", " + q + " )";
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
      // f = sin(p)
      // f' = cos(p) * d(p)
      FloatVar v = newDeriv(store);
      FloatVar v1 = newDeriv(store);
      Derivative.poseDerivativeConstraint(new CosPeqR(p, v1));
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(v1, Derivative.getDerivative(store, p, vars, x), v));
      return v;
    } else if (f.equals(p)) {
      // f = asin(q)
      // f' = d(q) * 1/sqrt(1-q^2)
      FloatVar v = newDeriv(store);
      FloatVar v1 = newDeriv(store);
      FloatVar v2 = newDeriv(store);
      FloatVar v3 = newDeriv(store);
      FloatVar v4 = newDeriv(store);
      Derivative.poseDerivativeConstraint(new PmulQeqR(q, q, v1));
      Derivative.poseDerivativeConstraint(new PminusQeqR(new FloatVar(store, 1.0, 1.0), v1, v2));
      Derivative.poseDerivativeConstraint(new SqrtPeqR(v2, v3));
      Derivative.poseDerivativeConstraint(new PdivQeqR(new FloatVar(store, 1.0, 1.0), v3, v4));
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(Derivative.getDerivative(store, q, vars, x), v4, v));
      return v;
    }

    return null;
  }
}
