/*
 * AbstractTrigConstraint.java
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

import java.util.function.DoubleUnaryOperator;
import org.jacop.api.Stateful;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Abstract base class for trigonometric float constraints (cos, sin, etc.).
 *
 * <p>Provides shared fields and methods for constraints of the form trig(P) = Q.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractTrigConstraint extends Constraint implements Stateful {

  /** It contains variable p. */
  protected final FloatVar p;

  /** It contains variable q. */
  protected final FloatVar q;

  /** Flag indicating if this is the first consistency check. */
  protected boolean firstConsistencyCheck = true;

  /** The backtracking level at which first consistency check occurred. */
  protected int firstConsistencyLevel;

  /**
   * It constructs a trigonometric constraint trig(P) = Q.
   *
   * @param p variable P
   * @param q variable Q
   */
  protected AbstractTrigConstraint(FloatVar p, FloatVar q) {

    checkInputForNullness(new String[] {"p", "q"}, new Object[] {p, q});

    this.queueIndex = 1;
    this.p = p;
    this.q = q;

    setScope(p, q);
  }

  @Override
  public void removeLevel(int level) {
    if (level == firstConsistencyLevel) {
      firstConsistencyCheck = true;
    }
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      q.domain.in(store.level, q, -1.0, 1.0);
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
    }

    boundConsistency(store);
  }

  /**
   * Performs bound consistency propagation specific to the trigonometric function.
   *
   * @param store the constraint store
   */
  protected abstract void boundConsistency(Store store);

  /**
   * Normalizes an angle variable to the range [-2*PI, 2*PI].
   *
   * @param v the variable to normalize
   * @return the normalized interval
   */
  protected FloatInterval normalize(FloatVar v) {
    return org.jacop.floats.core.FloatDomain.normalizeAngle(v.min(), v.max());
  }

  /**
   * Checks if the constraint is satisfied when both variables are grounded, using the given
   * trigonometric function.
   *
   * @param trigFunction the trigonometric function to apply (e.g., Math::cos, Math::sin, Math::tan)
   * @return true if the constraint is satisfied, false otherwise
   */
  protected boolean satisfiedWithTrigFunction(DoubleUnaryOperator trigFunction) {
    return satisfiedWithTrigFunctionStatic(p, q, trigFunction);
  }

  /**
   * Static helper method to check if a trigonometric constraint is satisfied when both variables
   * are grounded.
   *
   * @param p the input variable
   * @param q the output variable
   * @param trigFunction the trigonometric function to apply (e.g., Math::cos, Math::sin, Math::tan)
   * @return true if the constraint is satisfied, false otherwise
   */
  static boolean satisfiedWithTrigFunctionStatic(
      FloatVar p, FloatVar q, DoubleUnaryOperator trigFunction) {
    if (p.singleton() && q.singleton()) {
      double trigMin = trigFunction.applyAsDouble(p.min());
      double trigMax = trigFunction.applyAsDouble(p.max());

      FloatInterval minDiff =
          trigMin < q.min()
              ? new FloatInterval(trigMin, q.min())
              : new FloatInterval(q.min(), trigMin);
      FloatInterval maxDiff =
          trigMax < q.max()
              ? new FloatInterval(trigMax, q.max())
              : new FloatInterval(q.max(), trigMax);

      return minDiff.singleton() && maxDiff.singleton();
    } else {
      return false;
    }
  }

  /**
   * Updates the p variable domain based on q bounds using the inverse trigonometric function.
   *
   * @param store the constraint store
   * @param qMin the minimum value of q
   * @param qMax the maximum value of q
   * @param inverseFunc the inverse trigonometric function (e.g., Math::acos, Math::asin)
   * @param nanMin the value to use for pMin when inverseFunc returns NaN
   * @param nanMax the value to use for pMax when inverseFunc returns NaN
   */
  protected void updateFirstDomainFromSecond(
      Store store,
      double qminValue,
      double qmaxValue,
      DoubleUnaryOperator inverseFunc,
      double nanMin,
      double nanMax) {
    // p update
    double pMin = inverseFunc.applyAsDouble(qmaxValue);
    double pMax = inverseFunc.applyAsDouble(qminValue);

    pMin = FloatDomain.down(pMin);
    pMax = FloatDomain.up(pMax);
    if (java.lang.Double.isNaN(pMin)) {
      pMin = nanMin;
    }
    if (java.lang.Double.isNaN(pMax)) {
      pMax = nanMax;
    }

    double k = Math.floor(p.min() / (2 * FloatDomain.PI));
    double low = FloatDomain.down(pMin + 2 * k * FloatDomain.PI);
    k = Math.ceil(p.max() / (2 * FloatDomain.PI));
    double high = FloatDomain.up(pMax + 2 * k * FloatDomain.PI);
    FloatIntervalDomain pDom = new FloatIntervalDomain(low, high);

    p.domain.in(store.level, p, pDom);
  }

  /**
   * Checks if the p domain spans a full period (2*PI) or more, in which case no propagation is
   * needed.
   *
   * @return true if p domain spans >= 2*PI
   */
  protected boolean spansFullPeriod() {
    return p.max() - p.min() >= 2 * FloatDomain.PI;
  }

  /**
   * Normalizes p bounds to [-2*PI, 2*PI] if needed and returns the normalized min and max.
   *
   * @return array with [normalizedMin, normalizedMax]
   */
  protected double[] getNormalizedBounds() {
    double min = p.min();
    double max = p.max();
    if (p.min() < -2 * FloatDomain.PI || p.max() > 2 * FloatDomain.PI) {
      // normalize to -2*PI..2*PI
      FloatInterval normP = normalize(p);
      min = normP.min();
      max = normP.max();
    }
    return new double[] {min, max};
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  /**
   * Creates a new derivative variable with full float range.
   *
   * @param store the constraint store
   * @return a new FloatVar with Derivative min/max bounds
   */
  protected static FloatVar newDeriv(Store store) {
    return new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
  }

  @Override
  public abstract String toString();
}
