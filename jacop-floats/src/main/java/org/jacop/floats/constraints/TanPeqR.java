/*
 * TanPeqR.java
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
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Constraints sin(P) = R.
 *
 * <p>Bounds consistency can be used; third parameter of constructor controls this.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class TanPeqR extends Constraint implements SatisfiedPresent, Copyable<TanPeqR> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It contains variable p. */
  public final FloatVar p;

  /** It contains variable q. */
  public final FloatVar q;

  /**
   * It constructs sin(P) = Q constraints.
   *
   * @param p variable P
   * @param q variable Q
   */
  public TanPeqR(FloatVar p, FloatVar q) {

    checkInputForNullness(new String[] {"p", "q"}, new Object[] {p, q});

    numberId = idNumber.incrementAndGet();

    this.queueIndex = 1;
    this.p = p;
    this.q = q;

    setScope(p, q);
  }

  @Override
  public void consistency(Store store) {

    boundConsistency(store);
  }

  void boundConsistency(Store store) {

    if (p == q) {
      // tan(x) - x is increasing between the poles at -PI/2 and PI/2, so 0 is the only solution
      // there, which bound propagation would only approach by about x^3 per pass; Math.PI / 2 is
      // below the real pole, so the open intervals removed hold no other solution
      double pole = FloatDomain.PI / 2;
      FloatIntervalDomain outside = new FloatIntervalDomain(FloatDomain.MIN_FLOAT, -pole);
      outside.unionAdapt(0.0, 0.0);
      outside.unionAdapt(pole, FloatDomain.MAX_FLOAT);
      p.domain.in(store.level, p, outside);
    }

    if (p.max() - p.min() >= FloatDomain.PI) {
      return;
    }

    do {
      store.propagationHasOccurred = false;

      if (satisfied()) {
        return;
      }

      double min = p.min();
      double max = p.max();

      // p is narrower than PI, so it contains a pole of tan iff cos changes sign over it; Math.cos
      // reduces its argument exactly, so the signs are right far from zero too
      double cosMin = Math.cos(min);
      double cosMax = Math.cos(max);
      if (cosMin == 0.0 || cosMax == 0.0 || (cosMin < 0) != (cosMax < 0)) {
        // a pole is in p, also when p is a singleton (an interval up to the precision wide): tan
        // rises from tan(min) to +inf left of it and from -inf to tan(max) right of it
        if (!prunePole(store, min, max)) {
          return;
        }
        continue;
      }

      // tan is increasing between two poles
      double qMin = FloatDomain.down(Math.tan(min));
      double qMax = FloatDomain.up(Math.tan(max));
      q.domain.in(store.level, q, qMin, qMax);

      updateFirstDomainFromSecond(store, qMin, qMax);

    } while (store.propagationHasOccurred);
  }

  /**
   * Prunes p and q when p, narrower than PI, contains the pole between the branch of min and the
   * branch of max.
   *
   * @return false when the branches cannot be told apart and nothing is pruned
   */
  private boolean prunePole(Store store, double min, double max) {
    double kRight = Math.rint(max / FloatDomain.PI);
    double kLeft = kRight - 1;
    if (Math.rint(min / FloatDomain.PI) != kLeft || cosMinOrMaxZero(min, max)) {
      return false;
    }
    double tanMin = FloatDomain.down(Math.tan(min));
    double tanMax = FloatDomain.up(Math.tan(max));
    boolean left = q.max() >= tanMin;
    boolean right = q.min() <= tanMax;
    if (!left && !right) {
      throw Store.failException;
    }
    FloatIntervalDomain pDom = new FloatIntervalDomain(4);
    if (left) {
      double high = FloatDomain.up(Math.atan(q.max())) + kLeft * FloatDomain.PI;
      high = FloatDomain.up(high + AbstractTrigConstraint.reductionError(high, FloatDomain.PI));
      pDom.unionAdapt(min, Math.max(min, high));
    }
    if (right) {
      double low = FloatDomain.down(Math.atan(q.min())) + kRight * FloatDomain.PI;
      low = FloatDomain.down(low - AbstractTrigConstraint.reductionError(low, FloatDomain.PI));
      pDom.unionAdapt(Math.min(low, max), max);
    }
    p.domain.in(store.level, p, pDom);
    if (tanMax < tanMin) {
      FloatIntervalDomain qDom = new FloatIntervalDomain(FloatDomain.MIN_FLOAT, tanMax);
      qDom.unionAdapt(tanMin, FloatDomain.MAX_FLOAT);
      q.domain.in(store.level, q, qDom);
    }
    return true;
  }

  private static boolean cosMinOrMaxZero(double min, double max) {
    return Math.cos(min) == 0.0 || Math.cos(max) == 0.0;
  }

  private void updateFirstDomainFromSecond(Store store, double qminValue, double qmaxValue) {
    double pMin = Math.atan(qminValue);
    double pMax = Math.atan(qmaxValue);
    pMin = FloatDomain.down(pMin);
    pMax = FloatDomain.up(pMax);
    if (Double.isNaN(pMin)) {
      pMin = -FloatDomain.PI / 2;
    }
    if (Double.isNaN(pMax)) {
      pMax = FloatDomain.PI / 2;
    }
    // k * PI is computed in doubles, so widen the shifted bounds by its error
    double k = Math.floor(p.min() / FloatDomain.PI);
    double low = pMin + k * FloatDomain.PI;
    low = FloatDomain.down(low - AbstractTrigConstraint.reductionError(low, FloatDomain.PI));
    k = Math.ceil(p.max() / FloatDomain.PI);
    double high = pMax + k * FloatDomain.PI;
    high = FloatDomain.up(high + AbstractTrigConstraint.reductionError(high, FloatDomain.PI));
    FloatIntervalDomain pDom = new FloatIntervalDomain(low, high);
    p.domain.in(store.level, p, pDom);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    return AbstractTrigConstraint.satisfiedWithTrigFunctionStatic(p, q, Math::tan);
  }

  @Override
  public String toString() {

    return id() + " : TanPeqR(" + p + ", " + q + " )";
  }

  @Override
  public TanPeqR copy(VarMap map) {
    return new TanPeqR(map.get(p), map.get(q));
  }
}
