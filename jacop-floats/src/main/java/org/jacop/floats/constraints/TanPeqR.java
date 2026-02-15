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
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatInterval;
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
public class TanPeqR extends Constraint implements SatisfiedPresent {

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
      if (p.min() < -FloatDomain.PI || p.max() > FloatDomain.PI) {
        FloatInterval normP = normalize(p);
        min = normP.min();
        max = normP.max();
      }

      FloatInterval minMax = new FloatInterval(min, max);
      if (minMax.singleton()) {
        if ((FloatDomain.PI / 2 >= min && FloatDomain.PI / 2 <= max)
            || (-FloatDomain.PI / 2 >= min && -FloatDomain.PI / 2 <= max)) {
          throw Store.failException;
        }
      }

      double[] qBounds = computeTanQBounds(min, max);
      if (qBounds == null) {
        return;
      }

      q.domain.in(store.level, q, qBounds[0], qBounds[1]);
      updatePFromQ(store, qBounds[0], qBounds[1]);

    } while (store.propagationHasOccurred);
  }

  /** Returns {qMin, qMax} or null if we should return from the loop. */
  private double[] computeTanQBounds(double min, double max) {
    int intervalForMin = intervalNo(min);
    int intervalForMax = intervalNo(max);

    switch (intervalForMin) {
      case 1:
        if (intervalForMax != 1) {
          return null;
        }
        return qBoundsInterval1(min, max);
      case 2:
        if (intervalForMax != 2) {
          return null;
        }
        return qBoundsInterval2(min, max);
      case 3:
        if (intervalForMax != 3) {
          return null;
        }
        return qBoundsInterval3(min, max);
      default:
        return null;
    }
  }

  private static double[] qBoundsInterval1(double min, double max) {
    double qMin = FloatDomain.down(Math.tan(min));
    double qMax = FloatDomain.up(Math.tan(max));
    if (qMax < 0) {
      qMax = FloatDomain.MAX_FLOAT;
    }
    return new double[] {qMin, qMax};
  }

  private static double[] qBoundsInterval2(double min, double max) {
    double qMin = FloatDomain.down(Math.tan(min));
    double qMax = FloatDomain.up(Math.tan(max));
    if (qMin > qMax) {
      if (qMax > 0) {
        qMin = -FloatDomain.MAX_FLOAT;
      } else if (qMin < 0) {
        qMax = FloatDomain.MAX_FLOAT;
      }
    }
    return new double[] {qMin, qMax};
  }

  private static double[] qBoundsInterval3(double min, double max) {
    double qMin = FloatDomain.down(Math.tan(min));
    double qMax = FloatDomain.up(Math.tan(max));
    if (qMin > 0) {
      qMin = -FloatDomain.MAX_FLOAT;
    }
    return new double[] {qMin, qMax};
  }

  private void updatePFromQ(Store store, double qMin, double qMax) {
    double pMin = Math.atan(qMin);
    double pMax = Math.atan(qMax);
    pMin = FloatDomain.down(pMin);
    pMax = FloatDomain.up(pMax);
    if (java.lang.Double.isNaN(pMin)) {
      pMin = -FloatDomain.PI / 2;
    }
    if (java.lang.Double.isNaN(pMax)) {
      pMax = FloatDomain.PI / 2;
    }
    double k = Math.floor(p.min() / FloatDomain.PI);
    double low = FloatDomain.down(pMin + k * FloatDomain.PI);
    k = Math.ceil(p.max() / FloatDomain.PI);
    double high = FloatDomain.up(pMax + k * FloatDomain.PI);
    FloatIntervalDomain pDom = new FloatIntervalDomain(low, high);
    p.domain.in(store.level, p, pDom);
  }

  /*
   * Normalizes argument to interval -PI..PI
   */
  FloatInterval normalize(FloatVar v) {
    double min = v.min();
    double max = v.max();

    double normMin = min % FloatDomain.PI;
    double normMax = normMin + max - min;

    if (normMax >= FloatDomain.PI) {
      normMin -= FloatDomain.PI;
      normMax -= FloatDomain.PI;
    }

    return new FloatInterval(normMin, normMax);
  }

  int intervalNo(double d) {
    if (d >= -FloatDomain.PI && d < -FloatDomain.PI / 2) {
      return 1;
    }
    if (d >= -FloatDomain.PI / 2 && d < FloatDomain.PI / 2) {
      return 2;
    }
    if (d >= FloatDomain.PI / 2 && d <= FloatDomain.PI) {
      return 3; // undefined
    } else {
      return 0; // undefined
    }
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
}
