/*
 * AbsXeqY.java
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

import java.util.concurrent.atomic.AtomicInteger;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;

/**
 * Constraints |X| #= Y.
 *
 * <p>Domain and bounds consistency can be used; third parameter of constructor controls this.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class AbsXeqY extends AbstractConstraintXandY implements Stateful {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  static final boolean DEBUG_ALL = false;

  boolean firstConsistencyCheck = true;
  boolean domainConsistent;
  int firstConsistencyLevel;

  /**
   * It constructs |X| = Y constraints.
   *
   * @param x variable X1
   * @param y variable Y
   */
  public AbsXeqY(IntVar x, IntVar y) {

    super(idNumber, x, y);

    this.queueIndex = 0;
  }

  /**
   * It constructs |X| = Y constraints.
   *
   * @param x variable X1
   * @param y variable Y
   * @param domConsistency controls which consistency method is used; true = domain, false = bound
   */
  public AbsXeqY(IntVar x, IntVar y, boolean domConsistency) {
    this(x, y);

    domainConsistent = domConsistency;

    if (domainConsistent) {
      this.queueIndex = 1;
    } else {
      this.queueIndex = 0;
    }
  }

  @Override
  public void removeLevel(int level) {
    if (level == firstConsistencyLevel) {
      firstConsistencyCheck = true;
    }
  }

  @Override
  public void consistency(final Store store) {

    if (firstConsistencyCheck) {
      y.domain.inMin(store.level, y, 0);
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
    }

    if (domainConsistent) {
      domainConsistency(store);
    } else {
      boundConsistency(store);
    }
  }

  void domainConsistency(final Store store) {

    do {

      store.propagationHasOccurred = false;

      if (DEBUG_ALL) {
        log.debug("X {} Y {}", x, y);
      }

      IntervalDomain xDom = xDomainAsInterval();

      IntervalDomain yDom1 = computeYDom1FromX(xDom);
      IntervalDomain yDom = computeYDomFromX(xDom, yDom1);

      if (DEBUG_ALL) {
        log.debug("new Ydom {}", yDom);
      }

      y.domain.in(store.level, y, yDom);

      IntervalDomain yDomAsInterval = yDomainAsInterval();
      IntervalDomain xDomFromY = computeXDomFromY(yDomAsInterval);

      if (DEBUG_ALL) {
        log.debug("new Xdom {}", xDomFromY);
      }

      x.domain.in(store.level, x, xDomFromY);

    } while (store.propagationHasOccurred);
  }

  private IntervalDomain xDomainAsInterval() {
    if (x.domain.domainId() == IntDomain.INTERVAL_DOMAIN_ID) {
      return (IntervalDomain) x.domain;
    }
    if (x.domain.domainId() == IntDomain.SMALL_DENSE_DOMAIN_ID) {
      return ((SmallDenseDomain) x.domain).toIntervalDomain();
    }
    IntervalDomain xDom = new IntervalDomain();
    IntervalEnumeration enumer = x.domain.intervalEnumeration();
    while (enumer.hasMoreElements()) {
      Interval next = enumer.nextElement();
      xDom.unionAdapt(next);
    }
    return xDom;
  }

  private IntervalDomain computeYDom1FromX(IntervalDomain xDom) {
    IntervalDomain yDom1 = new IntervalDomain(xDom.size + 1);
    Interval[] intervals = xDom.intervals;
    int i = 0;
    for (; i < xDom.size; i++) {
      if (intervals[i].max() > 0) {
        break;
      }
    }
    int j = i == xDom.size ? i - 1 : i;
    for (; j >= 0; j--) {
      if (intervals[j].max() <= 0) {
        yDom1.unionAdapt(-intervals[j].max(), -intervals[j].min());
      }
    }
    if (i < xDom.size && intervals[i].min() < 0 && intervals[i].max() > 0) {
      if (-intervals[i].min() > intervals[i].max()) {
        yDom1.unionAdapt(0, -intervals[i].min());
      } else {
        yDom1.unionAdapt(0, intervals[i].max());
      }
    }
    return yDom1;
  }

  private IntervalDomain computeYDomFromX(IntervalDomain xDom, IntervalDomain yDom1) {
    Interval[] intervals = xDom.intervals;
    int i = 0;
    for (; i < xDom.size; i++) {
      if (intervals[i].max() > 0) {
        break;
      }
    }
    IntervalDomain yDom = new IntervalDomain(xDom.size + 1);
    for (; i < xDom.size; i++) {
      yDom.unionAdapt(intervals[i]);
    }
    yDom.addDom(yDom1);
    return yDom;
  }

  private IntervalDomain yDomainAsInterval() {
    if (y.domain.domainId() == IntDomain.INTERVAL_DOMAIN_ID) {
      return (IntervalDomain) y.domain;
    }
    if (y.domain.domainId() == IntDomain.SMALL_DENSE_DOMAIN_ID) {
      return ((SmallDenseDomain) y.domain).toIntervalDomain();
    }
    IntervalDomain yDom = new IntervalDomain();
    IntervalEnumeration enumer = y.domain.intervalEnumeration();
    while (enumer.hasMoreElements()) {
      Interval next = enumer.nextElement();
      yDom.unionAdapt(next);
    }
    return yDom;
  }

  private IntervalDomain computeXDomFromY(IntervalDomain yDom) {
    IntervalDomain xDom = new IntervalDomain(yDom.size + 1);
    for (int i = yDom.size - 1; i >= 0; i--) {
      xDom.unionAdapt(-yDom.intervals[i].max(), -yDom.intervals[i].min());
    }
    xDom.addDom(yDom);
    return xDom;
  }

  void boundConsistency(final Store store) {

    do {

      if (x.min() >= 0) {
        // possible domain consistecny for this case

        // bounds consistency
        x.domain.in(store.level, x, y.min(), y.max());

        store.propagationHasOccurred = false;

        y.domain.in(store.level, y, x.min(), x.max());
      } else if (x.max() < 0) {
        x.domain.in(store.level, x, -y.max(), -y.min());

        store.propagationHasOccurred = false;

        y.domain.in(store.level, y, -x.max(), -x.min());
      } else { // x.min() < 0 && x.max() >= 0
        IntervalDomain xBound;
        if (y.min() == 0) {
          xBound = new IntervalDomain(-y.max(), y.max());
        } else {
          xBound = new IntervalDomain(-y.max(), -y.min());
          xBound.unionAdapt(new Interval(y.min(), y.max()));
        }

        x.domain.in(store.level, x, xBound);

        store.propagationHasOccurred = false;

        y.domain.inMax(store.level, y, Math.max(-x.min(), x.max()));
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    if (domainConsistent) {
      return IntDomain.ANY;
    } else {
      return IntDomain.BOUND;
    }
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    if (domainConsistent) {
      return IntDomain.ANY;
    } else {
      return IntDomain.BOUND;
    }
  }

  @Override
  public void notConsistency(final Store store) {

    do {
      store.propagationHasOccurred = false;

      if (y.singleton()) {

        x.domain.inComplement(store.level, x, y.value());
        x.domain.inComplement(store.level, x, -y.value());
      }

      if (x.singleton()) {

        if (x.value() >= 0) {
          y.domain.inComplement(store.level, y, x.value());
        } else {
          y.domain.inComplement(store.level, y, -x.value());
        }
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean notSatisfied() {
    IntDomain xDom = x.domain;
    IntDomain yDom = y.domain;
    int xSize = xDom.noIntervals();
    for (int i = 0; i < xSize; i++) {
      if (yIntersectsAbsImage(xDom, yDom, i)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Returns true if yDom intersects the image of the i-th x-interval under the absolute value map.
   */
  private boolean yIntersectsAbsImage(IntDomain xDom, IntDomain yDom, int i) {
    int right = xDom.rightElement(i);
    int left = xDom.leftElement(i);
    if (right <= 0) {
      return yDom.isIntersecting(-right, -left);
    }
    if (left >= 0) {
      return yDom.isIntersecting(left, right);
    }
    return yDom.isIntersecting(0, -left) || yDom.isIntersecting(0, right);
  }

  @Override
  public boolean satisfied() {
    return grounded() && (x.min() == y.min() || -x.min() == y.min());
  }

  @Override
  public String toString() {

    return id() + " : absXeqY(" + x + ", " + y + " )";
  }
}
