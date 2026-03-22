/*
 * Distance.java
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
import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * Constraint |X - Y| #= Z.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class Distance extends AbstractConstraintXandYandZ implements Stateful {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  boolean firstConsistencyCheck;
  int firstConsistencyLevel;

  /**
   * Distance between x and y |x-y| = z.
   *
   * @param x first parameter
   * @param y second parameter
   * @param z result
   */
  public Distance(IntVar x, IntVar y, IntVar z) {

    super(idNumber, x, y, z);
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
      z.domain.inMin(store.level, z, 0);
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
    }

    do {

      store.propagationHasOccurred = false;

      if (x.singleton()) {
        propagateWhenXsingleton(store);
      } else if (y.singleton()) {
        propagateWhenYsingleton(store);
      } else if (z.singleton()) {
        propagateWhenZsingleton(store);
      } else {
        propagateWhenNoneSingleton(store);
      }

    } while (store.propagationHasOccurred);
  }

  private void propagateWhenXsingleton(Store store) {
    int xValue = x.value();
    IntDomain yDom = y.dom();
    int ySize = yDom.noIntervals();
    IntervalDomain tempPlus4Z = new IntervalDomain(ySize);
    for (int i = ySize - 1; i >= 0; i--) {
      if (xValue >= yDom.rightElement(i)) {
        tempPlus4Z.unionAdapt(
            new Interval(xValue - yDom.rightElement(i), xValue - yDom.leftElement(i)));
      } else if (xValue >= yDom.leftElement(i)) {
        tempPlus4Z.unionAdapt(new Interval(0, xValue - yDom.leftElement(i)));
      }
    }
    IntervalDomain tempMinus4Z = new IntervalDomain(ySize);
    for (int i = 0; i < ySize; i++) {
      if (xValue <= yDom.leftElement(i)) {
        tempMinus4Z.unionAdapt(
            new Interval(-xValue + yDom.leftElement(i), -xValue + yDom.rightElement(i)));
      } else if (xValue <= yDom.rightElement(i)) {
        tempMinus4Z.unionAdapt(new Interval(0, -xValue + yDom.rightElement(i)));
      }
    }
    tempPlus4Z.addDom(tempMinus4Z);
    z.domain.in(store.level, z, tempPlus4Z);
    store.propagationHasOccurred = false;
    IntDomain zDom = z.dom();
    int zSize = z.domain.noIntervals();
    IntervalDomain temp = new IntervalDomain(zSize);
    for (int i = zSize - 1; i >= 0; i--) {
      temp.unionAdapt(new Interval(-zDom.rightElement(i), -zDom.leftElement(i)));
    }
    temp.addDom(zDom);
    y.domain.inShift(store.level, y, temp, xValue);
  }

  private void propagateWhenYsingleton(Store store) {
    int yValue = y.value();
    IntDomain xDom = x.dom();
    int xSize = x.domain.noIntervals();
    IntervalDomain temp4PlusZ = new IntervalDomain(xSize);
    IntervalDomain temp4MinusZ = new IntervalDomain(xSize);
    for (int i = 0; i < xSize; i++) {
      if (xDom.leftElement(i) - yValue >= 0) {
        temp4PlusZ.unionAdapt(
            new Interval(xDom.leftElement(i) - yValue, xDom.rightElement(i) - yValue));
      } else if (xDom.rightElement(i) - yValue >= 0) {
        temp4PlusZ.unionAdapt(0, xDom.rightElement(i) - yValue);
      }
    }
    for (int i = xSize - 1; i >= 0; i--) {
      if (xDom.rightElement(i) - yValue <= 0) {
        temp4MinusZ.unionAdapt(
            new Interval(-xDom.rightElement(i) + yValue, -xDom.leftElement(i) + yValue));
      } else if (xDom.leftElement(i) - yValue <= 0) {
        temp4MinusZ.unionAdapt(0, -xDom.leftElement(i) + yValue);
      }
    }
    temp4PlusZ.addDom(temp4MinusZ);
    z.domain.in(store.level, z, temp4PlusZ);
    store.propagationHasOccurred = false;
    IntDomain zDom = z.dom();
    int zSize = zDom.noIntervals();
    IntervalDomain temp = new IntervalDomain(zSize);
    for (int i = zSize - 1; i >= 0; i--) {
      temp.unionAdapt(new Interval(-zDom.rightElement(i), -zDom.leftElement(i)));
    }
    temp.addDom(zDom);
    x.domain.inShift(store.level, x, temp, yValue);
  }

  private void propagateWhenZsingleton(Store store) {
    int zValue = z.value();
    IntDomain xDom = x.dom();
    int xSize = xDom.noIntervals();
    IntervalDomain tempPlusC = new IntervalDomain(xSize);
    IntervalDomain tempMinusC = new IntervalDomain(xSize);
    for (int i = 0; i < xSize; i++) {
      tempPlusC.unionAdapt(
          new Interval(xDom.leftElement(i) + zValue, xDom.rightElement(i) + zValue));
      tempMinusC.unionAdapt(
          new Interval(xDom.leftElement(i) - zValue, xDom.rightElement(i) - zValue));
    }
    tempPlusC.addDom(tempMinusC);
    y.domain.in(store.level, y, tempPlusC);
    store.propagationHasOccurred = false;
    IntDomain yDom = y.dom();
    int ySize = yDom.noIntervals();
    IntervalDomain tempPlusC2 = new IntervalDomain(ySize);
    IntervalDomain tempMinusC2 = new IntervalDomain(ySize);
    for (int i = 0; i < ySize; i++) {
      tempPlusC2.unionAdapt(
          new Interval(yDom.leftElement(i) + zValue, yDom.rightElement(i) + zValue));
      tempMinusC2.unionAdapt(
          new Interval(yDom.leftElement(i) - zValue, yDom.rightElement(i) - zValue));
    }
    tempPlusC2.addDom(tempMinusC2);
    x.domain.in(store.level, x, tempPlusC2);
  }

  private void propagateWhenNoneSingleton(Store store) {
    IntervalDomain xDom1 = new IntervalDomain(y.min() - z.max(), y.max() - z.min());
    xDom1.unionAdapt(y.min() + z.min(), y.max() + z.max());
    x.domain.in(store.level, x, xDom1);
    store.propagationHasOccurred = false;
    IntervalDomain yDom1 = new IntervalDomain(x.min() + z.min(), x.max() + z.max());
    yDom1.unionAdapt(x.min() - z.max(), x.max() - z.min());
    y.domain.in(store.level, y, yDom1);
    IntervalDomain zDom1 = new IntervalDomain(y.min() - x.max(), y.max() - x.min());
    zDom1.unionAdapt(x.min() - y.max(), x.max() - y.min());
    z.domain.in(store.level, z, zDom1);
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public boolean satisfied() {
    IntDomain xDom = x.dom();
    IntDomain yDom = y.dom();
    IntDomain zDom = z.dom();
    return xDom.singleton()
        && yDom.singleton()
        && zDom.singleton()
        && Math.abs(xDom.min() - yDom.min()) == zDom.min();
  }

  @Override
  public String toString() {

    return id() + " : Distance(" + x + ", " + y + ", " + z + " )";
  }

  @Override
  public boolean notSatisfied() {

    IntDomain xDom = x.dom();
    IntDomain yDom = y.dom();
    IntDomain zDom = z.dom();
    return xDom.singleton()
        && yDom.singleton()
        && zDom.singleton()
        && Math.abs(xDom.min() - yDom.min()) != zDom.min();
  }

  @Override
  public void notConsistency(final Store store) {

    do {

      store.propagationHasOccurred = false;

      if (x.singleton()) {

        if (z.singleton()) {

          // |X - Y| = Z
          // X - Y = Z => Y = X - Z
          // -X + Y = Z => Y = X + Z

          y.domain.inComplement(store.level, y, x.value() - z.value());
          y.domain.inComplement(store.level, y, x.value() + z.value());

        } else if (y.singleton()) {

          z.domain.inComplement(store.level, z, x.value() - y.value());
          z.domain.inComplement(store.level, x, y.value() - x.value());
        }

      } else if (z.singleton() && y.singleton()) {

        // |X - Y| = Z
        // -X + Y = Z => X = Y - Z, Y = X + Z
        // X - Y = Z => X = Y + Z, Y = X - Z

        x.domain.inComplement(store.level, x, y.value() - z.value());
        x.domain.inComplement(store.level, x, y.value() + z.value());
      }

    } while (store.propagationHasOccurred);
  }
}
