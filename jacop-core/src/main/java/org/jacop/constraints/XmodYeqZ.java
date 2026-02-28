/*
 * XmodYeqZ.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Constraint X mod Y = Z.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XmodYeqZ extends AbstractXopYeqZ {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs a constraint X mod Y = Z.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XmodYeqZ(IntVar x, IntVar y, IntVar z) {
    super(idNumber, x, y, z);
  }

  @Override
  public void consistency(final Store store) {

    int resultMin = IntDomain.MIN_INT;
    int resultMax = IntDomain.MAX_INT;

    y.domain.inComplement(store.level, y, 0);

    do {
      store.propagationHasOccurred = false;
      int[] result = propagateOneRound(store, resultMin, resultMax);
      resultMin = result[0];
      resultMax = result[1];
    } while (store.propagationHasOccurred);

    if (ASSERTS_ENABLED && checkSolution(resultMin, resultMax) != null) {
      throw new IllegalStateException(String.valueOf(checkSolution(resultMin, resultMax)));
    }
  }

  private int[] propagateOneRound(Store store, int resultMin, int resultMax) {
    int[] reminderBounds = computeReminderBounds();
    int reminderMin = reminderBounds[0];
    int reminderMax = reminderBounds[1];

    z.domain.in(store.level, z, reminderMin, reminderMax);

    if (y.singleton()) {
      propagateWhenYSingleton(store);
    }

    if (x.singleton()) {
      propagateWhenXSingleton(store);
    }

    reminderMin = z.min();
    reminderMax = z.max();

    if (y.min() > 0 || y.max() < 0) {
      resultMin = propagateNonZeroY(store, resultMin, resultMax, reminderMin, reminderMax);
      resultMax = resultMaxFromLastPropagate;
    }
    return new int[] {resultMin, resultMax};
  }

  private int resultMaxFromLastPropagate;

  private int[] computeReminderBounds() {
    if (x.min() >= 0) {
      return computeReminderBoundsXNonNegative();
    }
    if (x.max() < 0) {
      return computeReminderBoundsXNegative();
    }
    return computeReminderBoundsXMixed();
  }

  private int[] computeReminderBoundsXNonNegative() {
    int reminderMax = Math.max(Math.abs(y.min()), Math.abs(y.max())) - 1;
    reminderMax = Math.min(reminderMax, x.max());
    return new int[] {0, reminderMax};
  }

  private int[] computeReminderBoundsXNegative() {
    int reminderMin = -Math.max(Math.abs(y.min()), Math.abs(y.max())) + 1;
    reminderMin = Math.max(reminderMin, x.min());
    return new int[] {reminderMin, 0};
  }

  private int[] computeReminderBoundsXMixed() {
    int reminderMin = Math.min(Math.min(y.min(), -y.min()), Math.min(y.max(), -y.max())) + 1;
    int reminderMax = Math.max(Math.max(y.min(), -y.min()), Math.max(y.max(), -y.max())) - 1;
    reminderMin = Math.max(reminderMin, x.min());
    reminderMax = Math.min(reminderMax, x.max());
    return new int[] {reminderMin, reminderMax};
  }

  private void propagateWhenYSingleton(Store store) {
    if (x.domain.getSize() < 100) {
      int absY = Math.abs(y.value());
      IntDomain d = makeDomain(x, absY, z);
      x.domain.in(store.level, x, d);
    } else {
      int absY = Math.abs(y.value());
      IntDomain zDom = z.dom();
      int xMin = x.min();
      boolean found = false;
      for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
        xMin = e.nextElement();
        if (zDom.contains(xMin % absY)) {
          found = true;
          break;
        }
      }
      if (found) {
        x.domain.inMin(store.level, x, xMin);
      } else {
        throw Store.failException;
      }
      int xMax = x.max();
      int xMinVal = x.min();
      while (!zDom.contains(xMax % absY) && xMax >= xMinVal) {
        xMax--;
      }
      if (xMax >= xMinVal) {
        x.domain.inMax(store.level, x, xMax);
      } else {
        throw Store.failException;
      }
    }
  }

  private void propagateWhenXSingleton(Store store) {
    if (!z.domain.contains(x.value() % Math.abs(y.min()))) {
      y.domain.inMin(store.level, y, y.min() + 1);
    } else if (!z.domain.contains(x.value() % Math.abs(y.max()))) {
      y.domain.inMax(store.level, y, y.max() - 1);
    }
  }

  private int propagateNonZeroY(
      Store store, int resultMin, int resultMax, int reminderMin, int reminderMax) {
    int oldResultMin = resultMin;
    int oldResultMax = resultMax;
    Interval result = IntDomain.divBounds(x.min(), x.max(), y.min(), y.max());
    resultMin = result.min();
    resultMaxFromLastPropagate = result.max();
    if (oldResultMin != resultMin || oldResultMax != resultMaxFromLastPropagate) {
      store.propagationHasOccurred = true;
    }
    Interval yBounds =
        IntDomain.divBounds(
            x.min() - reminderMax, x.max() - reminderMin, resultMin, resultMaxFromLastPropagate);
    y.domain.in(store.level, y, yBounds.min(), yBounds.max());
    Interval reminder =
        IntDomain.mulBounds(resultMin, resultMaxFromLastPropagate, y.min(), y.max());
    int zMin = reminder.min();
    int zMax = reminder.max();
    int newReminderMin = x.min() - zMax;
    int newReminderMax = x.max() - zMin;
    z.domain.in(store.level, z, newReminderMin, newReminderMax);
    x.domain.in(store.level, x, zMin + z.min(), zMax + z.max());
    return resultMin;
  }

  IntDomain makeDomain(IntVar x, int y, IntVar z) {
    IntervalDomain d = new IntervalDomain();
    boolean empty = true;
    IntDomain zDom = z.dom();
    for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int val = e.nextElement();
      if (zDom.contains(val % y)) {
        empty = false;
        if (d.getSize() == 0) {
          d.unionAdapt(val);
        } else {
          d.addLastElement(val);
        }
      }
    }
    if (empty) {
      throw Store.failException;
    }
    return d;
  }

  @Override
  public boolean satisfied() {
    return grounded() && z.min() == mod(x.min(), y.min());
  }

  @Override
  public String toString() {

    return id() + " : XmodYeqZ(" + x + ", " + y + ", " + z + " )";
  }

  private String checkSolution(int resultMin, int resultMax) {
    String result;

    if (z.singleton() && y.singleton() && x.singleton()) {
      result =
          "Operation mod does not hold "
              + x
              + " mod "
              + y
              + " = "
              + z
              + "(result "
              + resultMin
              + ".."
              + resultMax;
      for (int i = resultMin; i <= resultMax; i++) {
        if (i * y.value() + z.value() == x.value()) {
          result = null;
        }
      }
    } else {
      result = null;
    }
    return result;
  }

  private int div(int a, int b) {
    return (int) Math.floor((float) a / (float) b);
  }

  private int mod(int a, int b) {
    return a - div(a, b) * b;
  }
}
