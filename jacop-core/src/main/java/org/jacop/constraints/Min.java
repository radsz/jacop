/*
 * Min.java
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

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Min constraint implements the minimum/2 constraint. It provides the minimum varable from all FD
 * varaibles on the list.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Min extends AbstractMinMax {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable min, which stores the minimum value within the whole list. */
  private final IntVar min;

  /**
   * It constructs min constraint.
   *
   * @param min variable denoting the minimal value
   * @param list the array of variables for which the minimal value is imposed.
   */
  public Min(IntVar[] list, IntVar min) {

    super(idNumber, list, min);
    this.min = min;
  }

  /**
   * It constructs min constraint.
   *
   * @param min variable denoting the minimal value
   * @param list the array of variables for which the minimal value is imposed.
   */
  public Min(List<? extends IntVar> list, IntVar min) {
    this(list.toArray(new IntVar[0]), min);
  }

  @Override
  public void consistency(Store store) {

    int start = position.value();

    do {

      store.propagationHasOccurred = false;
      IntVar v;
      IntDomain vDom;

      int minValue = IntDomain.MAX_INT;
      int maxValue = IntDomain.MAX_INT;

      int minMin = min.min();
      int maxMin = min.max();
      for (int i = start; i < l; i++) {
        v = list[i];

        vDom = v.dom();
        int varMin = vDom.min();
        int varMax = vDom.max();

        if (varMin > maxMin) {
          swap(start, i);
          start++;
        } else if (varMin < minMin) {
          v.domain.inMin(store.level, v, minMin);
        }

        minValue = Math.min(minValue, varMin);
        maxValue = Math.min(maxValue, varMax);
      }

      min.domain.in(store.level, min, minValue, maxValue);

      if (start == l) { // all variables have their min value greater than max value of min variable
        throw Store.failException;
      }

      if (start
          == list.length
              - 1) { // one variable on the list is minimal; its is max < min of all other variables
        list[start].domain.in(store.level, list[start], min.dom());

        if (min.singleton()) {
          removeConstraint();
        }
      }
    } while (store.propagationHasOccurred);

    position.update(start);
  }

  @Override
  public boolean satisfied() {

    if (!min.singleton()) {
      return false;
    }

    int minValue = min.max();
    int i = 0;
    boolean eq = false;

    while (i < list.length) {
      if (list[i].min() < minValue) {
        return false;
      }
      if (!eq && list[i].singleton() && list[i].value() == minValue) {
        eq = true;
      }
      i++;
    }

    return eq;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());

    result.append(" : min( [ ");
    appendArrayToString(result, list);
    result.append("], ").append(this.min);
    result.append(")");

    return result.toString();
  }
}
