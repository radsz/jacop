/*
 * ArgMax.java
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * ArgMax constraint provides the index of the maximum variable from all variables on the list.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ArgMax extends AbstractArgMinMax {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs max constraint.
   *
   * @param maxIndex variable denoting the index of the maximum value
   * @param list the array of variables for which the index of the maximum value is imposed.
   * @param indexOffset the offset for the index that is computed from 1 by default (if needed from
   *     0, use -1 for this parameter)
   */
  public ArgMax(IntVar[] list, IntVar maxIndex, int indexOffset) {
    this(list, maxIndex);
    this.indexOffset = indexOffset;
  }

  /**
   * It constructs max constraint with default index offset of 0.
   *
   * @param list the array of variables for which the index of the maximum value is imposed.
   * @param maxIndex variable denoting the index of the maximum value
   */
  public ArgMax(IntVar[] list, IntVar maxIndex) {
    super(idNumber, list, maxIndex);
  }

  /**
   * It constructs max constraint.
   *
   * @param maxIndex variable denoting index of the maximum value
   * @param variables the array of variables for which the maximum value is imposed.
   * @param indexOffset the offset for the index that is computed from 1 by default (if needed from
   *     0, use -1 for this parameter)
   */
  public ArgMax(List<? extends IntVar> variables, IntVar maxIndex, int indexOffset) {
    this(variables, maxIndex);
    this.indexOffset = indexOffset;
  }

  /**
   * It constructs max constraint with default index offset of 0.
   *
   * @param variables the list of variables for which the index of the maximum value is imposed.
   * @param maxIndex variable denoting the index of the maximum value
   */
  public ArgMax(List<? extends IntVar> variables, IntVar maxIndex) {
    this(variables.toArray(new IntVar[0]), maxIndex);
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      extremeIndex.domain.in(store.level, extremeIndex, 1 + indexOffset, list.length + indexOffset);
      firstConsistencyCheck = false;
    }

    do {

      store.propagationHasOccurred = false;

      int[] lbUbPos = findLbUbPosForMax();
      int lb = lbUbPos[0];
      int ub = lbUbPos[1];
      int pos = lbUbPos[2];

      if (lb == ub) {
        extremeIndex.domain.inMax(store.level, extremeIndex, pos + 1 + indexOffset);
      }

      IntervalDomain idxDomain = buildIdxDomainForMax(lb);
      if (idxDomain.isEmpty()) {
        throw Store.failException;
      }
      extremeIndex.domain.in(store.level, extremeIndex, idxDomain);

      int[] ubPos = findUbPosForMax();
      int ub2 = ubPos[0];
      int pos2 = ubPos[1];
      if (list[pos2].singleton()) {
        extremeIndex.domain.in(
            store.level, extremeIndex, pos2 + 1 + indexOffset, pos2 + 1 + indexOffset);
      }

      if (extremeIndex.singleton()) {
        pruneWhenExtremeIndexSingletonMax(store);
      } else {
        pruneWhenExtremeIndexNotSingletonMax(store, ub2);
      }
    } while (store.propagationHasOccurred);
  }

  private int[] findLbUbPosForMax() {
    int lb = IntDomain.MIN_INT;
    int ub = IntDomain.MIN_INT;
    int pos = -1;
    for (ValueEnumeration e = extremeIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int cp = e.nextElement();
      int i = cp - 1 - indexOffset;
      int vDomMin = list[i].min();
      if (lb < vDomMin) {
        lb = vDomMin;
        pos = i;
      }
      int vDomMax = list[i].max();
      if (ub < vDomMax) {
        ub = vDomMax;
      }
    }
    return new int[] {lb, ub, pos};
  }

  private IntervalDomain buildIdxDomainForMax(int lb) {
    IntervalDomain idxDomain = new IntervalDomain();
    for (ValueEnumeration e = extremeIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int cp = e.nextElement();
      int i = cp - 1 - indexOffset;
      if (list[i].max() >= lb) {
        if (idxDomain.getSize() == 0) {
          idxDomain.unionAdapt(cp, cp);
        } else {
          idxDomain.addLastElement(cp);
        }
      }
    }
    return idxDomain;
  }

  private int[] findUbPosForMax() {
    int ub = IntDomain.MIN_INT;
    int pos = -1;
    for (ValueEnumeration e = extremeIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int i = e.nextElement() - 1 - indexOffset;
      int vDomMax = list[i].max();
      if (ub < vDomMax) {
        ub = vDomMax;
        pos = i;
      }
    }
    return new int[] {ub, pos};
  }

  private void pruneWhenExtremeIndexSingletonMax(Store store) {
    int idx = extremeIndex.value() - 1 - indexOffset;
    IntVar y = list[idx];
    for (int i = 0; i < list.length; i++) {
      IntVar x = list[i];
      if (i < idx) {
        x.domain.inMax(store.level, x, y.max() - 1);
        y.domain.inMin(store.level, y, x.min() + 1);
      } else {
        x.domain.inMax(store.level, x, y.max());
        y.domain.inMin(store.level, y, x.min());
      }
    }
  }

  private void pruneWhenExtremeIndexNotSingletonMax(Store store, int ub) {
    int im = extremeIndex.min();
    for (int i = 0; i < list.length; i++) {
      int cp = i + 1 + indexOffset;
      IntVar v = list[i];
      if (cp < im) {
        v.domain.inMax(store.level, v, ub - 1);
      } else {
        v.domain.inMax(store.level, v, ub);
      }
    }
  }

  @Override
  public boolean satisfied() {

    boolean sat = extremeIndex.singleton();

    int maxVal = list[extremeIndex.value() - 1 - indexOffset].value();
    int i = 0;
    int eq = 0;
    while (sat && i < list.length) {
      if (list[i].singleton() && list[i].value() <= maxVal) {
        eq++;
      }
      sat = list[i].max() <= maxVal;
      i++;
    }

    return sat && eq == list.length;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : ArgMax(  [ ");
    appendArrayToString(result, list);

    result.append("], ").append(this.extremeIndex);
    result.append(", ").append(indexOffset).append(")");

    return result.toString();
  }
}
