/*
 * ArgMin.java
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
 * ArgMin constraint provides the index of the minimum variable from all variables on the list.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ArgMin extends AbstractArgMinMax {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs min constraint.
   *
   * @param minIndex variable denoting the index of the minimum value
   * @param list the array of variables for which the index of the minimum value is imposed.
   * @param indexOffset the offset for the index that is computed from 1 by default (if needed from
   *     0, use -1 for this parameter)
   */
  public ArgMin(IntVar[] list, IntVar minIndex, int indexOffset) {
    this(list, minIndex);
    this.indexOffset = indexOffset;
  }

  /**
   * It constructs min constraint with default index offset of 0.
   *
   * @param list the array of variables for which the index of the minimum value is imposed.
   * @param minIndex variable denoting the index of the minimum value
   */
  public ArgMin(IntVar[] list, IntVar minIndex) {
    super(idNumber, list, minIndex);
  }

  /**
   * It constructs min constraint.
   *
   * @param minIndex variable denoting the index of minimum value
   * @param variables the array of variables for which the minimum value is imposed.
   * @param indexOffset the offset for the index that is computed from 1 by default (if needed from
   *     0, use -1 for this parameter)
   */
  public ArgMin(List<? extends IntVar> variables, IntVar minIndex, int indexOffset) {
    this(variables, minIndex);
    this.indexOffset = indexOffset;
  }

  /**
   * It constructs min constraint with default index offset of 0.
   *
   * @param variables the list of variables for which the index of the minimum value is imposed.
   * @param minIndex variable denoting the index of the minimum value
   */
  public ArgMin(List<? extends IntVar> variables, IntVar minIndex) {
    this(variables.toArray(new IntVar[0]), minIndex);
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      extremeIndex.domain.in(store.level, extremeIndex, 1 + indexOffset, list.length + indexOffset);
      firstConsistencyCheck = false;
    }

    do {
      store.propagationHasOccurred = false;
      propagateMin(store);
    } while (store.propagationHasOccurred);
  }

  private void propagateMin(Store store) {
    int[] lbUbPos = findLbUbPosForMin();
    int lb = lbUbPos[0];
    int ub = lbUbPos[1];
    int pos = lbUbPos[2];

    if (lb == ub) {
      extremeIndex.domain.inMax(store.level, extremeIndex, pos + 1 + indexOffset);
    }

    IntervalDomain idxDomain = buildIdxDomainForMin(ub);
    if (idxDomain.isEmpty()) {
      throw Store.failException;
    }
    extremeIndex.domain.in(store.level, extremeIndex, idxDomain);

    int[] lbPos = findLbPosForMin();
    int lb2 = lbPos[0];
    int pos2 = lbPos[1];
    if (list[pos2].singleton()) {
      extremeIndex.domain.in(
          store.level, extremeIndex, pos2 + 1 + indexOffset, pos2 + 1 + indexOffset);
    }

    if (extremeIndex.singleton()) {
      pruneWhenExtremeIndexSingletonMin(store);
    } else {
      pruneWhenExtremeIndexNotSingletonMin(store, lb2);
    }
  }

  private int[] findLbUbPosForMin() {
    int lb = IntDomain.MAX_INT;
    int ub = IntDomain.MAX_INT;
    int pos = -1;
    for (int i = 0; i < list.length; i++) {
      int vDomMin = list[i].dom().min();
      if (lb > vDomMin) {
        lb = vDomMin;
      }
      int vDomMax = list[i].dom().max();
      if (ub > vDomMax) {
        ub = vDomMax;
        pos = i;
      }
    }
    return new int[] {lb, ub, pos};
  }

  private IntervalDomain buildIdxDomainForMin(int ub) {
    IntervalDomain idxDomain = new IntervalDomain();
    for (int i = 0; i < list.length; i++) {
      int cp = i + 1 + indexOffset;
      if (list[i].min() <= ub) {
        if (idxDomain.getSize() == 0) {
          idxDomain.unionAdapt(cp, cp);
        } else {
          idxDomain.addLastElement(cp);
        }
      }
    }
    return idxDomain;
  }

  private int[] findLbPosForMin() {
    int lb = IntDomain.MAX_INT;
    int pos = -1;
    for (ValueEnumeration e = extremeIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int i = e.nextElement() - 1 - indexOffset;
      int vDomMin = list[i].dom().min();
      if (lb > vDomMin) {
        lb = vDomMin;
        pos = i;
      }
    }
    return new int[] {lb, pos};
  }

  private void pruneWhenExtremeIndexSingletonMin(Store store) {
    int idx = extremeIndex.value() - 1 - indexOffset;
    IntVar y = list[idx];
    for (int i = 0; i < list.length; i++) {
      IntVar x = list[i];
      if (i < idx) {
        x.domain.inMin(store.level, x, y.min() + 1);
        y.domain.inMax(store.level, y, x.max() - 1);
      } else {
        x.domain.inMin(store.level, x, y.min());
        y.domain.inMax(store.level, y, x.max());
      }
    }
  }

  private void pruneWhenExtremeIndexNotSingletonMin(Store store, int lb) {
    int im = extremeIndex.min();
    for (int i = 0; i < list.length; i++) {
      int cp = i + 1 + indexOffset;
      if (cp < im) {
        list[i].domain.inMin(store.level, list[i], lb + 1);
      } else if (cp > im) {
        list[i].domain.inMin(store.level, list[i], lb);
      }
    }
  }

  @Override
  public boolean satisfied() {

    boolean sat = extremeIndex.singleton();

    if (!sat) {
      return false;
    }

    int minVal = list[extremeIndex.value() - 1 - indexOffset].value();
    int i = 0;
    int eq = 0;
    while (sat && i < list.length) {
      if (list[i].singleton() && list[i].value() >= minVal) {
        eq++;
      }
      sat = list[i].min() >= minVal;
      i++;
    }

    return sat && eq == list.length;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : ArgMin(  [ ");
    appendArrayToString(result, list);

    result.append("], ").append(this.extremeIndex);
    result.append(", ").append(indexOffset).append(")");

    return result.toString();
  }
}
