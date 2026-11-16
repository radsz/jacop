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
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * ArgMin constraint provides the index of the minimum variable from all variables on the list.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ArgMin extends AbstractArgMinMax implements Copyable<ArgMin> {

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

    if (init.begin(store)) {
      extremeIndex.domain.in(store.level, extremeIndex, 1 + indexOffset, list.length + indexOffset);
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

    pruneIndexToFirstExtremum(store, false);

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

  /*
   * Every position after the first one of the index is at least lb, the smallest minimum over the
   * positions left in the index. A position k that is not in the index cannot be the first
   * minimum, so some position j of the index is at most x[k] before k, or below it after k: x[k]
   * is at least the smallest minimum of the index positions before k, or one more than the
   * smallest after k.
   */
  private void pruneWhenExtremeIndexNotSingletonMin(Store store, int lb) {
    int n = list.length;
    int im = extremeIndex.min();
    long[] after = new long[n + 1];
    after[n] = Long.MAX_VALUE;
    for (int j = n - 1; j >= 0; j--) {
      after[j] = after[j + 1];
      if (extremeIndex.domain.contains(j + 1 + indexOffset)) {
        after[j] = Math.min(after[j], list[j].min());
      }
    }
    long before = Long.MAX_VALUE;
    for (int i = 0; i < n; i++) {
      IntVar v = list[i];
      int cp = i + 1 + indexOffset;
      if (extremeIndex.domain.contains(cp)) {
        if (cp > im) {
          v.domain.inMin(store.level, v, lb);
        }
        before = Math.min(before, v.min());
      } else {
        long bound =
            Math.min(before, after[i + 1] == Long.MAX_VALUE ? Long.MAX_VALUE : after[i + 1] + 1);
        if (bound > v.max()) {
          throw Store.failException;
        }
        v.domain.inMin(store.level, v, (int) Math.max(bound, cp < im ? lb + 1L : lb));
      }
    }
  }

  @Override
  public boolean satisfied() {
    return firstExtremumEntailed(false);
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

  @Override
  public ArgMin copy(VarMap map) {
    return new ArgMin(map.get(list), map.get(extremeIndex), indexOffset);
  }
}
