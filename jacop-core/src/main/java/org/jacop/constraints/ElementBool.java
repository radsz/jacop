/*
 * ElementBool.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.*;

/**
 * ElementBool constraint defines a relation list[index - indexOffset] = value.
 *
 * <p>The first element of the list corresponds to index - indexOffset = 1. By default indexOffset
 * is equal 0 so first value within a list corresponds to index equal 1.
 *
 * <p>If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to make
 * addressing of list array starting from 1.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.10
 */
public class ElementBool extends Constraint implements UsesQueueVariable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  boolean firstConsistencyCheck = true;
  int firstConsistencyLevel;

  /** It specifies variable index within an element constraint list[index-indexOffset] = value. */
  public final IntVar index;

  /** It specifies variable value within an element constraint list[index-indexOffset] = value. */
  public final IntVar value;

  /** It specifies indexOffset within an element constraint list[index-indexOffset] = value. */
  public final int indexOffset;

  /**
   * It specifies list of variables within an element constraint list[index-indexOffset] = value.
   * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0.
   */
  public final int[] list;

  boolean indexHasChanged = true;
  boolean valueHasChanged = true;

  final IntDomain indexAtZero = new IntervalDomain(5);
  final IntDomain indexAtOne = new IntervalDomain(5);

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of integers from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementBool(IntVar index, int[] list, IntVar value, int indexOffset) {

    checkInputForNullness(new String[] {"index", "value"}, new Object[] {index, value});
    checkInputForNullness("list", list);

    this.indexOffset = indexOffset;
    this.numberId = idNumber.incrementAndGet();
    this.index = index;
    this.value = value;
    this.list = Arrays.copyOf(list, list.length);
    this.queueIndex = 1;

    setScope(index, value);

    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int idx = e.nextElement();
      int i = idx - 1 - indexOffset;
      if (i >= 0 && i < list.length) {
        int valueOfElement = list[i];

        if (valueOfElement == 0) {
          indexAtZero.unionAdapt(idx);
        } else if (valueOfElement == 1) {
          indexAtOne.unionAdapt(idx);
        }
      }
    }
  }

  /**
   * It constructs an element constraint with default indexOffset equal 0.
   *
   * @param index index variable.
   * @param list list containing variables which one pointed out by index variable is made equal to
   *     value variable.
   * @param value a value variable equal to the specified element from the list.
   */
  public ElementBool(IntVar index, List<Integer> list, IntVar value) {
    this(index, list, value, 0);
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of integers from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementBool(IntVar index, List<Integer> list, IntVar value, int indexOffset) {
    this(index, list.stream().mapToInt(i -> i).toArray(), value, indexOffset);
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of integers from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   * @param checkDuplicates informs whether to create duplicates list for values from list (default
   *     = true).
   */
  public ElementBool(
      IntVar index, List<Integer> list, IntVar value, int indexOffset, boolean checkDuplicates) {
    this(index, list.stream().mapToInt(i -> i).toArray(), value, indexOffset);
  }

  /**
   * It constructs an element constraint with indexOffset by default set to 0.
   *
   * @param index variable index
   * @param list list of integers from which an index-th element is taken
   * @param value a value of the index-th element from list
   */
  ElementBool(IntVar index, int[] list, IntVar value) {
    this(index, list, value, 0);
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {

      index.domain.in(store.level, index, 1 + indexOffset, list.length + indexOffset);
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
    }

    if (valueHasChanged) {
      if (value.max() == 0) {
        index.domain.in(store.level, index, indexAtZero);
        removeConstraint();
        return;
      } else if (value.min() == 1) {
        index.domain.in(store.level, index, indexAtOne);
        removeConstraint();
        return;
      }
    }

    if (indexHasChanged) {

      boolean zeros = false;
      boolean ones = false;
      ValueEnumeration e = index.domain.valueEnumeration();
      do {
        int idx = e.nextElement();
        int i = idx - 1 - indexOffset;
        int valueOfElement = list[i];

        if (valueOfElement == 0) {
          zeros = true;
        } else if (valueOfElement == 1) {
          ones = true;
        }
      } while (!(zeros && ones) && e.hasMoreElements());

      if (zeros && !ones) {
        value.domain.inValue(store.level, value, 0);
        removeConstraint();
      } else if (!zeros && ones) {
        value.domain.inValue(store.level, value, 1);
        removeConstraint();
      }

      indexHasChanged = false;
      valueHasChanged = false;
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void queueVariable(int level, Var var) {
    if (var == index) {
      indexHasChanged = true;
    } else {
      valueHasChanged = true;
    }
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : elementBool").append("( ").append(index).append(", [");

    for (int i = 0; i < list.length; i++) {
      result.append(list[i]);

      if (i < list.length - 1) {
        result.append(", ");
      }
    }

    result.append("], ").append(value).append(", ").append(indexOffset).append(" )");

    return result.toString();
  }
}
