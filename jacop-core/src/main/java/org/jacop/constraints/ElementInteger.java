/*
 * ElementInteger.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * ElementInteger constraint defines a relation list[index - indexOffset] = value.
 *
 * <p>The first element of the list corresponds to index - indexOffset = 1. By default indexOffset
 * is equal 0 so first value within a list corresponds to index equal 1.
 *
 * <p>If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to make
 * addressing of list array starting from 1.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class ElementInteger extends AbstractElement implements UsesQueueVariable, SatisfiedPresent {

  /**
   * It specifies the maximal size of index domain when the constraint will apply domain consistency
   * for value. Otherwise bound consistency is applied. This limit applies to both duplicates and
   * index.
   */
  static final int LIMIT_FOR_DOMAIN_PRUNING = 100;

  static int limitForDomainPruning = LIMIT_FOR_DOMAIN_PRUNING;

  /**
   * It specifies the minimal size of number of duplicated values on the list that are consodered
   * together.. Otherwise they are processed one by one.
   */
  static final int MIN_DUPLICATES_SIZE = 10;

  static int minDuplicatesSize = MIN_DUPLICATES_SIZE;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It specifies whether duplicate values should be treated specially (combined to a single check).
   * In general a good idea but when lists are long it makes the process slower instead of faster.
   */
  private final boolean checkDuplicates;

  /** It specifies variable value within an element constraint list[index-indexOffset] = value. */
  private final IntVar value;

  /**
   * It specifies list of variables within an element constraint list[index-indexOffset] = value.
   * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0.
   */
  private final int[] list;

  /**
   * It specifies for each value what are the possible values of the index variable (it takes into
   * account indexOffset.
   */
  // Hashtable<Integer, IntDomain> mappingValuesToIndex = new Hashtable<Integer, IntDomain>();

  boolean indexHasChanged = true;

  boolean valueHasChanged = true;

  /**
   * It holds information about the positions within list array that are equal. It allows to safely
   * skip duplicates when enumerating index domain. duplicatesIndexes is a domain having indexes of
   * all indexes for duplicates.
   */
  List<IntDomain> duplicates;

  IntDomain duplicatesIndexes;

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of integers from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementInteger(IntVar index, int[] list, IntVar value, int indexOffset) {
    this(index, list, value, indexOffset, true);
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
  public ElementInteger(
      IntVar index, int[] list, IntVar value, int indexOffset, boolean checkDuplicates) {

    super(index, indexOffset);
    checkInputForNullness(new String[] {"index", "value"}, new Object[] {index, value});
    checkInputForNullness("list", list);

    this.checkDuplicates = checkDuplicates;
    this.numberId = idNumber.incrementAndGet();
    this.value = value;
    this.list = Arrays.copyOf(list, list.length);
    this.queueIndex = 1;

    setScope(index, value);
  }

  /**
   * It constructs an element constraint with default indexOffset equal 0.
   *
   * @param index index variable.
   * @param list list containing variables which one pointed out by index variable is made equal to
   *     value variable.
   * @param value a value variable equal to the specified element from the list.
   */
  public ElementInteger(IntVar index, List<Integer> list, IntVar value) {
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
  public ElementInteger(IntVar index, List<Integer> list, IntVar value, int indexOffset) {
    this(index, list.stream().mapToInt(i -> i).toArray(), value, indexOffset, true);
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
  public ElementInteger(
      IntVar index, List<Integer> list, IntVar value, int indexOffset, boolean checkDuplicates) {
    this(index, list.stream().mapToInt(i -> i).toArray(), value, indexOffset, checkDuplicates);
  }

  /**
   * It constructs an element constraint with indexOffset by default set to 0.
   *
   * @param index variable index
   * @param list list of integers from which an index-th element is taken
   * @param value a value of the index-th element from list
   */
  ElementInteger(IntVar index, int[] list, IntVar value) {
    this(index, list, value, 0);
  }

  @Override
  protected int listLength() {
    return list.length;
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      initFirstConsistencyCheck(store);
    }

    // ====== Very simple implementation =========

    // ==============================================

    boolean copyOfValueHasChanged = valueHasChanged;

    if (indexHasChanged) {

      indexHasChanged = false;
      IntDomain indexDom = index.dom().cloneLight();
      IntervalDomain domValue = new IntervalDomain(5);

      if (checkDuplicates) {
        for (IntDomain duplicate : duplicates) {
          if (indexDom.isIntersecting(duplicate)) {
            if (domValue.isEmpty()) {
              domValue.unionAdapt(list[duplicate.min() - 1 - indexOffset]);
            } else {
              domValue.addLastElement(list[duplicate.min() - 1 - indexOffset]);
            }
          }
        }
      }

      indexDom = indexDom.subtract(duplicatesIndexes);

      if (indexDom.getSize()
          < limitForDomainPruning) { // domain consistency for small index domains
        // values of index for duplicated values within list are already taken care of above.
        for (ValueEnumeration e = indexDom.valueEnumeration(); e.hasMoreElements(); ) {
          int valueOfElement = list[e.nextElement() - 1 - indexOffset];
          domValue.unionAdapt(valueOfElement);
        }

        value.domain.in(store.level, value, domValue);
        valueHasChanged = false;
      } else { // bound consistency for large index domains
        // values of index for duplicated values within list are already taken care of above.
        int min = IntDomain.MAX_INT;
        int max = IntDomain.MIN_INT;
        for (ValueEnumeration e = indexDom.valueEnumeration(); e.hasMoreElements(); ) {
          int valueOfElement = list[e.nextElement() - 1 - indexOffset];

          min = Math.min(min, valueOfElement);
          max = Math.max(max, valueOfElement);
        }
        domValue.unionAdapt(min, max);

        value.domain.in(store.level, value, domValue);
        valueHasChanged = false;
      }
    }

    // the if statement above can change value variable but those changes can be ignored.
    if (copyOfValueHasChanged) {

      valueHasChanged = false;

      IntervalDomain indexDom = new IntervalDomain(5);
      for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
        int position = e.nextElement() - 1 - indexOffset;
        int val = list[position];

        if (disjoint(value.domain, val)) {
          if (indexDom.size == 0) {
            indexDom.unionAdapt(position + 1 + indexOffset);
          } else {
            // indexes are in ascending order and can be added at the end if the last element
            // plus 1 is not equal a new value. In such case the max must be changed.
            indexDom.addLastElement(position + 1 + indexOffset);
          }
        }
      }

      index.domain.in(store.level, index, indexDom.complement());
      indexHasChanged = false;
    }

    if (value.singleton() && !index.singleton()) {
      removeConstraint();
    }
  }

  boolean disjoint(IntDomain v1, int v2) {
    if (v1.min() > v2 || v2 > v1.max()) {
      return true;
    } else {
      return !v1.contains(v2);
    }
  }

  @Override
  public void impose(Store store) {

    imposeInit(store);

    if (checkDuplicates) {
      duplicates = new ArrayList<>();

      TreeMap<Integer, IntervalDomain> map = new TreeMap<>();

      for (int pos = 0; pos < list.length; pos++) {

        int el = list[pos];
        IntervalDomain indexes = map.get(el);
        int elementIndex = pos + 1 + indexOffset;
        if (indexes == null) {
          indexes = new IntervalDomain(elementIndex, elementIndex);
          map.put(el, indexes);
        } else {
          indexes.addLastElement(elementIndex);
        }
      }

      duplicatesIndexes = new IntervalDomain();
      for (IntDomain duplicate : map.values()) {
        if (duplicate.getSize() > minDuplicatesSize) {
          duplicates.add(duplicate);

          duplicatesIndexes.unionAdapt(duplicate);
        }
      }
    }

    valueHasChanged = true;
    indexHasChanged = true;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (v == index) {
      indexHasChanged = true;
    } else {
      valueHasChanged = true;
    }
  }

  @Override
  public boolean satisfied() {

    if (value.singleton()) {

      int v = value.min();

      IntDomain duplicate = null;

      for (IntDomain d : duplicates) {
        if (index.domain.isIntersecting(d)) {
          duplicate = d;
          break;
        }
      }

      if (duplicate == null) {

        if (!index.singleton()) {
          return false;
        } else {
          return list[index.value() - 1 - indexOffset] == v;
        }

      } else {

        return duplicate.contains(index.domain) && list[index.min() - 1 - indexOffset] == v;
      }

    } else {
      return false;
    }
  }

  @Override
  public String toString() {
    return buildToString("elementInteger", list, value, true);
  }
}
