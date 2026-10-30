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
import java.util.Optional;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import org.jacop.api.Copyable;
import org.jacop.api.Functional;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Simplifiable;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.ElementExplanation;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

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
public class ElementInteger extends AbstractElement
    implements Functional,
        Violation,
        Simplifiable,
        UsesQueueVariable,
        SatisfiedPresent,
        Copyable<ElementInteger>,
        Explainable {

  /**
   * It specifies the size of index domain from which the values supported by the index are
   * collected through the value ranks of the list (sorted or marked) instead of being added one by
   * one to the value domain. Both ways give domain consistency for value.
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
   * The distinct values of the list in increasing order. It is only computed when the list has at
   * least limitForDomainPruning elements.
   */
  private int[] sortedValues;

  /** For each position of the list, the rank of its value in sortedValues. */
  private int[] valueRank;

  /** A buffer for the ranks of the values supported by the current index domain. */
  private int[] supportedRanks;

  /** For each rank, the stamp of the last call that found the value supported. */
  private int[] rankStamp;

  private int stamp;

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

    if (init.begin(store)) {
      initFirstConsistencyCheck(store);
    }

    if (index == value) {
      propagateSameVariable(store);
      return;
    }

    boolean copyOfValueHasChanged = valueHasChanged;

    if (indexHasChanged) {
      propagateIndexChanged(store);
    }

    if (copyOfValueHasChanged) {
      propagateValueChanged(store);
    }

    if (value.singleton() && !index.singleton()) {
      removeConstraint();
    }
  }

  /**
   * With the same variable as index and value, a pruning of one side changes the other, which the
   * store does not report back to this constraint, so the two-sided propagation stopped before its
   * fixpoint. The variable can take exactly the positions that hold their own index.
   */
  private void propagateSameVariable(Store store) {
    IntervalDomain positions = new IntervalDomain();
    for (int pos = 0; pos < list.length; pos++) {
      int position = pos + 1 + indexOffset;
      if (list[pos] == position) {
        positions.unionAdapt(position, position);
      }
    }
    index.domain.in(store.level, index, positions);
    removeConstraint();
  }

  private void propagateIndexChanged(Store store) {
    indexHasChanged = false;

    IntervalDomain domValue;
    if (index.getSize() < limitForDomainPruning || sortedValues == null) {
      IntDomain indexDom = index.dom().cloneLight();
      domValue = addDuplicatesToDomValue(indexDom);
      if (!duplicates.isEmpty()) {
        indexDom = indexDom.subtract(duplicatesIndexes);
      }
      addIndexDomValuesToDomValue(indexDom, domValue);
    } else {
      domValue = supportedValuesByRank();
    }

    value.domain.in(store.level, value, domValue);
    valueHasChanged = false;
  }

  /**
   * It computes the values of the list at the positions of the index domain. The ranks of these
   * values are collected and then turned into a domain in increasing order, either by sorting the
   * ranks or by a sweep over all ranks, whichever is cheaper. It takes O(|D(index)| log |D(index)|)
   * or O(|D(index)| + number of distinct values) instead of the quadratic worst case of adding
   * values out of order to an interval domain.
   *
   * @return the domain of values supported by the index.
   */
  private IntervalDomain supportedValuesByRank() {

    int count = 0;
    IntDomain indexDom = index.dom();
    if (!duplicates.isEmpty()) {
      for (IntDomain duplicate : duplicates) {
        if (indexDom.isIntersecting(duplicate)) {
          supportedRanks[count++] = valueRank[duplicate.min() - 1 - indexOffset];
        }
      }
      indexDom = indexDom.subtract(duplicatesIndexes);
    }
    for (ValueEnumeration e = indexDom.valueEnumeration(); e.hasMoreElements(); ) {
      supportedRanks[count++] = valueRank[e.nextElement() - 1 - indexOffset];
    }

    IntervalDomain domValue = new IntervalDomain(5);
    if (count == 0) {
      return domValue;
    }

    if ((long) count * (32 - Integer.numberOfLeadingZeros(count)) < sortedValues.length) {
      Arrays.sort(supportedRanks, 0, count);
      int previous = supportedRanks[0];
      domValue.unionAdapt(sortedValues[previous]);
      for (int i = 1; i < count; i++) {
        int rank = supportedRanks[i];
        if (rank != previous) {
          domValue.addLastElement(sortedValues[rank]);
          previous = rank;
        }
      }
    } else {
      if (stamp == Integer.MAX_VALUE) {
        Arrays.fill(rankStamp, 0);
        stamp = 0;
      }
      stamp++;
      for (int i = 0; i < count; i++) {
        rankStamp[supportedRanks[i]] = stamp;
      }
      for (int rank = 0; rank < sortedValues.length; rank++) {
        if (rankStamp[rank] == stamp) {
          if (domValue.isEmpty()) {
            domValue.unionAdapt(sortedValues[rank]);
          } else {
            domValue.addLastElement(sortedValues[rank]);
          }
        }
      }
    }
    return domValue;
  }

  private IntervalDomain addDuplicatesToDomValue(IntDomain indexDom) {
    IntervalDomain domValue = new IntervalDomain(5);
    if (!checkDuplicates) {
      return domValue;
    }
    for (IntDomain duplicate : duplicates) {
      if (indexDom.isIntersecting(duplicate)) {
        if (domValue.isEmpty()) {
          domValue.unionAdapt(list[duplicate.min() - 1 - indexOffset]);
        } else {
          domValue.addLastElement(list[duplicate.min() - 1 - indexOffset]);
        }
      }
    }
    return domValue;
  }

  private void addIndexDomValuesToDomValue(IntDomain indexDom, IntervalDomain domValue) {
    for (ValueEnumeration e = indexDom.valueEnumeration(); e.hasMoreElements(); ) {
      int valueOfElement = list[e.nextElement() - 1 - indexOffset];
      domValue.unionAdapt(valueOfElement);
    }
  }

  private void propagateValueChanged(Store store) {
    valueHasChanged = false;
    IntervalDomain indexDom = new IntervalDomain(5);
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int position = e.nextElement() - 1 - indexOffset;
      int val = list[position];
      if (disjoint(value.domain, val)) {
        if (indexDom.size == 0) {
          indexDom.unionAdapt(position + 1 + indexOffset);
        } else {
          indexDom.addLastElement(position + 1 + indexOffset);
        }
      }
    }
    index.domain.in(store.level, index, indexDom.complement());
    indexHasChanged = false;
  }

  @Override
  public void impose(Store store) {

    imposeInit(store);

    duplicates = new ArrayList<>();
    duplicatesIndexes = new IntervalDomain();

    if (checkDuplicates) {

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

      for (IntDomain duplicate : map.values()) {
        if (duplicate.getSize() > minDuplicatesSize) {
          duplicates.add(duplicate);

          duplicatesIndexes.unionAdapt(duplicate);
        }
      }
    }

    if (list.length >= limitForDomainPruning) {
      computeValueRanks();
    }

    valueHasChanged = true;
    indexHasChanged = true;
  }

  private void computeValueRanks() {
    int[] values = Arrays.copyOf(list, list.length);
    Arrays.sort(values);
    int distinct = 0;
    for (int i = 0; i < values.length; i++) {
      if (i == 0 || values[i] != values[i - 1]) {
        values[distinct++] = values[i];
      }
    }
    sortedValues = Arrays.copyOf(values, distinct);
    valueRank = new int[list.length];
    for (int pos = 0; pos < list.length; pos++) {
      valueRank[pos] = Arrays.binarySearch(sortedValues, list[pos]);
    }
    supportedRanks = new int[list.length];
    rankStamp = new int[distinct];
    stamp = 0;
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

  @Override
  public Optional<List<Constraint>> simplify() {
    if (getClass() != ElementInteger.class) {
      return Optional.empty();
    }
    return ElementSimplification.integers(
        index,
        list,
        value,
        indexOffset,
        (i, l, offset) -> new ElementInteger(i, l, value, offset, checkDuplicates));
  }

  @Override
  public ElementInteger copy(VarMap map) {
    return new ElementInteger(map.get(index), list, map.get(value), indexOffset, checkDuplicates);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == ElementInteger.class
        && index != value
        && ElementExplanation.explain(trail, entry, index, list, value, indexOffset, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == ElementInteger.class
        && index != value
        && ElementExplanation.explainFailure(trail, index, list, value, indexOffset, out);
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    int i = value.applyAsInt(index) - indexOffset - 1;
    if (i < 0 || i >= list.length) {
      return 1;
    }
    return list[i] == value.applyAsInt(this.value) ? 0 : 1;
  }

  @Override
  public IntVar functionalResult() {
    return value;
  }

  @Override
  public int functionalValue(ToIntFunction<IntVar> value) {
    int i = value.applyAsInt(index) - indexOffset - 1;
    if (i < 0 || i >= list.length) {
      // The constraint is violated whatever the result, so the result keeps its value.
      return value.applyAsInt(this.value);
    }
    return list[i];
  }
}
