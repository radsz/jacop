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
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

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
        Explainable,
        PbEncodable {

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
  final IntVar value;

  /**
   * It specifies list of variables within an element constraint list[index-indexOffset] = value.
   * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0.
   */
  final int[] list;

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

  /**
   * The list and what impose derives from it alone, shared with the elements made by {@link
   * #ElementInteger(IntVar, IntVar, ElementInteger)} and by {@link #copy(VarMap)}: each element
   * over one long list of 20,000 values held its own copy of the list, of the ranks of its values
   * and of the groups of duplicates, 350 KB an element.
   */
  private final Shared shared;

  // the buffers of supportedValuesByRank, one per thread instead of one per constraint
  private static final ThreadLocal<Buffers> BUFFERS = ThreadLocal.withInitial(Buffers::new);

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
    this.shared = new Shared();

    setScope(index, value);
  }

  /**
   * It constructs an element constraint over the list of another one, with its index offset and
   * treatment of duplicates. The two share the list and what is derived from it, so many elements
   * over one long list keep it once.
   *
   * @param index variable index
   * @param value a value of the index-th element from the list of same
   * @param same the element whose list, index offset and treatment of duplicates are used
   */
  public ElementInteger(IntVar index, IntVar value, ElementInteger same) {
    super(index, same.indexOffset);
    checkInputForNullness(
        new String[] {"index", "value", "same"}, new Object[] {index, value, same});
    this.checkDuplicates = same.checkDuplicates;
    this.numberId = idNumber.incrementAndGet();
    this.value = value;
    this.list = same.list;
    this.queueIndex = 1;
    this.shared = same.shared;

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

    // a small index reads its values directly: testing every group of duplicate positions against
    // it costs more than the values it holds; a large one skips the groups it covers
    boolean small = index.getSize() < limitForDomainPruning;
    IntervalDomain domValue;
    if (sortedValues == null) {
      domValue = new IntervalDomain(5);
      for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
        domValue.unionAdapt(list[e.nextElement() - 1 - indexOffset]);
      }
    } else {
      domValue = supportedValuesByRank(!small);
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
   * @param useDuplicates whether groups of positions holding one value are tested as a whole.
   * @return the domain of values supported by the index.
   */
  private IntervalDomain supportedValuesByRank(boolean useDuplicates) {

    Buffers buffers = BUFFERS.get();
    int[] supportedRanks = buffers.ranks(list.length);
    int count = 0;
    IntDomain indexDom = index.dom();
    if (useDuplicates && !duplicates.isEmpty()) {
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
      int[] rankStamp = buffers.stamps(sortedValues.length);
      int stamp = buffers.nextStamp();
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

    shared.derive(this);
    duplicates = shared.duplicates;
    duplicatesIndexes = shared.duplicatesIndexes;
    sortedValues = shared.sortedValues;
    valueRank = shared.valueRank;

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
    return new ElementInteger(map.get(index), map.get(value), this);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == ElementInteger.class
        && index != value
        && ElementExplanation.explain(trail, entry, index, list, value, indexOffset, out);
  }

  @Override
  public boolean encode(PbModel model) {
    if (getClass() != ElementInteger.class || index == value) {
      return false;
    }
    ElementExplanation.encode(model, index, list, value, indexOffset);
    return true;
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

  /**
   * Returns the values of the list.
   *
   * @return a copy of the list, read at index - indexOffset from 1.
   */
  public int[] values() {
    return list.clone();
  }

  /**
   * Returns the variable equal to the selected value.
   *
   * @return the value variable.
   */
  public IntVar value() {
    return value;
  }

  /**
   * The groups of duplicate positions and the ranks of the values of a list, computed by the first
   * impose of the elements sharing the list.
   */
  private static final class Shared {

    private boolean derived;

    private List<IntDomain> duplicates;

    private IntDomain duplicatesIndexes;

    private int[] sortedValues;

    private int[] valueRank;

    synchronized void derive(ElementInteger c) {
      if (derived) {
        return;
      }
      int[] list = c.list;
      int n = list.length;
      // the positions sorted by value, then by position
      long[] byValue = new long[n];
      for (int pos = 0; pos < n; pos++) {
        byValue[pos] = ((long) list[pos] << 32) | pos;
      }
      Arrays.sort(byValue);
      duplicates = new ArrayList<>();
      duplicatesIndexes = new IntervalDomain();
      if (c.checkDuplicates) {
        deriveDuplicates(byValue, c.indexOffset);
      }
      if (n >= limitForDomainPruning) {
        deriveRanks(byValue);
      }
      derived = true;
    }

    // the groups of more than minDuplicatesSize positions with one value, in increasing value
    private void deriveDuplicates(long[] byValue, int indexOffset) {
      int n = byValue.length;
      int start = 0;
      while (start < n) {
        int end = start + 1;
        while (end < n && byValue[end] >> 32 == byValue[start] >> 32) {
          end++;
        }
        if (end - start > minDuplicatesSize) {
          IntervalDomain indexes = new IntervalDomain();
          for (int k = start; k < end; k++) {
            int elementIndex = (int) byValue[k] + 1 + indexOffset;
            if (indexes.isEmpty()) {
              indexes.unionAdapt(elementIndex, elementIndex);
            } else {
              indexes.addLastElement(elementIndex);
            }
          }
          duplicates.add(indexes);
          duplicatesIndexes.unionAdapt(indexes);
        }
        start = end;
      }
    }

    // the distinct values in increasing order and the rank of the value of each position
    private void deriveRanks(long[] byValue) {
      int n = byValue.length;
      int distinct = 0;
      int[] values = new int[n];
      valueRank = new int[n];
      for (int k = 0; k < n; k++) {
        int v = (int) (byValue[k] >> 32);
        if (distinct == 0 || values[distinct - 1] != v) {
          values[distinct++] = v;
        }
        valueRank[(int) byValue[k]] = distinct - 1;
      }
      sortedValues = Arrays.copyOf(values, distinct);
    }
  }

  /** The buffers of {@link #supportedValuesByRank(boolean)} of one thread. */
  private static final class Buffers {

    private int[] ranks = new int[0];

    // for each rank, the stamp of the last call that found the value supported
    private int[] stamps = new int[0];

    private int stamp;

    int[] ranks(int n) {
      if (ranks.length < n) {
        ranks = new int[n];
      }
      return ranks;
    }

    int[] stamps(int n) {
      if (stamps.length < n) {
        stamps = new int[n];
        stamp = 0;
      }
      return stamps;
    }

    int nextStamp() {
      if (stamp == Integer.MAX_VALUE) {
        Arrays.fill(stamps, 0);
        stamp = 0;
      }
      return ++stamp;
    }
  }
}
