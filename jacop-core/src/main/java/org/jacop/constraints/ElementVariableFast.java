/*
 * ElementVariableFast.java
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

import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.Functional;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Simplifiable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.ElementVariableExplanation;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * ElementVariableFast constraint defines a relation list[index - indexOffset] = value. This version
 * uses bounds consistency.
 *
 * <p>The first element of the list corresponds to index - indexOffset = 1. By default indexOffset
 * is equal 0 so first value within a list corresponds to index equal 1.
 *
 * <p>If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to make
 * addressing of list array starting from 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ElementVariableFast extends AbstractElement
    implements Functional,
        Violation,
        Simplifiable,
        SatisfiedPresent,
        Copyable<ElementVariableFast>,
        Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable value within an element constraint list[index - indexOffset] = value. */
  private final IntVar value;

  /**
   * It specifies list of variables within an element constraint list[index - indexOffset] = value.
   * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0.
   */
  private final IntVar[] list;

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementVariableFast(IntVar index, IntVar[] list, IntVar value, int indexOffset) {

    super(index, indexOffset);
    checkInputForNullness(new String[] {"index", "value"}, new Object[] {index, value});
    checkInputForNullness("list", list);

    queueIndex = 1;

    this.numberId = idNumber.incrementAndGet();
    this.value = value;
    this.list = Arrays.copyOf(list, list.length);

    setScope(Stream.concat(Stream.concat(Stream.of(index), Arrays.stream(list)), Stream.of(value)));
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   */
  public ElementVariableFast(IntVar index, List<? extends IntVar> list, IntVar value) {

    this(index, list.toArray(new IntVar[0]), value, 0);
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementVariableFast(
      IntVar index, List<? extends IntVar> list, IntVar value, int indexOffset) {

    this(index, list.toArray(new IntVar[0]), value, indexOffset);
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   */
  public ElementVariableFast(IntVar index, IntVar[] list, IntVar value) {

    this(index, list, value, 0);
  }

  @Override
  protected int listLength() {
    return list.length;
  }

  @Override
  public void impose(Store store) {
    imposeInit(store);
  }

  @Override
  public void consistency(Store store) {

    if (init.begin(store)) {
      initFirstConsistencyCheck(store);
    }

    if (value.singleton() && index.singleton()) {
      IntVar v = list[index.value() - 1 - indexOffset];
      v.domain.inValue(store.level, v, value.value());
      removeConstraint();
      return;
    }
    if (index.singleton()) {
      int position = index.value() - 1 - indexOffset;
      value.domain.in(store.level, value, list[position].domain);
      list[position].domain.in(store.level, list[position], value.domain);
      return;
    }

    int min = IntDomain.MAX_INT;
    int max = IntDomain.MIN_INT;
    int valueMin = value.min();
    // the values of the selectable positions, as bits from valueMin, when the value spans 64 values
    boolean smallValue = !value.singleton() && (long) value.max() - valueMin < 64;
    long supportBits = 0;
    IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
    boolean indexDomNonEmpty = false;
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int position = e.nextElement() - 1 - indexOffset;

      if (disjoint(value, list[position])) {
        indexDomNonEmpty = true;
        if (indexDom.size == 0) {
          indexDom.unionAdapt(position + 1 + indexOffset);
        } else {
          indexDom.addLastElement(position + 1 + indexOffset);
        }
      } else {
        min = Math.min(min, list[position].min());
        max = Math.max(max, list[position].max());
        if (smallValue) {
          supportBits |= list[position].domain.bitsFrom(valueMin);
        }
      }
    }

    if (indexDomNonEmpty) {
      index.domain.in(store.level, index, indexDom.complement());
    }
    value.domain.in(store.level, value, min, max);
    if (smallValue && (value.domain.bitsFrom(valueMin) & ~supportBits) != 0) {
      // a value inside the bounds that no selectable position can take; kept to small value
      // domains, where the union is a few word operations
      value.domain.in(
          store.level, value, new SmallDenseDomain(valueMin, Long.reverse(supportBits)));
    }

    if (index.singleton()) {
      // index is singleton; value == list[index - 1 - offset]
      IntVar lp = list[index.value() - 1 - indexOffset];
      value.domain.in(store.level, value, lp.domain);
      lp.domain.in(store.level, lp, value.domain);
    }
  }

  @Override
  public boolean satisfied() {
    return satisfiedForVariableList(list, value);
  }

  @Override
  public String toString() {
    return buildToString("elementVariableFast", list, value, true);
  }

  @Override
  public Optional<List<Constraint>> simplify() {
    if (getClass() != ElementVariableFast.class) {
      return Optional.empty();
    }
    return ElementSimplification.variables(
        index,
        list,
        value,
        indexOffset,
        (i, l, offset) -> new ElementVariableFast(i, l, value, offset),
        (i, l, offset) -> new ElementIntegerFast(i, l, value, offset));
  }

  @Override
  public ElementVariableFast copy(VarMap map) {
    return new ElementVariableFast(map.get(index), map.get(list), map.get(value), indexOffset);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == ElementVariableFast.class
        && ElementVariableExplanation.explain(trail, entry, index, list, value, indexOffset, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == ElementVariableFast.class
        && ElementVariableExplanation.explainFailure(trail, index, list, value, indexOffset, out);
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    int i = value.applyAsInt(index) - indexOffset - 1;
    if (i < 0 || i >= list.length) {
      return 1;
    }
    return value.applyAsInt(list[i]) == value.applyAsInt(this.value) ? 0 : 1;
  }

  @Override
  public IntVar functionalResult() {
    return value;
  }

  @Override
  public int functionalValue(ToIntFunction<IntVar> value) {
    int i = value.applyAsInt(index) - indexOffset - 1;
    return value.applyAsInt(list[Math.max(0, Math.min(list.length - 1, i))]);
  }
}
