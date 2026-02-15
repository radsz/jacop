/*
 * CountVar.java
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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * CountVar constraint implements the counting over number of occurrences of a given value in a list
 * of variables. The number of occurrences is specified by variable counter.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CountVar extends AbstractCount {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable to count the number of occurences of the specified value in a list. */
  private final IntVar counter;

  /** The value to which is any variable is equal to makes the constraint count it. */
  private final IntVar value;

  /**
   * It constructs a CountVar constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public CountVar(IntVar[] list, IntVar counter, IntVar value) {

    super(idNumber, list);

    checkInputForNullness(
        new String[] {"list", "counter", "value"},
        list,
        new Object[] {counter},
        new Object[] {value});

    this.counter = counter;
    this.value = value;

    setScope(
        Stream.concat(
            Stream.of(value), Stream.concat(Arrays.stream(this.list), Stream.of(counter))));
  }

  /**
   * It constructs a CountVar constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public CountVar(List<? extends IntVar> list, IntVar counter, IntVar value) {
    this(list.toArray(new IntVar[0]), counter, value);
  }

  @Override
  public void consistency(final Store store) {

    CountState state = countEqualAndMaybe();

    if (state.numberMayBe == counter.min() - state.numberEq) {
      if (applyWhenMayBeTight(store, state.start, state.numberEq, state.numberMayBe)) {
        return;
      }
    } else if (state.numberEq == counter.max()) {
      if (applyWhenEqMax(store, state.start, state.numberEq)) {
        return;
      }
    }

    updateState(state.numberEq, state.start);

    counter.domain.in(store.level, counter, state.numberEq, state.numberEq + state.numberMayBe);
  }

  private CountState countEqualAndMaybe() {
    int numberEq = equal.value();
    int numberMayBe = 0;
    int start = position.value();
    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      if (v.domain.isIntersecting(value.domain)) {
        if (v.singleton() && value.singleton() && v.value() == value.value()) {
          numberEq++;
          swap(start, i);
          start++;
        } else {
          numberMayBe++;
        }
      } else {
        swap(start, i);
        start++;
      }
    }
    return new CountState(numberEq, numberMayBe, start);
  }

  private record CountState(int numberEq, int numberMayBe, int start) {}

  /**
   * Applies pruning when numberMayBe == counter.min() - numberEq; returns true if constraint
   * removed.
   */
  private boolean applyWhenMayBeTight(Store store, int start, int numberEq, int numberMayBe) {
    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      v.domain.in(store.level, v, value.domain);
    }

    if (value.singleton()) {
      numberEq += numberMayBe;
      counter.domain.inValue(store.level, counter, numberEq);
      removeConstraint();
      return true;
    }
    return false;
  }

  /** Applies pruning when numberEq == counter.max(); returns true if constraint removed. */
  private boolean applyWhenEqMax(Store store, int start, int numberEq) {
    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      if (value.singleton()) {
        v.domain.inComplement(store.level, v, value.value());
      }
    }
    if (value.singleton()) {
      counter.domain.inValue(store.level, counter, numberEq);
      removeConstraint();
      return true;
    }
    return false;
  }

  @Override
  public void notConsistency(final Store store) {

    int numberEq = equal.value();
    int numberMayBe = 0;
    int start = position.value();
    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      if (v.domain.isIntersecting(value.domain)) {
        if (v.singleton() && value.singleton() && v.value() == value.value()) {
          numberEq++;
          swap(start, i);
          start++;
        } else {
          numberMayBe++;
        }
      } else { // does not have the value in its domain
        swap(start, i);
        start++;
      }
    }

    if (numberEq > counter.max() || numberEq + numberMayBe < counter.min()) {
      removeConstraint();
      return;
    }

    if (start == list.length) {
      counter.domain.inComplement(store.level, counter, numberEq);
    }

    updateState(numberEq, start);
  }

  @Override
  public boolean satisfied() {

    int eq = 0;
    int notEq = 0;

    for (IntVar v : list) {
      if (v.singleton() && value.singleton() && v.value() == value.value()) {
        eq++;
      } else if (!v.domain.isIntersecting(value.domain)) {
        notEq++;
      }
    }

    return eq + notEq == list.length && counter.singleton(eq);
  }

  @Override
  public boolean notSatisfied() {

    int eq = 0;
    int notEq = 0;

    for (IntVar v : list) {
      if (v.singleton() && value.singleton() && v.value() == value.value()) {
        eq++;
      } else if (!v.domain.isIntersecting(value.domain)) {
        notEq++;
      }
    }

    return eq > counter.max() // equal values is more than allowed
        || list.length - notEq < counter.min() // possibly equal values is too low
        || (eq + notEq == list.length && !counter.domain.contains(eq)); // final check
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : countVar(").append(value).append(",[");
    appendArrayToString(result, list);
    result.append("], ").append(counter).append(" )");

    return result.toString();
  }
}
