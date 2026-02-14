/*
 * Count.java
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
 * Count constraint implements the counting over number of occurrences of a given value in a list of
 * variables. The number of occurrences is specified by variable counter.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Count extends AbstractCount {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It specifies variable idNumber to count the number of occurences of the specified value in a
   * list.
   */
  private final IntVar counter;

  /** The value to which is any variable is equal to makes the constraint count it. */
  private final int value;

  /**
   * It constructs a Count constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public Count(IntVar[] list, IntVar counter, int value) {

    super(idNumber, list);

    checkInputForNullness(new String[] {"list", "counter"}, list, new Object[] {counter});

    this.counter = counter;
    this.value = value;

    setScope(Stream.concat(Arrays.stream(this.list), Stream.of(counter)));
  }

  /**
   * It constructs a Count constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public Count(List<? extends IntVar> list, IntVar counter, int value) {
    this(list.toArray(new IntVar[0]), counter, value);
  }

  @Override
  public void consistency(final Store store) {

    int numberEq = equal.value();
    int numberMayBe = 0;
    int start = position.value();
    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      if (v.domain.contains(value)) {
        if (v.singleton()) {
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

    if (numberMayBe == counter.min() - numberEq) {
      for (int i = start; i < list.length; i++) {
        IntVar v = list[i];
        v.domain.inValue(store.level, v, value);
      }

      numberEq += numberMayBe;

      counter.domain.inValue(store.level, counter, numberEq);
      removeConstraint();
      return;

    } else if (numberEq == counter.max()) {
      for (int i = start; i < list.length; i++) {
        IntVar v = list[i];
        v.domain.inComplement(store.level, v, value);
      }

      counter.domain.inValue(store.level, counter, numberEq);
      removeConstraint();
      return;
    }

    counter.domain.in(store.level, counter, numberEq, numberEq + numberMayBe);

    updateState(numberEq, start);
  }

  @Override
  public void notConsistency(final Store store) {

    int numberEq = equal.value();
    int numberMayBe = 0;
    int start = position.value();
    for (int i = start; i < list.length; i++) {
      IntVar v = list[i];
      if (v.domain.contains(value)) {
        if (v.singleton()) {
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
      if (v.singleton(value)) {
        eq++;
      } else if (!v.domain.contains(value)) {
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
      if (v.singleton(value)) {
        eq++;
      } else if (!v.domain.contains(value)) {
        notEq++;
      }
    }

    return eq + notEq == list.length && !counter.domain.contains(eq);
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : count(").append(value).append(",[");
    appendArrayToString(result, list);
    result.append("], ").append(counter).append(" )");

    return result.toString();
  }
}
