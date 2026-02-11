/*
 * AbstractAtLeastMost.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * Abstract base for AtLeast and AtMost constraints. Both count occurrences of a given value in a
 * list of variables and share identical field layout, constructors, counting loop, and pruning
 * event configuration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractAtLeastMost extends PrimitiveConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The required count threshold. */
  public final int counter;

  /** The list of variables checked for occurrences of value. */
  public final IntVar[] list;

  /** The value whose occurrences are counted. */
  public final int value;

  /** Whether this constraint is used in a reified context. */
  boolean reified = true;

  private TimeStamp<Integer> position;

  private TimeStamp<Integer> equal;

  /**
   * Constructs the constraint.
   *
   * @param list variables to inspect.
   * @param counter count threshold.
   * @param value value to count.
   */
  protected AbstractAtLeastMost(IntVar[] list, int counter, int value) {

    checkInputForNullness("list", list);

    this.queueIndex = 1;
    this.numberId = idNumber.incrementAndGet();

    this.list = Arrays.copyOf(list, list.length);
    this.counter = counter;
    this.value = value;

    setScope(list);
  }

  /**
   * Constructs the constraint from a list.
   *
   * @param list variables to inspect.
   * @param counter count threshold.
   * @param value value to count.
   */
  protected AbstractAtLeastMost(List<? extends IntVar> list, int counter, int value) {
    this(list.toArray(new IntVar[0]), counter, value);
  }

  @Override
  public void include(Store store) {
    position = new TimeStamp<>(store, 0);
    equal = new TimeStamp<>(store, 0);
  }

  @Override
  public void impose(Store store) {

    reified = false;

    super.impose(store);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  /**
   * Swaps two elements in the list array.
   *
   * @param i first index.
   * @param j second index.
   */
  protected void swap(int i, int j) {
    if (i != j) {
      IntVar tmp = list[i];
      list[i] = list[j];
      list[j] = tmp;
    }
  }

  /**
   * Scans the list from the current position, counting variables that are singletons equal to value
   * (numberEq) and variables whose domain still contains value but are not ground (numberMayBe).
   * Variables that are ground to value or do not contain value are swapped to the front and the
   * position is advanced.
   *
   * @return an array {@code [numberEq, numberMayBe, start]} where start is the updated scan
   *     position.
   */
  protected int[] computeCounts() {
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
      } else {
        swap(start, i);
        start++;
      }
    }
    return new int[] {numberEq, numberMayBe, start};
  }

  /**
   * Persists the latest counting state into backtrackable timestamps.
   *
   * @param numberEq number of variables known to equal value.
   * @param start first index not yet processed.
   */
  protected void updateState(int numberEq, int start) {
    equal.update(numberEq);
    position.update(start);
  }
}
