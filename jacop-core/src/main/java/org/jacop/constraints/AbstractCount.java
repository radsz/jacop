/*
 * AbstractCount.java
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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * Abstract base for Count, CountVar and CountBounds constraints. Provides shared fields (list,
 * position, equal), impose/include for TimeStamp initialization, swap, and default pruning events.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractCount extends PrimitiveConstraint {

  /** The list of variables which are checked and counted if equal to specified value. */
  protected final IntVar[] list;

  /** Tracks the first position of undecided variables. */
  protected TimeStamp<Integer> position;

  /** Tracks the number of variables equal to the value. */
  protected TimeStamp<Integer> equal;

  /**
   * Constructs the common parts of a Count constraint.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param list the array of variables to count over.
   */
  protected AbstractCount(AtomicInteger idNum, IntVar[] list) {
    this.queueIndex = 1;
    this.numberId = idNum.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
  }

  @Override
  public void impose(Store store) {

    super.impose(store);

    position = new TimeStamp<>(store, 0);
    equal = new TimeStamp<>(store, 0);
  }

  @Override
  public void include(Store store) {
    position = new TimeStamp<>(store, 0);
    equal = new TimeStamp<>(store, 0);
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.ANY;
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
   * Updates the backtrackable state after counting.
   *
   * @param numberEq the number of variables definitely equal.
   * @param start the new position value.
   */
  protected void updateState(int numberEq, int start) {
    equal.update(numberEq);
    position.update(start);
  }

  /** Holds the result of counting occurrences of a value in the list. */
  protected record CountResult(int numberEq, int numberMayBe, int start) {}

  /**
   * Counts how many variables are definitely equal to the given value and how many might still
   * become equal. This method has a side effect: it swaps decided variables to the front of the
   * list.
   *
   * @param value the value to count.
   * @return a record with the counts and the new start position.
   */
  protected CountResult countOccurrences(int value) {
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
    return new CountResult(numberEq, numberMayBe, start);
  }

  /** Holds the counts of variables that are satisfied or definitely not equal. */
  protected record SatisfactionCounts(int eq, int notEq) {}

  /**
   * Counts variables that are grounded to the given value and those that definitely cannot equal
   * it.
   *
   * @param value the value to check.
   * @return a record with eq and notEq counts.
   */
  protected SatisfactionCounts countSatisfaction(int value) {
    int eq = 0;
    int notEq = 0;
    for (IntVar v : list) {
      if (v.singleton(value)) {
        eq++;
      } else if (!v.domain.contains(value)) {
        notEq++;
      }
    }
    return new SatisfactionCounts(eq, notEq);
  }
}
