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
  public final IntVar[] list;

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
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
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
}
