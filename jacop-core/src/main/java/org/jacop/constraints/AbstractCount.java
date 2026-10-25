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
import org.jacop.core.TrailedInts;

/**
 * Abstract base for Count, CountVar and CountBounds constraints. Provides shared fields (list,
 * position, equal), the backtrackable state behind them, swap, and default pruning events.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractCount extends PrimitiveConstraint {

  /** The list of variables which are checked and counted if equal to specified value. */
  protected final IntVar[] list;

  private static final int POSITION = 0;

  private static final int EQUAL = 1;

  /**
   * The first position of undecided variables, the variables before it being decided, and the
   * number of decided variables equal to the value.
   */
  private TrailedInts state;

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

    state = new TrailedInts(store, 2);
  }

  @Override
  public void include(Store store) {
    state = new TrailedInts(store, 2);
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
    state.set(EQUAL, numberEq);
    state.set(POSITION, start);
  }

  /**
   * Returns the first position of undecided variables; the variables before it are decided.
   *
   * @return the position.
   */
  protected int position() {
    return state.get(POSITION);
  }

  /**
   * Returns the number of decided variables equal to the value.
   *
   * @return the number of decided variables equal to the value.
   */
  protected int equal() {
    return state.get(EQUAL);
  }

  /** The number of variables equal to the value, as found by the last count. */
  protected int countEq;

  /**
   * The number of variables that may still become equal to the value, as found by the last count.
   */
  protected int countMayBe;

  /** The new start position found by the last count. */
  protected int countStart;

  /**
   * Counts how many variables are definitely equal to the given value and how many might still
   * become equal, and stores them in {@link #countEq}, {@link #countMayBe} and {@link #countStart};
   * fields rather than a returned record, as the record is allocated on every call. This method has
   * a side effect: it swaps decided variables to the front of the list.
   *
   * @param value the value to count.
   */
  protected void countOccurrences(int value) {
    int numberEq = equal();
    int numberMayBe = 0;
    int start = position();
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
    countEq = numberEq;
    countMayBe = numberMayBe;
    countStart = start;
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
