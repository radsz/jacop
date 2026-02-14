/*
 * AbstractCountValues.java
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * Abstract base for CountValues and CountValuesBounds constraints. Provides shared fields (list,
 * values, valuesDomain, position, equal[], rest), impose, swap, and default pruning event.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractCountValues extends Constraint implements SatisfiedPresent {

  /** The list of variables which are checked and counted if equal to specified value. */
  protected final IntVar[] list;

  /** The values to which variables are compared. */
  protected final int[] values;

  /** Domain consisting of all counted values. */
  final IntDomain valuesDomain;

  /** Complement of valuesDomain. */
  final IntDomain valuesDomainComplement;

  /** Length of the list. */
  final int n;

  /** Tracks the first position of undecided variables. */
  protected TimeStamp<Integer> position;

  /** Tracks the number of variables equal to each value. */
  @SuppressWarnings("unchecked")
  protected TimeStamp<Integer>[] equal;

  /** Tracks the number of variables not matching any counted value. */
  protected TimeStamp<Integer> rest;

  /**
   * Constructs the common parts of a CountValues constraint.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param list the array of variables to count over.
   * @param values the array of values to count.
   */
  protected AbstractCountValues(AtomicInteger idNum, IntVar[] list, int[] values) {
    this.queueIndex = 1;
    this.numberId = idNum.incrementAndGet();
    this.n = list.length;
    this.list = Arrays.copyOf(list, n);
    this.values = values;

    this.valuesDomain = new IntervalDomain();
    for (int v : values) {
      valuesDomain.unionAdapt(v);
    }
    this.valuesDomainComplement = valuesDomain.complement();
  }

  @SuppressWarnings("unchecked")
  @Override
  public void impose(Store store) {

    super.impose(store);

    position = new TimeStamp<>(store, 0);
    equal = new TimeStamp[values.length];
    for (int i = 0; i < values.length; i++) {
      equal[i] = new TimeStamp<>(store, 0);
    }
    rest = new TimeStamp<>(store, 0);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
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
}
