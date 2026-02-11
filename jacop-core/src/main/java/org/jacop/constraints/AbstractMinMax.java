/*
 * AbstractMinMax.java
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
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * Abstract base class for Min and Max constraints. Provides shared fields, constructor logic, swap,
 * impose, and pruning event.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractMinMax extends Constraint implements SatisfiedPresent {

  /** It specifies a list of variables among which the extremum is being searched for. */
  public final IntVar[] list;

  /** It specifies the target variable storing the min or max value. */
  public final IntVar target;

  /** It specifies length of the list. */
  final int l;

  /** Defines first position of the variable that needs to be considered. */
  protected TimeStamp<Integer> position;

  /**
   * Constructs the base min/max constraint.
   *
   * @param idNum the atomic id counter for the concrete constraint type
   * @param list the array of variables
   * @param target the min or max variable
   */
  protected AbstractMinMax(AtomicInteger idNum, IntVar[] list, IntVar target) {
    checkInputForNullness("list", list);
    checkInputForNullness("target", new Object[] {target});

    this.l = list.length;
    this.target = target;
    this.list = Arrays.copyOf(list, list.length);

    if (list.length > 1000) {
      this.queueIndex = 2;
    } else {
      this.queueIndex = 1;
    }

    this.numberId = idNum.incrementAndGet();

    setScope(Stream.concat(Arrays.stream(list), Stream.of(target)));
  }

  /**
   * Swaps two variables in the list.
   *
   * @param i first index
   * @param j second index
   */
  protected void swap(int i, int j) {
    if (i != j) {
      IntVar tmp = list[i];
      list[i] = list[j];
      list[j] = tmp;
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {
    super.impose(store);
    position = new TimeStamp<>(store, 0);
  }
}
