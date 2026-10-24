/*
 * AbstractArgMinMax.java
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
import org.jacop.core.Var;

/**
 * Abstract base for ArgMax and ArgMin constraints. Provides shared fields, constructor logic,
 * default pruning events, and custom per-variable pruning event logic.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractArgMinMax extends Constraint implements SatisfiedPresent {

  /** It specifies a list of variables among which the extremum is being searched for. */
  protected final IntVar[] list;

  /** It specifies variable which stores the index of the extremum. */
  protected final IntVar extremeIndex;

  /** It specifies indexOffset within an element constraint list[index-indexOffset] = value. */
  protected int indexOffset;

  boolean firstConsistencyCheck = true;

  /**
   * Constructs an arg-min/max constraint.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param list the array of variables.
   * @param extremeIndex variable denoting the index of the extremum.
   */
  protected AbstractArgMinMax(AtomicInteger idNum, IntVar[] list, IntVar extremeIndex) {

    checkInputForNullness(new String[] {"list", "extremeIndex"}, list, new Object[] {extremeIndex});

    this.queueIndex = 1;
    this.numberId = idNum.incrementAndGet();
    this.indexOffset = 0;
    this.extremeIndex = extremeIndex;
    this.list = Arrays.copyOf(list, list.length);

    setScope(Stream.concat(Arrays.stream(list), Stream.of(extremeIndex)));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }

    if (v == extremeIndex) {
      return IntDomain.ANY;
    } else {
      return IntDomain.BOUND;
    }
  }
}
