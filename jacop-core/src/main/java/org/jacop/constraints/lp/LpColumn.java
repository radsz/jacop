/*
 * LpColumn.java
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

package org.jacop.constraints.lp;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;

/**
 * A column of the linear relaxation that is not a variable of the store: the auxiliary 0/1 column
 * {@code [x = v]} of a value encoding that the model has no Boolean for. It is never pruned and
 * never searched on; its bounds stay those it was made with. The relaxation removes it from every
 * inequality it deduces, at the bound that keeps the inequality valid, so that pruning and its
 * explanations only use variables of the store.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LpColumn extends IntVar {

  private static final AtomicInteger NUMBER = new AtomicInteger();

  private final IntVar variable;
  private final int value;

  /**
   * Creates the 0/1 column {@code [variable = value]}.
   *
   * @param variable the variable whose value the column indicates
   * @param value the value
   */
  public LpColumn(IntVar variable, int value) {
    super();
    this.variable = variable;
    this.value = value;
    id = "lp_" + variable.id() + "=" + value + "#" + NUMBER.incrementAndGet();
    domain = new IntervalDomain(0, 1);
    refreshBounds();
  }

  /**
   * Returns the variable whose value the column indicates.
   *
   * @return the variable
   */
  public IntVar variable() {
    return variable;
  }

  /**
   * Returns the value the column indicates.
   *
   * @return the value
   */
  public int value() {
    return value;
  }

  /**
   * Returns the 0 or 1 the column has in a solution, given the value of its variable there.
   *
   * @param of the value of the variable
   * @return 1 when it is the value of the column, 0 otherwise
   */
  public int valueIn(int of) {
    return of == value ? 1 : 0;
  }

  /**
   * Returns the column of the same value for a copy of the relaxation, over the copy of its
   * variable.
   *
   * @param copied the copy of the variable
   * @return the new column
   */
  public LpColumn copy(IntVar copied) {
    return new LpColumn(copied, value);
  }
}
