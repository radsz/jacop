/*
 * AbstractXcompY.java
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

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * Abstract base for two-variable integer comparison constraints (XgtY, XltY, XgteqY, XlteqY).
 * Provides shared fields and constructor logic, with pruning event configuration that returns
 * {@link IntDomain#BOUND} for all pruning events.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractXcompY extends AbstractConstraintXandY {

  /**
   * Constructs a comparison constraint between two integer variables.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param x variable x.
   * @param y variable y.
   */
  protected AbstractXcompY(AtomicInteger idNum, IntVar x, IntVar y) {

    super(idNum, x, y);
  }

  /**
   * It tells which bounds consistency() reads: the minimum of x and the maximum of y for x
   * {@literal <=} y and x {@literal <} y, or the maximum of x and the minimum of y otherwise.
   *
   * @return true if consistency() reads the minimum of x and the maximum of y.
   */
  protected abstract boolean readsMinOfX();

  @Override
  public int getBoundPruningEvent(Var v) {
    if (x == y) {
      return IntDomain.BOUND;
    }
    return (v == x) == readsMinOfX() ? IntDomain.MIN_EVENT : IntDomain.MAX_EVENT;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }
}
