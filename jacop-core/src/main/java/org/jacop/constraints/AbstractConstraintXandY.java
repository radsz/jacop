/*
 * AbstractConstraintXandY.java
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
import org.jacop.core.IntVar;

/**
 * Abstract base class for primitive constraints that operate on two integer variables x and y.
 * Provides shared field declarations and constructor logic.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractConstraintXandY extends PrimitiveConstraint {

  /** It specifies variable x. */
  protected final IntVar x;

  /** It specifies variable y. */
  protected final IntVar y;

  /**
   * Constructs a two-variable primitive constraint.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param x variable x.
   * @param y variable y.
   */
  protected AbstractConstraintXandY(AtomicInteger idNum, IntVar x, IntVar y) {

    checkInputForNullness(new String[] {"x", "y"}, new Object[] {x, y});

    numberId = idNum.incrementAndGet();

    this.x = x;
    this.y = y;

    setScope(x, y);
  }
}
