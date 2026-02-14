/*
 * AbstractPcompC.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.constraints;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Domain;
import org.jacop.floats.core.FloatVar;

/**
 * Abstract base for float variable-vs-constant comparison constraints (PgtC, PltC, PgteqC, PlteqC,
 * PeqC, PneqC). Provides shared fields, constructor logic, and the two non-nested pruning event
 * methods.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractPcompC extends PrimitiveConstraint {

  /** It specifies the float variable. */
  protected final FloatVar p;

  /** It specifies the constant. */
  public final double c;

  /**
   * Constructs a comparison constraint between a float variable and a constant.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param p variable p.
   * @param c constant c.
   */
  protected AbstractPcompC(AtomicInteger idNum, FloatVar p, double c) {

    checkInputForNullness("p", new Object[] {p});

    numberId = idNum.incrementAndGet();

    this.p = p;
    this.c = c;

    setScope(p);
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return Domain.NONE;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return Domain.NONE;
  }
}
