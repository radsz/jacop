/*
 * AbstractPcompQ.java
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
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Abstract base for two-variable float comparison constraints (PlteqQ, PgtQ, PltQ, PgteqQ).
 * Provides shared fields, constructor logic, and pruning event configuration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractPcompQ extends PrimitiveConstraint {

  /** It specifies the first float variable. */
  public final FloatVar p;

  /** It specifies the second float variable. */
  public final FloatVar q;

  /**
   * Constructs a comparison constraint between two float variables.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param p variable p.
   * @param q variable q.
   */
  protected AbstractPcompQ(AtomicInteger idNum, FloatVar p, FloatVar q) {

    checkInputForNullness(new String[] {"p", "q"}, new Object[] {p, q});

    numberId = idNum.incrementAndGet();

    this.p = p;
    this.q = q;

    setScope(p, q);
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return FloatDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return FloatDomain.BOUND;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return FloatDomain.BOUND;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return FloatDomain.BOUND;
  }
}
