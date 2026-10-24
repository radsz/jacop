/*
 * AbstractReifiedConstraint.java
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

import org.jacop.api.UsesQueueVariable;
import org.jacop.core.Domain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * Abstract base class for constraints with a boolean variable and nested constraint (e.g., Reified,
 * Implies). Provides shared pruning event methods and constructor validation.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractReifiedConstraint extends PrimitiveConstraint
    implements UsesQueueVariable {

  /**
   * It specifies variable b which stores status of the constraint (0 - for certain not satisfied, 1
   * - for certain satisfied).
   */
  public final IntVar b;

  /** It specifies constraint c which status is being checked. */
  public final PrimitiveConstraint c;

  /**
   * Constructs an abstract reified constraint.
   *
   * @param b the boolean variable.
   * @param c the nested constraint.
   */
  protected AbstractReifiedConstraint(IntVar b, PrimitiveConstraint c) {

    checkInputForNullness(new String[] {"c", "b"}, new Object[] {c, b});
    if (b.min() < 0 || b.max() > 1) {
      throw new IllegalArgumentException(
          "Variable b in reified constraint must have a domain within 0..1, not " + b);
    }

    this.b = b;
    this.c = c;
  }

  @Override
  public int getNestedPruningEvent(Var v, boolean mode) {
    return getConsistencyPruningEvent(v);
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return throwMorePreciseMethodExists();
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    int event = getConsistencyPruningEventForReified(v, b, c);
    if (consistencyPruningEvents != null && consistencyPruningEvents.containsKey(v)) {
      return event;
    }
    return Math.max(event, getNestedPropagationEvent(v));
  }

  /**
   * Returns the event on v that the methods of c run by consistency() need once b is fixed. The
   * nested pruning events of c only cover deciding whether c is satisfied, and for example
   * XplusCeqZ needs a ground variable for that while its consistency() prunes on any change.
   * Constraints composed of other constraints already report the events of their parts.
   *
   * @param v variable for which the event is computed.
   * @return the pruning event, or NONE if c does not need one.
   */
  protected int getNestedPropagationEvent(Var v) {
    if (!isSimpleNestedConstraintOver(v)) {
      return Domain.NONE;
    }
    return Math.max(c.getConsistencyPruningEvent(v), c.getNotConsistencyPruningEvent(v));
  }

  /**
   * Checks whether c is not composed of other constraints and has v among its arguments.
   *
   * @param v variable to look for.
   * @return true if the events of c's own methods should be used for v.
   */
  protected boolean isSimpleNestedConstraintOver(Var v) {
    return (c.constraintScope == null || c.constraintScope.isEmpty()) && c.arguments().contains(v);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return throwMorePreciseMethodExists();
  }

  @Override
  public int getNotConsistencyPruningEvent(Var v) {
    return getNotConsistencyPruningEventForReified(v, b, c);
  }
}
