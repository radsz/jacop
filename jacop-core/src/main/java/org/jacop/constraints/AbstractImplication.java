/*
 * AbstractImplication.java
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

import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.QueueForward;

/**
 * The propagation of an implication {@code b = on => c} of a 0/1 variable and a primitive
 * constraint: {@link Implies} (on = 1) and {@link ImpliesNot} (on = 0).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractImplication extends AbstractReifiedConstraint {

  private final QueueForward<PrimitiveConstraint> queueForward;

  // the value of b that enforces c
  private final int on;

  /**
   * It constructs the implication {@code b = on => c}.
   *
   * @param b the 0/1 variable of the implication.
   * @param c the constraint which must hold if b has the value on.
   * @param on the value, 0 or 1, of b that enforces c.
   */
  protected AbstractImplication(IntVar b, PrimitiveConstraint c, int on) {
    super(b, c);
    this.on = on;
    setScope(Stream.concat(c.arguments().stream(), Stream.of(b)));
    setConstraintScope(c);
    queueForward = new QueueForward<>(c, arguments());
    this.queueIndex = c.queueIndex;
  }

  // b has the value that enforces c
  private boolean enforced() {
    return on == 1 ? b.min() == 1 : b.max() == 0;
  }

  // b cannot take the value that enforces c
  private boolean released() {
    return on == 1 ? b.max() == 0 : b.min() == 1;
  }

  @Override
  public void consistency(Store store) {

    if (c.satisfied()) {
      removeConstraint();
    } else if (c.notSatisfied()) {
      b.domain.inValue(store.level, b, 1 - on);
      removeConstraint();
    } else if (released()) {
      removeConstraint();
    } else if (enforced()) {
      c.consistency(store);
    }
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    if (v != b
        && (consistencyPruningEvents == null || !consistencyPruningEvents.containsKey(v))
        && isSimpleNestedConstraintOver(v)) {
      // consistency() needs c.notSatisfied() before b is fixed, decided on c's nested event for
      // its negation, and c.consistency() after, on c's own consistency event; c's own event alone
      // can be GROUND where deciding c.notSatisfied() needs BOUND (x >= 6 fails once x <= 5).
      // c.satisfied() only removes the constraint early, so it does not need c's events for
      // satisfaction, which can be ANY where c's are GROUND (XneqY).
      return Math.max(
          IntDomain.GROUND,
          Math.max(c.getConsistencyPruningEvent(v), c.getNestedPruningEvent(v, false)));
    }
    return super.getConsistencyPruningEvent(v);
  }

  @Override
  public int getNestedPruningEvent(Var v, boolean mode) {
    // nested in Not or Reified, notConsistency() and satisfied() decide the outer constraint
    return super.getConsistencyPruningEvent(v);
  }

  @Override
  protected int getNestedPropagationEvent(Var v) {
    // consistency() only ever runs c.consistency().
    return isSimpleNestedConstraintOver(v) ? c.getConsistencyPruningEvent(v) : Domain.NONE;
  }

  @Override
  public boolean notSatisfied() {
    return enforced() && c.notSatisfied();
  }

  @Override
  public void notConsistency(Store store) {

    // b first: c may share b, and c.notConsistency() must see it fixed
    b.domain.inValue(store.level, b, on);
    c.notConsistency(store);
  }

  @Override
  public boolean satisfied() {

    return (enforced() && c.satisfied()) || released();
  }

  @Override
  public void queueVariable(int level, Var variable) {
    queueForward.queueForward(level, variable);
  }

  /**
   * It tells whether the nested constraint, and so the implication, can be copied.
   *
   * @return true if c can be copied.
   */
  public boolean canCopy() {
    return Copyable.canCopy(c);
  }
}
