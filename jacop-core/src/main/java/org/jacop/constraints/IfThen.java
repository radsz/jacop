/*
 * IfThen.java
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
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.QueueForward;

/**
 * Constraint if constraint1 then constraint2.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class IfThen extends PrimitiveConstraint implements UsesQueueVariable {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  public final QueueForward<PrimitiveConstraint> queueForward;

  /** It specifies constraint condC in the IfThen constraint. */
  public final PrimitiveConstraint condC;

  /** It specifies constraint condC in the IfThen constraint. */
  public final PrimitiveConstraint thenC;

  boolean imposed;
  Store store;

  /**
   * It constructs ifthen constraint.
   *
   * @param condC the condition of the ifthen constraint.
   * @param thenC the constraint which must hold if the condition holds.
   */
  public IfThen(PrimitiveConstraint condC, PrimitiveConstraint thenC) {

    PrimitiveConstraint[] scope = new PrimitiveConstraint[] {condC, thenC};
    checkInputForNullness(new String[] {"condC", "thenC"}, scope);
    numberId = idNumber.incrementAndGet();
    this.condC = condC;
    this.thenC = thenC;
    setScope(scope);
    setConstraintScope(scope);
    queueForward = new QueueForward<>(new PrimitiveConstraint[] {condC, thenC}, arguments());
    this.queueIndex = Integer.max(condC.queueIndex, thenC.queueIndex);
  }

  @Override
  public void consistency(Store store) {

    if (condC.satisfied()) {
      if (imposed) {
        this.removeConstraint();
        store.impose(thenC);
        return;
      } else {
        thenC.consistency(store);
      }
    }

    if (thenC.notSatisfied()) {
      if (imposed) {
        this.removeConstraint();
        store.impose(new Not(condC));
      } else {
        condC.notConsistency(store);
      }
    }
  }

  @Override
  public boolean notSatisfied() {
    return condC.satisfied() && thenC.notSatisfied();
  }

  @Override
  public void notConsistency(Store store) {

    thenC.notConsistency(store);
    condC.consistency(store);
  }

  @Override
  public int getConsistencyPruningEvent(Var var) {

    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(var);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return computeMaxPruningEvent(var, condC, thenC);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("It should not be called as overrides exist.");
  }

  @Override
  public int getNotConsistencyPruningEvent(Var var) {

    if (notConsistencyPruningEvents != null) {
      Integer possibleEvent = notConsistencyPruningEvents.get(var);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return computeMaxPruningEvent(var, condC, thenC);
  }

  @Override
  public int getNestedPruningEvent(Var var, boolean mode) {

    if (mode) {
      if (consistencyPruningEvents != null) {
        Integer possibleEvent = consistencyPruningEvents.get(var);
        if (possibleEvent != null) {
          return possibleEvent;
        }
      }
    } else {
      if (notConsistencyPruningEvents != null) {
        Integer possibleEvent = notConsistencyPruningEvents.get(var);
        if (possibleEvent != null) {
          return possibleEvent;
        }
      }
    }
    return computeMaxPruningEvent(var, condC, thenC);
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    throw new IllegalStateException("It should not be called as overrides exist.");
  }

  @Override
  public void impose(Store store) {

    this.store = store;
    super.impose(store);
    imposed = true;
  }

  @Override
  public void include(Store store) {
    this.store = store;
  }

  @Override
  public boolean satisfied() {

    if (imposed) {
      return condC.notSatisfied();
    } else {
      return condC.satisfied() && thenC.satisfied() || condC.notSatisfied();
    }
  }

  @Override
  public String toString() {

    return id() + " : IfThen(" + condC + ", " + thenC + " )\n";
  }

  @Override
  public void queueVariable(int level, Var variable) {

    queueForward.queueForward(level, variable);
  }
}
