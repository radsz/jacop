/*
 * IfThenElseBool.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.constraints;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;

/**
 * Constraint if condVar = 1 then thenVar = 1 else elseVar = 1 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
public class IfThenElseBool extends PrimitiveConstraint {

  static AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies constraint condVar in the IfThenElseBool constraint. */
  public BooleanVar condVar;

  /** It specifies constraint thenVar in the IfThenElseBool constraint. */
  public BooleanVar thenVar;

  /** It specifies constraint elseVar in the IfThenElseBool constraint. */
  public BooleanVar elseVar;

  // imposed variable to manifest that constraint has been imposed (top-level)
  // constraint
  boolean imposed = false;

  Store store;

  /**
   * It creates ifthenelse constraint.
   *
   * @param condVar the condition of the constraint.
   * @param thenVar the condition which must be true if the constraint condition is true.
   * @param elseVar the condition which must be true if the constraint condition is not true.
   */
  // Constructors
  public IfThenElseBool(BooleanVar condVar, BooleanVar thenVar, BooleanVar elseVar) {

    BooleanVar[] scope = new BooleanVar[] {condVar, thenVar, elseVar};
    checkInputForNullness(new String[] {"condVar", "thenVar", "elseVar"}, scope);

    numberId = idNumber.incrementAndGet();

    this.condVar = condVar;
    this.thenVar = thenVar;
    this.elseVar = elseVar;

    setScope(scope);
    this.queueIndex = 0;
  }

  @Override
  public void consistency(Store store) {

    if (condVar.min() == 1) thenVar.domain.inValue(store.level, thenVar, 1);
    else if (condVar.max() == 0) elseVar.domain.inValue(store.level, elseVar, 1);

    if (imposed) {

      if (thenVar.max() == 0) {
        condVar.domain.inValue(store.level, condVar, 0);
        elseVar.domain.inValue(store.level, elseVar, 1);
      }

      if (elseVar.max() == 0) {
        condVar.domain.inValue(store.level, condVar, 1);
        thenVar.domain.inValue(store.level, thenVar, 1);
      }
    }
  }

  @Override
  public boolean notSatisfied() {
    return (condVar.min() == 1 && thenVar.max() == 0) || (condVar.max() == 0 && elseVar.max() == 0);
  }

  @Override
  public void notConsistency(Store store) {

    if (condVar.max() == 0) elseVar.domain.inValue(store.level, elseVar, 0);

    if (condVar.min() == 1) thenVar.domain.inValue(store.level, thenVar, 0);
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void impose(Store store) {

    super.impose(store);

    this.store = store;
    imposed = true;
  }

  @Override
  public boolean satisfied() {

    if (imposed) {

      if (condVar.min() == 1) {
        this.removeConstraint();
        store.impose(new XeqC(thenVar, 1));
        return false;
      }

      if (condVar.max() == 0) {
        this.removeConstraint();
        store.impose(new XeqC(elseVar, 1));
        return false;
      }
    }

    return (condVar.min() == 1 && thenVar.min() == 1) || (condVar.max() == 0 && elseVar.min() == 1);
  }

  @Override
  public String toString() {

    StringBuffer result = new StringBuffer(id());
    result.append(" : IfThenElseBool(").append(condVar).append(", ");
    result.append(thenVar).append(", ").append(elseVar).append(" )");

    return result.toString();
  }
}
