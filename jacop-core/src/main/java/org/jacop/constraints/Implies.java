/*
 * Implies.java
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
import java.util.stream.Stream;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Constraint b {@literal =>} c (implication or half-reification).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Implies extends AbstractReifiedConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  boolean imposed;
  Store store;

  /**
   * It constructs ifthen constraint.
   *
   * @param b the varaible of the implied constraint.
   * @param c the constraint which must hold if the variable is 1.
   */
  public Implies(IntVar b, PrimitiveConstraint c) {

    super(b, c);
    numberId = idNumber.incrementAndGet();
    setScope(Stream.concat(c.arguments().stream(), Stream.of(b)));
    setConstraintScope(c);
    this.queueIndex = c.queueIndex;
  }

  @Override
  public void consistency(Store store) {

    if (c.satisfied()) {
      removeConstraint();
    } else if (c.notSatisfied()) {
      b.domain.inValue(store.level, b, 0);
      removeConstraint();
    } else if (b.max() == 0) {
      removeConstraint();
    } else if (b.min() == 1) {
      c.consistency(store);
    }
  }

  @Override
  public boolean notSatisfied() {
    return b.min() == 1 && c.notSatisfied();
  }

  @Override
  public void notConsistency(Store store) {

    c.notConsistency(store);
    b.domain.inValue(store.level, b, 1);
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

    return (b.min() == 1 && c.satisfied()) || (b.max() == 0);
  }

  @Override
  public String toString() {

    return id() + " : Implies(" + b + ", " + c + " )";
  }
}
