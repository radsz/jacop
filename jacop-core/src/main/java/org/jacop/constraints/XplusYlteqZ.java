/*
 * XplusYlteqZ.java
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
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Constraint X + Y{@literal =<} Z.
 *
 * <p>Bound consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XplusYlteqZ extends AbstractConstraintXandYandZ implements Copyable<XplusYlteqZ> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs X + Y{@literal <=} Z constraint.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XplusYlteqZ(IntVar x, IntVar y, IntVar z) {

    super(idNumber, x, y, z);
  }

  @Override
  public void impose(Store store) {

    if (satisfied()) {
      // XplusYlteqZ is trivially consistent.
      return;
    }

    super.impose(store);
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

  @Override
  public int getBoundPruningEvent(Var v) {
    // consistency() reads only the minima of x and y and the maximum of z
    if (x == z || y == z) {
      return IntDomain.BOUND;
    }
    return v == z ? IntDomain.MAX_EVENT : IntDomain.MIN_EVENT;
  }

  @Override
  public void consistency(final Store store) {
    if (x == z || y == z) {
      // x + y <= x means y <= 0 (and x + y <= y means x <= 0); the bounds below would shrink by
      // the other variable per call, but the constraint is not woken by its own pruning
      IntVar other = x == z ? y : x;
      other.domain.inMax(store.level, other, 0);
      return;
    }
    x.domain.inMax(store.level, x, z.max() - y.min());
    y.domain.inMax(store.level, y, z.max() - x.min());
    z.domain.inMin(store.level, z, x.min() + y.min());
  }

  @Override
  public void notConsistency(final Store store) {
    if (x == z || y == z) {
      IntVar other = x == z ? y : x;
      other.domain.inMin(store.level, other, 1);
      return;
    }

    x.domain.inMin(store.level, x, z.min() - y.max() + 1);

    y.domain.inMin(store.level, y, z.min() - x.max() + 1);

    z.domain.inMax(store.level, z, x.max() + y.max() - 1);
  }

  @Override
  public boolean notSatisfied() {
    if (x == z || y == z) {
      return (x == z ? y : x).min() > 0;
    }
    return x.min() + y.min() > z.max();
  }

  @Override
  public boolean satisfied() {
    if (x == z || y == z) {
      return (x == z ? y : x).max() <= 0;
    }
    return x.max() + y.max() <= z.min();
  }

  @Override
  public String toString() {

    return id() + " : XplusYlteqZ(" + x + ", " + y + ", " + z + " )";
  }

  @Override
  public XplusYlteqZ copy(VarMap map) {
    return new XplusYlteqZ(map.get(x), map.get(y), map.get(z));
  }
}
