/*
 * XplusCeqZ.java
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

/**
 * Constraint X + C #= Z.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XplusCeqZ extends AbstractConstraintXandCandZ implements Copyable<XplusCeqZ> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs a constraint x+c=z.
   *
   * @param x variable x.
   * @param c constant c.
   * @param z variable z.
   */
  public XplusCeqZ(IntVar x, int c, IntVar z) {

    super(idNumber, x, c, z);

    checkForOverflow();
  }

  void checkForOverflow() {
    checkSumOverflow(x.min(), x.max(), c, c, z.min(), z.max());
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void consistency(final Store store) {

    if (x == z) {
      // x + c = x holds only for c = 0; the shifts below would not reach a fixpoint, since the
      // constraint is not woken by its own pruning
      if (c != 0) {
        throw Store.failException;
      }
      return;
    }

    // after the two shifts z equals x shifted by c, a fixpoint unless x only keeps its bounds
    x.domain.inShift(store.level, x, z.domain, -c);
    z.domain.inShift(store.level, z, x.domain, c);
    if (x.domain.domainId() == IntDomain.BOUND_DOMAIN_ID) {
      x.domain.inShift(store.level, x, z.domain, -c);
    }
  }

  @Override
  public void notConsistency(final Store store) {

    if (x == z) {
      if (c == 0) {
        throw Store.failException;
      }
      return;
    }

    do {

      store.propagationHasOccurred = false;

      if (x.singleton()) {
        z.domain.inComplement(store.level, z, x.min() + c);
      }

      if (z.singleton()) {
        x.domain.inComplement(store.level, x, z.min() - c);
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean notSatisfied() {
    if (x == z) {
      return c != 0;
    }
    return x.max() + c < z.min() || x.min() + c > z.max();
  }

  @Override
  public boolean satisfied() {
    if (x == z) {
      return c == 0;
    }
    int xMin = x.min();
    int zMin = z.min();
    return x.singleton(xMin) && z.singleton(zMin) && xMin + c == zMin;
  }

  @Override
  public String toString() {

    return id() + " : XplusCeqZ(" + x + ", " + c + ", " + z + " )";
  }

  @Override
  public XplusCeqZ copy(VarMap map) {
    return new XplusCeqZ(map.get(x), c, map.get(z));
  }
}
