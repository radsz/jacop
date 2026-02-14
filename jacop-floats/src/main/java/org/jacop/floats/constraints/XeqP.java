/*
 * XeqP.java
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;

/**
 * Constraints X #= P for X and P floats.
 *
 * <p>Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XeqP extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a left hand variable in equality constraint. */
  private final IntVar x;

  /** It specifies a right hand variable in equality constraint. */
  private final FloatVar p;

  /**
   * It constructs constraint X = P.
   *
   * @param x variable x.
   * @param p variable p.
   */
  public XeqP(IntVar x, FloatVar p) {

    checkInputForNullness(new String[] {"x", "q"}, new Object[] {x, p});

    numberId = idNumber.incrementAndGet();

    this.x = x;
    this.p = p;

    setScope(x, p);
  }

  @Override
  public void consistency(Store store) {

    do {

      // domain consistency
      int xMin;
      if (Math.abs(p.min()) < (double) IntDomain.MAX_INT) {
        xMin = (int) (Math.round(Math.ceil(p.min())));
      } else {
        xMin = IntDomain.MIN_INT;
      }

      int xMax;
      if (Math.abs(p.max()) < (double) IntDomain.MAX_INT) {
        xMax = (int) (Math.round(Math.floor(p.max())));
      } else {
        xMax = IntDomain.MAX_INT;
      }

      if (xMin > xMax) {
        int t = xMax;
        xMax = xMin;
        xMin = t;
      }

      x.domain.in(store.level, x, xMin, xMax);

      store.propagationHasOccurred = false;

      p.domain.in(store.level, p, x.min(), x.max());

    } while (store.propagationHasOccurred);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    return grounded() && x.min() <= p.max() && x.max() >= p.min();
  }

  @Override
  public String toString() {
    return id() + " : XeqP(" + x + ", " + p + " )";
  }
}
