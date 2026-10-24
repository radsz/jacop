/*
 * CeilPeqX.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;

/**
 * Constraints ceil(P) #= X for integer variable X and float variable P.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CeilPeqX extends AbstractRoundPeqX {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs constraint X = P.
   *
   * @param x variable x.
   * @param p variable p.
   */
  public CeilPeqX(FloatVar p, IntVar x) {
    super(idNumber, p, x);
  }

  @Override
  public void consistency(Store store) {

    do {
      // ceil(p) = x, n - 1 < x <= n
      p.domain.in(store.level, p, Math.nextUp((double) x.min() - 1), x.max());

      store.propagationHasOccurred = false;

      x.domain.in(store.level, x, (int) Math.ceil(p.min()), (int) Math.ceil(p.max()));
    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean satisfied() {
    return x.singleton() && p.min() > x.value() - 1.0 && p.max() <= x.value();
  }

  @Override
  public String toString() {
    return id() + " : CeilPeqX(" + p + ", " + x + " )";
  }
}
