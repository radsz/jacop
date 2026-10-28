/*
 * AsinPeqR.java
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

import org.jacop.api.VarMap;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Constraints asin(P) = R.
 *
 * <p>Bounds consistency can be used; third parameter of constructor controls this.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AsinPeqR extends SinPeqR {

  /**
   * It constructs sin(P) = Q constraints.
   *
   * @param p variable P
   * @param q variable Q
   */
  public AsinPeqR(FloatVar p, FloatVar q) {
    super(q, p);
  }

  /**
   * Propagates R = asin(P) on the principal branch: R is restricted to -PI/2..PI/2, where sin is
   * increasing, so both directions are bounds of monotone functions (sin(R) = P alone also accepted
   * R = PI - asin(P) + 2kPI).
   */
  @Override
  protected void boundConsistency(Store store) {
    do {
      store.propagationHasOccurred = false;

      if (satisfied()) {
        return;
      }

      p.domain.in(
          store.level,
          p,
          FloatDomain.down(Math.asin(Math.max(q.min(), -1.0))),
          FloatDomain.up(Math.asin(Math.min(q.max(), 1.0))));
      q.domain.in(
          store.level, q, FloatDomain.down(Math.sin(p.min())), FloatDomain.up(Math.sin(p.max())));
      // with p and q the same variable, asin(x) = x shrinks the bounds towards 0 by about x^3 per
      // pass, so the loop would not reach a fixpoint in any reasonable time; search splits instead
    } while (store.propagationHasOccurred && p != q);

    // the store does not run the constraint again for its own pruning, so check a value it left
    if (p == q && p.singleton() && !satisfied()) {
      throw Store.failException;
    }
  }

  @Override
  public boolean satisfied() {
    // also compare in the direction of asin, which is well conditioned where the forward
    // function is not (tan near its poles, sin and cos near their extrema)
    return (super.satisfied() || satisfiedWithTrigFunctionStatic(q, p, Math::asin))
        && p.min() >= FloatDomain.down(-FloatDomain.PI / 2)
        && p.max() <= FloatDomain.up(FloatDomain.PI / 2);
  }

  @Override
  public String toString() {

    return id() + " : AsinPeqR(" + q + ", " + p + " )";
  }

  @Override
  public AsinPeqR copy(VarMap map) {
    return new AsinPeqR(map.get(q), map.get(p));
  }
}
