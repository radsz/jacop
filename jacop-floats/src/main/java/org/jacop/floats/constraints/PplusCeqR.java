/*
 * PplusCeqR.java
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

import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Constraint P + C #= R.
 *
 * <p>Bound consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class PplusCeqR extends PrimitiveConstraint implements FloatDerivableConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable p in constraint p+c=r. */
  public final FloatVar p;

  /** It specifies constant c in constraint p+c=r. */
  public final double c;

  /** It specifies variable r in constraint p+c=r. */
  public final FloatVar r;

  /**
   * It constructs constraint P+C=R.
   *
   * @param p variable p.
   * @param c constant c.
   * @param r variable r.
   */
  public PplusCeqR(FloatVar p, double c, FloatVar r) {

    checkInputForNullness(new String[] {"p", "r"}, new Object[] {p, r});

    numberId = idNumber.incrementAndGet();

    this.p = p;
    this.c = c;
    this.r = r;

    setScope(p, r);
  }

  @Override
  public void consistency(Store store) {

    do {
      store.propagationHasOccurred = false;

      FloatIntervalDomain pDom = FloatDomain.subBounds(r.min(), r.max(), c, c);
      p.domain.in(store.level, p, pDom.min(), pDom.max());

      FloatIntervalDomain rDom = FloatDomain.addBounds(p.min(), p.max(), c, c);
      r.domain.in(store.level, r, rDom.min(), rDom.max());

    } while (store.propagationHasOccurred);
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void notConsistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      if (r.singleton()) {
        p.domain.inComplement(store.level, p, r.min() - c);
      }

      if (p.singleton()) {
        r.domain.inComplement(store.level, r, p.min() + c);
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean notSatisfied() {
    FloatDomain pDom = p.dom();
    FloatDomain rDom = r.dom();
    return pDom.max() + c < rDom.min() || pDom.min() + c > rDom.max();
  }

  @Override
  public boolean satisfied() {

    return p.singleton()
        && r.singleton()
        && r.value() - p.value() - c < FloatDomain.epsilon(r.value() - p.value() - c);
  }

  @Override
  public String toString() {

    return id() + " : PplusCeqR(" + p + ", " + c + ", " + r + " )";
  }

  /**
   * Computes the derivative of this constraint with respect to a variable.
   *
   * @param store the constraint store
   * @param f the function variable for which to compute the derivative
   * @param vars the set of variables involved in the derivative computation
   * @param x the variable with respect to which the derivative is computed
   * @return the derivative variable, or null if f is not part of this constraint
   */
  public FloatVar derivative(Store store, FloatVar f, Set<FloatVar> vars, FloatVar x) {
    if (f.equals(r)) {
      // f = p + c
      // f' = d(p)
      return Derivative.getDerivative(store, p, vars, x);

    } else if (f.equals(p)) {
      // f = r - c
      // f' = d(r)
      return Derivative.getDerivative(store, r, vars, x);
    }

    return null;
  }
}
