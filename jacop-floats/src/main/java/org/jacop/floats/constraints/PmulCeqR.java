/*
 * PmulCeqR.java
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
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Constraint P * C = R for floats.
 *
 * <p>Boundary consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class PmulCeqR extends Constraint
    implements SatisfiedPresent, FloatDerivableConstraint, Copyable<PmulCeqR> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable p in constraint p * c = r. */
  public final FloatVar p;

  /** It specifies constants c in constraint p * c = r. */
  public final double c;

  /** It specifies variable r in constraint p * c = r. */
  public final FloatVar r;

  /**
   * It constructs a constraint P * C = R.
   *
   * @param p variable p.
   * @param c constnat c.
   * @param r variable r.
   */
  public PmulCeqR(FloatVar p, double c, FloatVar r) {

    checkInputForNullness(new String[] {"p", "r"}, new Object[] {p, r});
    checkFinite(getClass().getSimpleName(), c);

    numberId = idNumber.incrementAndGet();

    this.p = p;
    this.c = c;
    this.r = r;

    setScope(p, r);
  }

  /**
   * Checks that a constant of a float constraint is finite.
   *
   * @param constraint the name of the constraint.
   * @param c the constant.
   * @throws IllegalArgumentException if c is NaN or infinite.
   */
  static void checkFinite(String constraint, double c) {
    if (!Double.isFinite(c)) {
      throw new IllegalArgumentException(
          "Constraint " + constraint + " has constant c " + c + " that is not finite.");
    }
  }

  @Override
  public void consistency(Store store) {
    if (p == r) {
      consistencySameVariable(store);
      return;
    }
    // p * c = r: each projection is computed again only when the bounds of the other variable
    // changed since it was last computed; with unchanged inputs it narrows nothing, so the fixpoint
    // is the one of recomputing both until a round changes nothing
    boolean pStale = true;
    boolean rStale = true;
    do {
      if (pStale) {
        pStale = false;
        double min = p.min();
        double max = p.max();
        p.domain.in(store.level, p, FloatDomain.divBounds(r.min(), r.max(), c, c));
        if (min != p.min() || max != p.max()) {
          rStale = true;
        }
      }
      if (rStale) {
        rStale = false;
        double min = r.min();
        double max = r.max();
        r.domain.in(store.level, r, FloatDomain.mulBounds(p.min(), p.max(), c, c));
        if (min != r.min() || max != r.max()) {
          pStale = true;
        }
      }
    } while (pStale || rStale);
    store.propagationHasOccurred = false;
  }

  // p * c = p: a change of one side is a change of the other
  private void consistencySameVariable(Store store) {
    do {
      store.propagationHasOccurred = false;

      FloatIntervalDomain pBounds = FloatDomain.divBounds(r.min(), r.max(), c, c);
      p.domain.in(store.level, p, pBounds);

      FloatIntervalDomain rBounds = FloatDomain.mulBounds(p.min(), p.max(), c, c);
      r.domain.in(store.level, r, rBounds);

    } while (store.propagationHasOccurred);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    FloatDomain pDom = p.dom();
    FloatDomain rDom = r.dom();
    return grounded() && rDom.eq(FloatDomain.mulBounds(pDom.min(), pDom.max(), c, c));
  }

  @Override
  public String toString() {
    return id() + " : PmulCeqR(" + p + ", " + c + ", " + r + " )";
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
      // f = c * p
      // f' = c * d(p)
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(
          new PmulCeqR(Derivative.getDerivative(store, p, vars, x), c, v));
      return v;
    } else if (f.equals(p)) {
      // f = 1/c * r
      // f' = 1/c * d(r)
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(
          new PmulCeqR(Derivative.getDerivative(store, r, vars, x), 1 / c, v));
      return v;
    }

    return null;
  }

  @Override
  public PmulCeqR copy(VarMap map) {
    return new PmulCeqR(map.get(p), c, map.get(r));
  }
}
