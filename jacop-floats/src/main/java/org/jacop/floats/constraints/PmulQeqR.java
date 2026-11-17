/*
 * PmulQeqR.java
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
 * Constraint P * Q = R for floats.
 *
 * <p>Boundary consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class PmulQeqR extends Constraint
    implements SatisfiedPresent, FloatDerivableConstraint, Copyable<PmulQeqR> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable p in constraint p * q = r. */
  public final FloatVar p;

  /** It specifies variable q in constraint p * q = r. */
  public final FloatVar q;

  /** It specifies variable r in constraint p * q = r. */
  public final FloatVar r;

  final boolean xSquare;

  /**
   * It constructs a constraint P * Q = R.
   *
   * @param p variable p.
   * @param q variable q.
   * @param r variable r.
   */
  public PmulQeqR(FloatVar p, FloatVar q, FloatVar r) {

    checkInputForNullness(new String[] {"p", "q", "r"}, new Object[] {p, q, r});

    numberId = idNumber.incrementAndGet();

    xSquare = p == q;

    this.p = p;
    this.q = q;
    this.r = r;

    setScope(p, q, r);
  }

  @Override
  public void consistency(Store store) {

    // p * q = p holds when p = 0 or q = 1 (and symmetrically for q * p = q)
    if (p.equals(r)) {
      consistencyFactorIsOne(store, p, q);
      return;
    }
    if (q.equals(r)) {
      consistencyFactorIsOne(store, q, p);
      return;
    }

    if (xSquare) {
      consistencySquare(store);
    } else {
      consistencyProduct(store);
    }
  }

  /**
   * Propagates x * y = x, which holds exactly when x = 0 or y = 1.
   *
   * @param store the constraint store
   * @param x the variable that is both a factor and the product
   * @param y the other factor
   */
  private static void consistencyFactorIsOne(Store store, FloatVar x, FloatVar y) {
    if (!x.domain.contains(0.0)) {
      y.domain.in(store.level, y, 1.0, 1.0);
    }
    if (!y.domain.contains(1.0)) {
      x.domain.in(store.level, x, 0.0, 0.0);
    }
  }

  // r = p * p: each projection is computed again only when the other variable's bounds changed
  private void consistencySquare(Store store) {
    boolean rStale = true;
    boolean pStale = true;
    do {
      if (r.max() < 0) {
        throw Store.failException;
      }

      if (rStale) {
        rStale = false;
        double rMin = r.min();
        double rMax = r.max();
        double min = computeSquareRangeMinimum();
        double max = computeSquareRangeMaximum();
        r.domain.in(store.level, r, min, max);
        if (rMin != r.min() || rMax != r.max()) {
          pStale = true;
        }
      }

      if (pStale) {
        pStale = false;
        // |p| in [sqrt(r.min), sqrt(r.max)], rounded outward
        double pMin = r.min() <= 0.0 ? 0.0 : FloatDomain.sqrtDown(r.min());
        if (r.max() < 0.0) {
          throw Store.failException;
        }
        double pMax = FloatDomain.sqrtUp(r.max());

        if (pMin > pMax) {
          throw Store.failException;
        }

        double oldMin = p.min();
        double oldMax = p.max();
        FloatDomain dom = new FloatIntervalDomain(-pMax, -pMin);
        dom.unionAdapt(pMin, pMax);
        p.domain.in(store.level, p, dom);
        if (oldMin != p.min() || oldMax != p.max()) {
          rStale = true;
        }
      }
    } while (rStale || pStale);
    store.propagationHasOccurred = false;
  }

  private double computeSquareRangeMinimum() {
    if (p.min() <= 0.0 && p.max() >= 0.0) {
      return 0.0;
    }
    return Math.min(FloatDomain.mulDown(p.min(), p.min()), FloatDomain.mulDown(p.max(), p.max()));
  }

  private double computeSquareRangeMaximum() {
    return Math.max(FloatDomain.mulUp(p.min(), p.min()), FloatDomain.mulUp(p.max(), p.max()));
  }

  // p, q and r are distinct here. A projection is computed again only when the bounds of one of
  // its two inputs changed since it was last computed: with unchanged inputs it gives the same
  // bounds and narrows nothing, so the result is the same fixpoint as recomputing all three until
  // a round changes nothing.
  private void consistencyProduct(Store store) {
    boolean pStale = true;
    boolean qStale = true;
    boolean rStale = true;
    do {
      if (pStale) {
        pStale = false;
        double min = p.min();
        double max = p.max();
        p.domain.in(store.level, p, FloatDomain.divBounds(r.min(), r.max(), q.min(), q.max()));
        if (min != p.min() || max != p.max()) {
          qStale = true;
          rStale = true;
        }
      }
      if (qStale) {
        qStale = false;
        double min = q.min();
        double max = q.max();
        q.domain.in(store.level, q, FloatDomain.divBounds(r.min(), r.max(), p.min(), p.max()));
        if (min != q.min() || max != q.max()) {
          pStale = true;
          rStale = true;
        }
      }
      if (rStale) {
        rStale = false;
        double min = r.min();
        double max = r.max();
        r.domain.in(store.level, r, FloatDomain.mulBounds(p.min(), p.max(), q.min(), q.max()));
        if (min != r.min() || max != r.max()) {
          pStale = true;
          qStale = true;
        }
      }
    } while (pStale || qStale || rStale);
    store.propagationHasOccurred = false;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    FloatDomain pDom = p.dom();
    FloatDomain qDom = q.dom();
    FloatDomain rDom = r.dom();
    return grounded()
        && rDom.eq(FloatDomain.mulBounds(pDom.min(), pDom.max(), qDom.min(), qDom.max()));
  }

  @Override
  public String toString() {
    return id() + " : PmulQeqR(" + p + ", " + q + ", " + r + " )";
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
      // f = p * q
      // f' = p*d(q) + d(p)*q
      FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(Derivative.getDerivative(store, p, vars, x), q, v1));
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(Derivative.getDerivative(store, q, vars, x), p, v2));
      Derivative.poseDerivativeConstraint(new PplusQeqR(v1, v2, v));
      return v;

    } else if (f.equals(p)) {
      // f = r / q
      // f' = (d(r) - (r/q)*d(q))/q
      FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v3 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(new PdivQeqR(r, q, v1));
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(v1, Derivative.getDerivative(store, q, vars, x), v2));
      Derivative.poseDerivativeConstraint(
          new PminusQeqR(Derivative.getDerivative(store, r, vars, x), v2, v3));
      Derivative.poseDerivativeConstraint(new PdivQeqR(v3, q, v));
      return v;
    } else if (f.equals(q)) {
      // f = r / p
      // f' = (d(r) - (r/p)*d(p))/p
      FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v3 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
      Derivative.poseDerivativeConstraint(new PdivQeqR(r, p, v1));
      Derivative.poseDerivativeConstraint(
          new PmulQeqR(v1, Derivative.getDerivative(store, p, vars, x), v2));
      Derivative.poseDerivativeConstraint(
          new PminusQeqR(Derivative.getDerivative(store, r, vars, x), v2, v3));
      Derivative.poseDerivativeConstraint(new PdivQeqR(v3, p, v));
      return v;
    }

    return null;
  }

  @Override
  public PmulQeqR copy(VarMap map) {
    return new PmulQeqR(map.get(p), map.get(q), map.get(r));
  }
}
