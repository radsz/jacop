/*
 * XmulYeqZ.java
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

import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import org.jacop.api.Copyable;
import org.jacop.api.Functional;
import org.jacop.api.Simplifiable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Constraint X * Y #= Z.
 *
 * <p>Boundary consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XmulYeqZ extends AbstractXopYeqZ
    implements Functional, Violation, Simplifiable, Copyable<XmulYeqZ>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private final boolean xSquare;

  private final XeqY xEqz;
  private final XeqY yEqz;

  /**
   * It constructs a constraint X * Y = Z.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XmulYeqZ(IntVar x, IntVar y, IntVar z) {

    super(idNumber, x, y, z);

    xSquare = x == y;

    this.queueIndex = 1;

    xEqz = new XeqY(x, z);
    yEqz = new XeqY(y, z);
  }

  @Override
  public void consistency(Store store) {

    if (xSquare) {
      propagateXsquareBounds(store);
    } else {
      propagateMulBounds(store);
    }

    if (x.singleton(0) || y.singleton(0)) {
      removeConstraint();
    }
  }

  private void propagateXsquareBounds(Store store) {
    do {
      // Bounds for Z
      Interval zBounds = IntDomain.squareBounds(x.min(), x.max());
      z.domain.in(store.level, z, zBounds.min(), zBounds.max());

      store.propagationHasOccurred = false;

      // Bounds for X
      int xMin = toInt(Math.round(Math.ceil(Math.sqrt(z.min()))));
      int xMax = toInt(Math.round(Math.floor(Math.sqrt(z.max()))));

      if (xMin > xMax) {
        throw Store.failException;
      }

      if (x.min() < 0) {
        IntDomain dom = new IntervalDomain(-xMax, -xMin);
        dom.unionAdapt(xMin, xMax);
        x.domain.in(store.level, x, dom);
      } else {
        x.domain.in(store.level, x, xMin, xMax);
      }

    } while (store.propagationHasOccurred);
  }

  private void propagateMulBounds(Store store) {
    if (propagateUnitFactor(store)) {
      return;
    }

    do {
      this.queueIndex = 1;

      // Bounds for Z
      Interval zBounds = IntDomain.mulBounds(x.min(), x.max(), y.min(), y.max());
      z.domain.in(store.level, z, zBounds.min(), zBounds.max());

      store.propagationHasOccurred = false;

      // Bounds for X
      Interval xBounds = factorBounds(x, y);
      x.domain.in(store.level, x, xBounds.min(), xBounds.max());

      // Bounds for Y
      Interval yBounds = factorBounds(y, x);
      y.domain.in(store.level, y, yBounds.min(), yBounds.max());

    } while (store.propagationHasOccurred);

    // the bounds can fix x or y to 1, and the constraint is not woken again by its own pruning
    propagateUnitFactor(store);
  }

  /** Makes z equal to the other factor once x or y is 1, and tells whether one of them is. */
  private boolean propagateUnitFactor(Store store) {
    if (x.singleton(1)) {
      this.queueIndex = 0;
      yEqz.consistency(store);
      return true;
    }
    if (y.singleton(1)) {
      this.queueIndex = 0;
      xEqz.consistency(store);
      return true;
    }
    return false;
  }

  /**
   * Bounds of factor v in v * other = z. When the interval of other contains 0 but z does not, the
   * quotient z / other is taken separately over the negative and the positive part of other, each
   * cut to the bounds of v, so that v is still pruned.
   */
  private Interval factorBounds(IntVar v, IntVar other) {
    if (other.min() >= 0 || other.max() <= 0 || (z.min() <= 0 && z.max() >= 0)) {
      return IntDomain.divIntBounds(z.min(), z.max(), other.min(), other.max());
    }
    Interval negative = quotientWithin(v, other.min(), -1);
    Interval positive = quotientWithin(v, 1, other.max());
    if (negative == null && positive == null) {
      throw Store.failException;
    }
    if (negative == null || positive == null) {
      return negative == null ? positive : negative;
    }
    return new Interval(
        Math.min(negative.min(), positive.min()), Math.max(negative.max(), positive.max()));
  }

  /** The values of z / [c, d] within the bounds of v, or null if there are none. */
  private Interval quotientWithin(IntVar v, int c, int d) {
    int min;
    int max;
    try {
      Interval q = IntDomain.divIntBounds(z.min(), z.max(), c, d);
      min = Math.max(q.min(), v.min());
      max = Math.min(q.max(), v.max());
    } catch (FailException e) {
      return null;
    }
    return min <= max ? new Interval(min, max) : null;
  }

  // Once x or y is 1, consistency() makes z and the other variable equal, so a value removed inside
  // a domain must wake the constraint as well.
  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    return grounded() && x.min() * y.min() == z.min();
  }

  @Override
  public String toString() {

    return id() + " : XmulYeqZ(" + x + ", " + y + ", " + z + " )";
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == XmulYeqZ.class
        && new MulExplanation(trail, x, y, z, entry).explain(entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == XmulYeqZ.class
        && new MulExplanation(trail, x, y, z, trail.size()).explainFailure(out);
  }

  /** With a fixed factor the product becomes {@code XmulCeqZ}, or holds when it is zero. */
  @Override
  public Optional<List<Constraint>> simplify() {
    if (getClass() != XmulYeqZ.class || x == y || !(x.singleton() || y.singleton())) {
      return Optional.empty();
    }
    IntVar other = x.singleton() ? y : x;
    if (other == z) {
      return Optional.empty();
    }
    int c = x.singleton() ? x.value() : y.value();
    if (c == 0) {
      return z.singleton(0) ? Optional.of(List.of()) : Optional.empty();
    }
    return Optional.of(List.of(c == 1 ? new XeqY(other, z) : new XmulCeqZ(other, c, z)));
  }

  @Override
  public XmulYeqZ copy(VarMap map) {
    return new XmulYeqZ(map.get(x), map.get(y), map.get(z));
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    long xy = (long) value.applyAsInt(x) * value.applyAsInt(y);
    return Math.min(Integer.MAX_VALUE, Math.abs(xy - value.applyAsInt(z)));
  }

  @Override
  public IntVar functionalResult() {
    return z;
  }

  @Override
  public int functionalValue(ToIntFunction<IntVar> value) {
    long xy = (long) value.applyAsInt(x) * value.applyAsInt(y);
    return (int) Math.max(Integer.MIN_VALUE, Math.min(Integer.MAX_VALUE, xy));
  }
}
