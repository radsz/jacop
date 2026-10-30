/*
 * AffineView.java
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

package org.jacop.core;

import java.util.Arrays;

/**
 * An integer variable whose value is a*y + b for an integer variable y, its base. It has no domain
 * of its own: every query reads the base, every pruning prunes the base, and a change of the base
 * wakes the constraints of the view as well as those of the base. Constraints use a view like any
 * other integer variable, so a model with x = a*y + b needs neither x's domain nor a propagator for
 * the equation.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class AffineView extends IntVar {

  // the same as in the domain, which is replaced at each level its constraint lists change
  private final IntVar base;
  private final int a;
  private final int b;

  /**
   * Creates the view a*base + b.
   *
   * @param store the store of the base variable.
   * @param name the name of the view.
   * @param base the base variable, an integer variable that is not a view; a Boolean variable is
   *     not supported.
   * @param a the factor, not 0.
   * @param b the offset.
   * @throws IllegalArgumentException if a is 0, the base is a view or a Boolean variable, or a
   *     value of the view would leave the integer range of domains.
   */
  public AffineView(Store store, String name, IntVar base, int a, int b) {
    super(store, name, checked(base, a, b));
    this.base = base;
    this.a = a;
    this.b = b;
    if (base.views == null) {
      base.views = new AffineView[] {this};
    } else {
      base.views = Arrays.copyOf(base.views, base.views.length + 1);
      base.views[base.views.length - 1] = this;
    }
  }

  private static AffineDomain checked(IntVar base, int a, int b) {
    if (base instanceof AffineView || base instanceof BooleanVar) {
      throw new IllegalArgumentException(
          "The base of an affine view must be an integer variable, not " + base.getClass());
    }
    if (!fits(base.min(), base.max(), a, b)) {
      throw new IllegalArgumentException(
          "The values of " + a + "*" + base.id() + " + " + b + " leave the integer range");
    }
    return new AffineDomain(base, a, b);
  }

  /**
   * Tells whether a*u + b stays within the integer range of domains for every u in min..max.
   *
   * @param min the smallest value of the base.
   * @param max the largest value of the base.
   * @param a the factor.
   * @param b the offset.
   * @return true if the view's values fit.
   */
  public static boolean fits(int min, int max, int a, int b) {
    long x = (long) a * min + b;
    long y = (long) a * max + b;
    return Math.min(x, y) >= IntDomain.MIN_INT && Math.max(x, y) <= IntDomain.MAX_INT;
  }

  /**
   * Returns the base variable.
   *
   * @return the base.
   */
  public IntVar base() {
    return base;
  }

  /**
   * Returns the factor a of a*y + b.
   *
   * @return the factor.
   */
  public int factor() {
    return a;
  }

  /**
   * Returns the offset b of a*y + b.
   *
   * @return the offset.
   */
  public int offset() {
    return b;
  }

  // the bounds are read from the base: the bounds IntVar keeps are refreshed only on events of the
  // variable itself, and a view has none

  @Override
  public int min() {
    return a > 0 ? a * base.min() + b : a * base.max() + b;
  }

  @Override
  public int max() {
    return a > 0 ? a * base.max() + b : a * base.min() + b;
  }

  @Override
  public boolean singleton() {
    return base.singleton();
  }

  @Override
  public boolean singleton(int val) {
    return base.singleton() && a * base.min() + b == val;
  }

  @Override
  public int value() {
    return a * base.value() + b;
  }

  /** Returns the level of the last change of the values, the level of the base. */
  @Override
  public int level() {
    return base().level();
  }

  /** A view cannot be copied on its own; a derivation maps its base and makes a new view. */
  @Override
  public IntVar copyTo(Store target) {
    throw new UnsupportedOperationException(
        "An affine view cannot be copied to another store on its own");
  }

  @Override
  public String toString() {
    return id + " = " + domain;
  }
}
