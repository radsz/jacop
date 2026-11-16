/*
 * XmulYeqZSaturated.java
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
import org.jacop.core.Interval;
import org.jacop.core.Store;

/**
 * Constraint Z = max(MIN_INT, min(MAX_INT, X * Y)): the product of X and Y saturated at the ends of
 * JaCoP's integer range ({@link IntDomain#MIN_INT}, {@link IntDomain#MAX_INT}).
 *
 * <p>It stands for {@code z = x * y} when the declared domain of z reaches beyond JaCoP's range and
 * z is only compared with values strictly inside it: an end of the range then represents every
 * product at or beyond it, and the comparisons have the same truth value for both. Unlike {@link
 * XmulYeqZ} over the narrowed z, it removes no pair of factors whose product does not fit.
 *
 * <p>Bounds of z follow from the bounds of x and y, computed in 64-bit arithmetic. The bounds of x
 * and y follow from z only while z is away from both ends of the range, where it is the product
 * itself. Once x, y and z are fixed the bounds of z decide the constraint, so the pruning is sound
 * and complete on solutions.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class XmulYeqZSaturated extends AbstractXopYeqZ implements Copyable<XmulYeqZSaturated> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs a constraint Z = X * Y saturated at the ends of JaCoP's integer range.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XmulYeqZSaturated(IntVar x, IntVar y, IntVar z) {
    super(idNumber, x, y, z);
    this.queueIndex = 1;
  }

  /**
   * The product of two values saturated at the ends of JaCoP's integer range.
   *
   * @param a the first value
   * @param b the second value
   * @return max(MIN_INT, min(MAX_INT, a * b))
   */
  public static int saturatedProduct(int a, int b) {
    return (int) Math.clamp((long) a * b, IntDomain.MIN_INT, IntDomain.MAX_INT);
  }

  @Override
  public void consistency(Store store) {
    do {
      store.propagationHasOccurred = false;

      long min;
      long max;
      if (x == y) {
        long a = (long) x.min() * x.min();
        long b = (long) x.max() * x.max();
        min = x.min() <= 0 && x.max() >= 0 ? 0 : Math.min(a, b);
        max = Math.max(a, b);
      } else {
        long ac = (long) x.min() * y.min();
        long ad = (long) x.min() * y.max();
        long bc = (long) x.max() * y.min();
        long bd = (long) x.max() * y.max();
        min = Math.min(Math.min(ac, ad), Math.min(bc, bd));
        max = Math.max(Math.max(ac, ad), Math.max(bc, bd));
      }
      z.domain.in(
          store.level,
          z,
          (int) Math.clamp(min, IntDomain.MIN_INT, IntDomain.MAX_INT),
          (int) Math.clamp(max, IntDomain.MIN_INT, IntDomain.MAX_INT));

      // away from the ends of the range z is the product itself
      if (x != y && z.min() > IntDomain.MIN_INT && z.max() < IntDomain.MAX_INT) {
        Interval xBounds = factorBounds(y);
        if (xBounds != null) {
          x.domain.in(store.level, x, xBounds.min(), xBounds.max());
        }
        Interval yBounds = factorBounds(x);
        if (yBounds != null) {
          y.domain.in(store.level, y, yBounds.min(), yBounds.max());
        }
      }
    } while (store.propagationHasOccurred);
  }

  // bounds of the factor whose partner is other, or null when the quotient gives none
  private Interval factorBounds(IntVar other) {
    if (other.min() >= 0 || other.max() <= 0 || (z.min() <= 0 && z.max() >= 0)) {
      return IntDomain.divIntBounds(z.min(), z.max(), other.min(), other.max());
    }
    return null;
  }

  @Override
  public boolean satisfied() {
    return grounded() && saturatedProduct(x.value(), y.value()) == z.value();
  }

  @Override
  public XmulYeqZSaturated copy(VarMap map) {
    return new XmulYeqZSaturated(map.get(x), map.get(y), map.get(z));
  }

  @Override
  public String toString() {
    return id() + " : XmulYeqZSaturated(" + x + ", " + y + ", " + z + " )";
  }
}
