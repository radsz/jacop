/*
 * XmulYeqC.java
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

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * Constraint X * Y #= C.
 *
 * <p>Boundary consistency is used.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class XmulYeqC extends AbstractConstraintXandY implements Copyable<XmulYeqC> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies constant c in constraint x * y = c. */
  private final int c;

  /** It specifies if the constraint is actually, x^2 = c. */
  private final boolean xSquare;

  // the positive divisors of |c|, found at the first propagation with c != 0
  private int[] divisors;

  /**
   * It constructs constraint X * Y = C.
   *
   * @param x variable x.
   * @param y variable y.
   * @param c constant c.
   */
  public XmulYeqC(IntVar x, IntVar y, int c) {

    super(idNumber, x, y);

    xSquare = x == y;

    this.c = c;
  }

  @Override
  public void consistency(final Store store) {
    if (xSquare) {
      propagateXsquareEqC(store);
    } else {
      propagateXmulYeqC(store);
    }
  }

  private void propagateXsquareEqC(Store store) {
    do {
      store.propagationHasOccurred = false;

      if (c < 0) {
        throw Store.failException;
      }

      double sqrtOfC = Math.sqrt(c);

      if (Math.ceil(sqrtOfC) != Math.floor(sqrtOfC)) {
        throw Store.failException;
      }

      int value = (int) sqrtOfC;

      IntDomain dom = new IntervalDomain(-value, -value);
      dom.unionAdapt(value, value);

      x.domain.in(store.level, x, dom);

    } while (store.propagationHasOccurred);
  }

  private void propagateXmulYeqC(Store store) {
    if (c != 0) {
      propagateNonZeroProduct(store);
      return;
    }
    // x * y = 0: a factor without 0 leaves 0 to the other one
    if (!x.domain.contains(0)) {
      y.domain.in(store.level, y, 0, 0);
    } else if (!y.domain.contains(0)) {
      x.domain.in(store.level, x, 0, 0);
    }
  }

  /**
   * With c != 0 both factors are divisors of c, so the constraint keeps the values v of x that
   * divide c with c / v in the domain of y, and their quotients in y (domain consistency). The
   * divisors of |c| are found once, in O(sqrt |c|).
   */
  private void propagateNonZeroProduct(Store store) {
    int[] d = divisors();
    int[] xs = new int[2 * d.length];
    int count = 0;
    // the negative divisors in increasing order, then the positive ones
    for (int k = d.length - 1; k >= 0; k--) {
      count = keepFactor(-d[k], xs, count);
    }
    for (int value : d) {
      count = keepFactor(value, xs, count);
    }
    if (count == 0) {
      throw Store.failException;
    }
    IntervalDomain xDom = new IntervalDomain(count);
    int[] ys = new int[count];
    for (int k = 0; k < count; k++) {
      xDom.unionAdapt(xs[k], xs[k]);
      ys[k] = (int) (c / (long) xs[k]);
    }
    Arrays.sort(ys);
    IntervalDomain yDom = new IntervalDomain(count);
    for (int value : ys) {
      yDom.unionAdapt(value, value);
    }
    x.domain.in(store.level, x, xDom);
    y.domain.in(store.level, y, yDom);
  }

  private int keepFactor(int v, int[] xs, int count) {
    long other = c / (long) v;
    if (x.domain.contains(v)
        && other >= Integer.MIN_VALUE
        && other <= Integer.MAX_VALUE
        && y.domain.contains((int) other)) {
      xs[count] = v;
      return count + 1;
    }
    return count;
  }

  // the positive divisors of |c| in increasing order
  private int[] divisors() {
    if (divisors == null) {
      long abs = Math.abs((long) c);
      int[] small = new int[64];
      int[] large = new int[64];
      int ns = 0;
      int nl = 0;
      for (long k = 1; k * k <= abs; k++) {
        if (abs % k == 0) {
          if (ns == small.length) {
            small = Arrays.copyOf(small, 2 * ns);
            large = Arrays.copyOf(large, 2 * ns);
          }
          small[ns++] = (int) k;
          if (k * k != abs && abs / k <= Integer.MAX_VALUE) {
            large[nl++] = (int) (abs / k);
          }
        }
      }
      int[] all = new int[ns + nl];
      System.arraycopy(small, 0, all, 0, ns);
      for (int k = 0; k < nl; k++) {
        all[ns + k] = large[nl - 1 - k];
      }
      divisors = all;
    }
    return divisors;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    // notSatisfied() looks at the holes of the domains once a factor is fixed
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void notConsistency(final Store store) {

    do {

      store.propagationHasOccurred = false;

      if (x.singleton(0) || y.singleton(0)) {
        // the product is 0 whatever the other variable is
        if (c == 0) {
          throw Store.failException;
        }
      } else if (x.singleton() && c % x.value() == 0) {
        y.domain.inComplement(store.level, y, c / x.value());
      } else if (y.singleton() && c % y.value() == 0) {
        x.domain.inComplement(store.level, x, c / y.value());
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean notSatisfied() {
    if (xSquare && c < 0) {
      return true;
    }
    Interval r = IntDomain.mulBounds(x.min(), x.max(), y.min(), y.max());
    if (c < r.min() || c > r.max()) {
      return true;
    }
    // a fixed factor leaves one value for the other one
    if (x.singleton()) {
      return missingFactor(x.value(), y);
    }
    if (y.singleton()) {
      return missingFactor(y.value(), x);
    }
    return false;
  }

  private boolean missingFactor(int a, IntVar other) {
    return a == 0 ? c != 0 : c % a != 0 || !other.domain.contains(c / a);
  }

  @Override
  public boolean satisfied() {
    return grounded() && (long) x.min() * y.min() == c;
  }

  @Override
  public String toString() {

    return id() + " : XmulYeqC(" + x + ", " + y + ", " + c + " )";
  }

  @Override
  public XmulYeqC copy(VarMap map) {
    return new XmulYeqC(map.get(x), map.get(y), c);
  }
}
