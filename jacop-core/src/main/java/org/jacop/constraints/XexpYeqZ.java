/*
 * XexpYeqZ.java
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Constraint X ^ Y #= Z.
 *
 * <p>Bounds consistency for every exponent (see {@link DivModPowBounds#pow}); domain consistency
 * for a fixed positive exponent where the power is monotone (odd, or x non-negative), and when x
 * and y have at most {@link #SUPPORT_LIMIT} pairs of values.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XexpYeqZ extends AbstractXopYeqZ implements Copyable<XexpYeqZ>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs constraint X^Y=Z.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XexpYeqZ(IntVar x, IntVar y, IntVar z) {
    super(idNumber, x, y, z);
  }

  /** The most pairs of x and y values whose powers are enumerated for domain consistency. */
  static final int SUPPORT_LIMIT = 64;

  // Outside the domain of every IntVar, so it cannot be mistaken for a negative power.
  private static final int NO_VALUE = Integer.MIN_VALUE;

  private int computeZi(int xi, int yi, IntVar zvar) {
    if (xi == 0) {
      if (yi == 0) {
        return 1;
      }
      if (yi < 0) {
        return NO_VALUE; // 0 to negative exponent is infinity
      }
      return 0;
    }
    // compared as a double first, since a large power does not fit in a long
    double zd = Math.pow(xi, yi);
    if (zd <= zvar.min() - 1.0 || zd >= zvar.max() + 1.0) {
      return NO_VALUE;
    }
    long zl = toLong(zd);
    if (zl < zvar.min() || zl > zvar.max()) {
      return NO_VALUE;
    }
    return long2int(zl);
  }

  private void propagateSupportedValues(IntDomain xdomain, IntDomain ydomain, IntDomain zdomain) {
    for (ValueEnumeration ex = x.domain.valueEnumeration(); ex.hasMoreElements(); ) {
      int xi = ex.nextElement();
      for (ValueEnumeration ey = y.domain.valueEnumeration(); ey.hasMoreElements(); ) {
        int yi = ey.nextElement();
        int zi = computeZi(xi, yi, z);
        if (zi == NO_VALUE) {
          continue;
        }
        if (z.domain.contains(zi)) {
          xdomain.unionAdapt(xi);
          ydomain.unionAdapt(yi);
        }
        zdomain.unionAdapt(zi);
      }
    }
  }

  @Override
  public void consistency(Store store) {

    if (y.singleton() && y.value() > 0 && ((y.value() & 1) == 1 || x.min() >= 0)) {
      monotoneConsistency(store, y.value());
      return;
    }

    do {
      store.propagationHasOccurred = false;
      long[] b = {x.min(), x.max(), y.min(), y.max(), z.min(), z.max()};
      if (!DivModPowBounds.pow(b)) {
        throw Store.failException;
      }
      x.domain.in(store.level, x, (int) b[0], (int) b[1]);
      y.domain.in(store.level, y, (int) b[2], (int) b[3]);
      z.domain.in(store.level, z, (int) b[4], (int) b[5]);
    } while (store.propagationHasOccurred);

    if ((long) x.getSize() * y.getSize() > SUPPORT_LIMIT) {
      return;
    }

    // few pairs: domain consistency by their powers
    do {
      store.propagationHasOccurred = false;

      IntDomain zDom = new IntervalDomain();
      IntDomain xDom = new IntervalDomain();
      IntDomain yDom = new IntervalDomain();
      propagateSupportedValues(xDom, yDom, zDom);

      z.domain.in(store.level, z, zDom);
      x.domain.in(store.level, x, xDom);
      y.domain.in(store.level, y, yDom);

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return BoxExplanation.explain(trail, entry, new IntVar[] {x, y, z}, DivModPowBounds::pow, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return BoxExplanation.explainFailure(trail, new IntVar[] {x, y, z}, DivModPowBounds::pow, out);
  }

  /**
   * Domain consistency for a fixed exponent n &gt; 0 where x^n is strictly increasing on the domain
   * of x (n odd, or x non-negative). The bounds are narrowed first, which is all most calls need,
   * then one ordered pass over x keeps the values whose power is in z and, when z has other values,
   * sets z to those powers. Unlike the general case, nothing is allocated when no value is removed.
   */
  private void monotoneConsistency(Store store, int n) {

    do {
      store.propagationHasOccurred = false;

      // x^n is increasing, so the bounds of z follow from those of x
      z.domain.in(
          store.level,
          z,
          long2int(DivModPowBounds.power(x.min(), n)),
          long2int(DivModPowBounds.power(x.max(), n)));

      // the smallest r with r^n >= z.min() and the largest r with r^n <= z.max(); there is none
      // when z holds no n-th power
      long xMin = DivModPowBounds.floorRoot(z.min() - 1L, n) + 1;
      long xMax = DivModPowBounds.floorRoot(z.max(), n);
      if (xMin > xMax) {
        throw Store.failException;
      }
      x.domain.in(store.level, x, long2int(xMin), long2int(xMax));

    } while (store.propagationHasOccurred);

    if (x.singleton()) {
      return; // z is the singleton x^n
    }

    // after the bounds step x.min()^n == z.min() and x.max()^n == z.max(), and every power of a
    // value of x lies within the int range of z
    IntDomain xd = x.domain;
    IntDomain zd = z.domain;
    int xMax = xd.max();
    IntervalDomain xDom = null;
    int supported = 0;
    for (int v = xd.min(); ; v = xd.nextValue(v)) {
      if (zd.contains((int) DivModPowBounds.power(v, n))) {
        supported++;
        if (xDom != null) {
          xDom.unionAdapt(v, v);
        }
      } else if (xDom == null) {
        // first unsupported value: copy the supported values below it
        xDom = new IntervalDomain();
        for (int u = xd.min(); u < v; u = xd.nextValue(u)) {
          xDom.unionAdapt(u, u);
        }
      }
      if (v == xMax) {
        break;
      }
    }

    if (xDom != null) {
      if (xDom.isEmpty()) {
        throw Store.failException;
      }
      x.domain.in(store.level, x, xDom);
    }

    if (z.domain.domainId() != IntDomain.BOUND_DOMAIN_ID && z.getSize() != supported) {
      // z has values that are not powers of x; the supported powers are all in z
      IntervalDomain zDom = new IntervalDomain(supported + 1);
      for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
        int p = (int) DivModPowBounds.power(e.nextElement(), n);
        zDom.unionAdapt(p, p);
      }
      z.domain.in(store.level, z, zDom);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    // consistency keeps only supported values, so it uses the holes of the domains
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {

    return grounded() && computeZi(x.min(), y.min(), z) == z.min();
  }

  @Override
  public String toString() {

    return id() + " : XexpYeqZ(" + x + ", " + y + ", " + z + " )";
  }

  @Override
  public XexpYeqZ copy(VarMap map) {
    return new XexpYeqZ(map.get(x), map.get(y), map.get(z));
  }
}
