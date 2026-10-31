/*
 * XmodYeqZ.java
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
 * Constraint X mod Y = Z, with the remainder of the division rounding towards zero (it has the sign
 * of X).
 *
 * <p>Bounds consistency: every bound has a support with the other variables in their intervals (see
 * {@link DivModPowBounds#mod}). With Y fixed, X also loses the values whose remainder is not in the
 * domain of Z.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XmodYeqZ extends AbstractXopYeqZ implements Copyable<XmodYeqZ>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs a constraint X mod Y = Z.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XmodYeqZ(IntVar x, IntVar y, IntVar z) {
    super(idNumber, x, y, z);
  }

  @Override
  public void consistency(final Store store) {

    y.domain.inComplement(store.level, y, 0);

    do {
      store.propagationHasOccurred = false;
      long[] b = {x.min(), x.max(), y.min(), y.max(), z.min(), z.max()};
      if (!DivModPowBounds.mod(b)) {
        throw Store.failException;
      }
      x.domain.in(store.level, x, (int) b[0], (int) b[1]);
      y.domain.in(store.level, y, (int) b[2], (int) b[3]);
      z.domain.in(store.level, z, (int) b[4], (int) b[5]);

      if (y.singleton()) {
        propagateWhenYsingleton(store);
      }
    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return BoxExplanation.explain(trail, entry, new IntVar[] {x, y, z}, DivModPowBounds::mod, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return BoxExplanation.explainFailure(trail, new IntVar[] {x, y, z}, DivModPowBounds::mod, out);
  }

  // x keeps the values whose remainder is in the domain of z
  private void propagateWhenYsingleton(Store store) {
    if (x.domain.getSize() < 100) {
      int absY = Math.abs(y.value());
      IntDomain d = makeDomain(x, absY, z);
      x.domain.in(store.level, x, d);
    } else {
      int absY = Math.abs(y.value());
      IntDomain zDom = z.dom();
      int xMin = x.min();
      boolean found = false;
      for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
        xMin = e.nextElement();
        if (zDom.contains(xMin % absY)) {
          found = true;
          break;
        }
      }
      if (found) {
        x.domain.inMin(store.level, x, xMin);
      } else {
        throw Store.failException;
      }
      int xMax = x.max();
      int xMinVal = x.min();
      while (!zDom.contains(xMax % absY) && xMax >= xMinVal) {
        xMax--;
      }
      if (xMax >= xMinVal) {
        x.domain.inMax(store.level, x, xMax);
      } else {
        throw Store.failException;
      }
    }
  }

  IntDomain makeDomain(IntVar x, int y, IntVar z) {
    IntervalDomain d = new IntervalDomain();
    boolean empty = true;
    IntDomain zDom = z.dom();
    for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int val = e.nextElement();
      if (zDom.contains(val % y)) {
        empty = false;
        if (d.getSize() == 0) {
          d.unionAdapt(val);
        } else {
          d.addLastElement(val);
        }
      }
    }
    if (empty) {
      throw Store.failException;
    }
    return d;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    // the propagation for a singleton y or x uses the holes of the domains of x and z
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    // the remainder has the sign of x, as in consistency()
    return grounded() && y.min() != 0 && z.min() == x.min() % y.min();
  }

  @Override
  public String toString() {

    return id() + " : XmodYeqZ(" + x + ", " + y + ", " + z + " )";
  }

  @Override
  public XmodYeqZ copy(VarMap map) {
    return new XmodYeqZ(map.get(x), map.get(y), map.get(z));
  }
}
