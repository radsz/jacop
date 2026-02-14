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
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Constraint X ^ Y #= Z.
 *
 * <p>Boundary consistecny is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XexpYeqZ extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies the variable x in equation x^y = z. */
  private final IntVar x;

  /** It specifies the variable y in equation x^y = z. */
  private final IntVar y;

  /** It specifies the variable z in equation x^y = z. */
  private final IntVar z;

  /**
   * It constructs constraint X^Y=Z.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XexpYeqZ(IntVar x, IntVar y, IntVar z) {

    checkInputForNullness(new String[] {"x", "y", "z"}, new Object[] {x, y, z});

    numberId = idNumber.incrementAndGet();

    this.x = x;
    this.y = y;
    this.z = z;

    setScope(x, y, z);
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      // compute domain for x,y and z
      IntDomain zDom = new IntervalDomain();
      IntDomain xDom = new IntervalDomain();
      IntDomain yDom = new IntervalDomain();
      for (ValueEnumeration ex = x.domain.valueEnumeration(); ex.hasMoreElements(); ) {
        int xi = ex.nextElement();
        for (ValueEnumeration ey = y.domain.valueEnumeration(); ey.hasMoreElements(); ) {
          int yi = ey.nextElement();

          int zi;
          long zl;
          if (xi == 0) {
            if (yi == 0) {
              zi = 1;
            } else if (yi < 0) {
              continue; // 0 to negative exponent is infinity :(
            } else {
              zi = 0;
            }
          } else {
            zl = toLong(Math.pow(xi, yi));

            if (zl < z.min() || zl > z.max()) {
              continue; // value not in domain of z
            } else {
              zi = long2int(zl);
            }
          }

          if (z.domain.contains(zi)) {
            xDom.unionAdapt(xi);
            yDom.unionAdapt(yi);
          }

          zDom.unionAdapt(zi);
        }
      }

      z.domain.in(store.level, z, zDom);
      x.domain.in(store.level, x, xDom);
      y.domain.in(store.level, y, yDom);

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean satisfied() {

    return grounded() && toInt(Math.pow(x.min(), y.min())) == z.min();
  }

  @Override
  public String toString() {

    return id() + " : XexpYeqZ(" + x + ", " + y + ", " + z + " )";
  }
}
