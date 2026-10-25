/*
 * RoundPeqX.java
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

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;

/**
 * Constraints round(P) #= X for integer variable X and float variable P.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class RoundPeqX extends AbstractRoundPeqX implements Copyable<RoundPeqX> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs constraint X = P.
   *
   * @param x variable x.
   * @param p variable p.
   */
  public RoundPeqX(FloatVar p, IntVar x) {
    super(idNumber, p, x);
  }

  @Override
  public void consistency(Store store) {

    do {
      int min = round(p.min());
      int max = round(p.max());

      x.domain.in(store.level, x, min, max);

      store.propagationHasOccurred = false;

      p.domain.in(store.level, p, lowest(x.min()), highest(x.max()));

    } while (store.propagationHasOccurred);
  }

  double fractionalPart(double p) {
    long iPart = (long) p;
    return p - iPart;
  }

  int round(double p) {

    double fPart = fractionalPart(p);

    int r;
    if (p < 0) {
      if (fPart <= -0.5) {
        r = (int) Math.floor(p);
      } else {
        r = (int) Math.ceil(p);
      }
    } else { // p >= 0
      if (fPart >= 0.5) {
        r = (int) Math.ceil(p);
      } else {
        r = (int) Math.floor(p);
      }
    }
    return r;
  }

  /**
   * The smallest p that rounds to x; halves round away from zero, so x - 0.5 rounds to x when x is
   * positive.
   */
  static double lowest(int x) {
    return x > 0 ? x - 0.5 : Math.nextUp(x - 0.5);
  }

  /**
   * The largest p that rounds to x; halves round away from zero, so x + 0.5 rounds to x when x is
   * negative.
   */
  static double highest(int x) {
    return x < 0 ? x + 0.5 : Math.nextDown(x + 0.5);
  }

  @Override
  public boolean satisfied() {
    return x.singleton() && p.min() >= lowest(x.value()) && p.max() <= highest(x.value());
  }

  @Override
  public String toString() {
    return id() + " : RoundPeqX(" + p + ", " + x + " )";
  }

  @Override
  public RoundPeqX copy(VarMap map) {
    return new RoundPeqX(map.get(p), map.get(x));
  }
}
