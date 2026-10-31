/*
 * XplusYeqC.java
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Constraint X + Y #= C.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class XplusYeqC extends AbstractConstraintXandY
    implements Copyable<XplusYeqC>, LinearExplainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies constant c in constraint x+y=c. */
  final int c;

  /**
   * It constructs the constraint X+Y=C.
   *
   * @param x variable x.
   * @param y variable y.
   * @param c constant c.
   */
  public XplusYeqC(IntVar x, IntVar y, int c) {

    super(idNumber, x, y);

    this.c = c;

    checkForOverflow();
  }

  void checkForOverflow() {
    checkSumOverflow(x.min(), x.max(), y.min(), y.max(), c, c);
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    // notSatisfied() looks at the holes of the domains
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void consistency(final Store store) {

    // after the two mirrors x and y are mirror images, a fixpoint unless y only keeps its bounds
    inMirror(store, y, x);
    inMirror(store, x, y);
    if (y.domain.domainId() == IntDomain.BOUND_DOMAIN_ID) {
      inMirror(store, y, x);
    }
  }

  /** Keeps in target only the values c - v for v in source. */
  private void inMirror(Store store, IntVar target, IntVar source) {
    IntDomain sourceDom = source.dom();
    IntervalDomain targetDomIn = new IntervalDomain(sourceDom.noIntervals() + 1);
    for (int i = sourceDom.noIntervals() - 1; i >= 0; i--) {
      targetDomIn.unionAdapt(
          new Interval(c - sourceDom.rightElement(i), c - sourceDom.leftElement(i)));
    }

    target.domain.in(store.level, target, targetDomIn);
  }

  @Override
  public void notConsistency(final Store store) {

    do {

      store.propagationHasOccurred = false;

      if (x.singleton()) {
        y.domain.inComplement(store.level, y, c - x.value());
      } else if (y.singleton()) {
        x.domain.inComplement(store.level, x, c - y.value());
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean notSatisfied() {
    IntDomain xDom = x.dom();
    IntDomain yDom = y.dom();
    if (xDom.max() + yDom.max() < c || xDom.min() + yDom.min() > c) {
      return true;
    }
    // no value c - v for v in y is a value of x
    for (int i = 0, n = yDom.noIntervals(); i < n; i++) {
      if (xDom.isIntersecting(c - yDom.rightElement(i), c - yDom.leftElement(i))) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    int xMin = x.min();
    int yMin = y.min();
    return x.singleton(xMin) && y.singleton(yMin) && xMin + yMin == c;
  }

  @Override
  public String toString() {

    return id() + " : XplusYeqC(" + x + ", " + y + ", " + c + " )";
  }

  @Override
  public XplusYeqC copy(VarMap map) {
    return new XplusYeqC(map.get(x), map.get(y), c);
  }

  @Override
  public LinearForm linearForm() {
    return getClass() == XplusYeqC.class
        ? new LinearForm(new IntVar[] {x, y}, new long[] {1, 1}, c, LinearForm.EQ)
        : null;
  }
}
