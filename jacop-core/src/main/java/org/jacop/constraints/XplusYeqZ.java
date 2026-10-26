/*
 * XplusYeqZ.java
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
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearExplanation;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.ShiftExplanation;

/**
 * Constraint X + Y = Z.
 *
 * <p>Bound consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XplusYeqZ extends AbstractConstraintXandYandZ
    implements Copyable<XplusYeqZ>, LinearExplainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs constraint X+Y=Z.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XplusYeqZ(IntVar x, IntVar y, IntVar z) {

    super(idNumber, x, y, z);

    checkForOverflow();
  }

  @Override
  public void consistency(final Store store) {

    if (x == z || y == z) {
      // x + y = x means y = 0 (and x + y = y means x = 0); the shifts below would not reach a
      // fixpoint, since the constraint is not woken by its own pruning
      IntVar other = x == z ? y : x;
      other.domain.inValue(store.level, other, 0);
      return;
    }

    do {

      store.propagationHasOccurred = false;

      // with x (or y) fixed the two shifts make y and z equal up to the shift, which is a fixpoint
      // unless the first variable shifted only keeps its bounds
      if (x.singleton()) {

        y.domain.inShift(store.level, y, z.domain, -x.value());
        z.domain.inShift(store.level, z, y.domain, x.value());
        if (y.domain.domainId() != IntDomain.BOUND_DOMAIN_ID) {
          return;
        }

      } else if (y.singleton()) {

        x.domain.inShift(store.level, x, z.domain, -y.value());
        z.domain.inShift(store.level, z, x.dom(), y.value());
        if (x.domain.domainId() != IntDomain.BOUND_DOMAIN_ID) {
          return;
        }

      } else {

        // for large domains (for example, Integer.MIN_VALUE..Integer.MAX_VALUE) uncomment three
        // lines below,
        // comment three lines after uncommented lines and checkForOverlow in the constructor

        x.domain.in(store.level, x, z.min() - y.max(), z.max() - y.min());
        y.domain.in(store.level, y, z.min() - x.max(), z.max() - x.min());
        z.domain.in(store.level, z, x.min() + y.min(), x.max() + y.max());
      }

    } while (store.propagationHasOccurred);
  }

  void checkForOverflow() {
    checkSumOverflow(x.min(), x.max(), y.min(), y.max(), z.min(), z.max());
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  // Once x or y is a singleton, consistency() makes z and the other variable equal up to a shift,
  // so a value removed inside a domain must wake the constraint as well.
  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void notConsistency(final Store store) {

    if (x == z || y == z) {
      IntVar other = x == z ? y : x;
      other.domain.inComplement(store.level, other, 0);
      return;
    }

    do {

      store.propagationHasOccurred = false;

      if (z.singleton() && y.singleton()) {
        x.domain.inComplement(store.level, x, z.min() - y.min());
      }

      if (z.singleton() && x.singleton()) {
        y.domain.inComplement(store.level, y, z.min() - x.min());
      }

      if (x.singleton() && y.singleton()) {
        z.domain.inComplement(store.level, z, x.min() + y.min());
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean notSatisfied() {
    if (x == z || y == z) {
      return !(x == z ? y : x).domain.contains(0);
    }
    IntDomain xDom = x.dom();
    IntDomain yDom = y.dom();
    IntDomain zDom = z.dom();
    return xDom.max() + yDom.max() < zDom.min() || xDom.min() + yDom.min() > zDom.max();
  }

  @Override
  public boolean satisfied() {

    if (x == z || y == z) {
      return (x == z ? y : x).singleton(0);
    }
    int xMin = x.min();
    int yMin = y.min();
    int zMin = z.min();
    return x.singleton(xMin) && y.singleton(yMin) && z.singleton(zMin) && xMin + yMin == zMin;
  }

  @Override
  public String toString() {

    return id() + " : XplusYeqZ(" + x + ", " + y + ", " + z + " )";
  }

  @Override
  public XplusYeqZ copy(VarMap map) {
    return new XplusYeqZ(map.get(x), map.get(y), map.get(z));
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != XplusYeqZ.class || x == y || x == z || y == z) {
      return false;
    }
    return ShiftExplanation.explainSum(trail, entry, x, y, z, out)
        || LinearExplanation.explainChecked(
            trail, entry, new IntVar[] {x, y, z}, new long[] {1, 1, -1}, 0, true, true, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != XplusYeqZ.class || x == y || x == z || y == z) {
      return false;
    }
    return ShiftExplanation.explainSumFailure(trail, x, y, z, out)
        || LinearExplanation.explainFailure(
            trail, new IntVar[] {x, y, z}, new long[] {1, 1, -1}, 0, true, true, out);
  }

  // the equality, for entailment and negation
  @Override
  public LinearForm linearForm() {
    return getClass() == XplusYeqZ.class && x != y && x != z && y != z
        ? new LinearForm(new IntVar[] {x, y, z}, new long[] {1, 1, -1}, 0, LinearForm.EQ)
        : null;
  }
}
