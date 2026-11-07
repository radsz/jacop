/*
 * XplusCeqZ.java
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
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.ShiftExplanation;

/**
 * Constraint X + C #= Z.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XplusCeqZ extends AbstractConstraintXandCandZ
    implements Copyable<XplusCeqZ>, LinearExplainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs a constraint x+c=z.
   *
   * @param x variable x.
   * @param c constant c.
   * @param z variable z.
   */
  public XplusCeqZ(IntVar x, int c, IntVar z) {

    super(idNumber, x, c, z);

    checkForOverflow();
  }

  void checkForOverflow() {
    checkSumOverflow(x.min(), x.max(), c, c, z.min(), z.max());
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

    if (x == z) {
      // x + c = x holds only for c = 0; the shifts below would not reach a fixpoint, since the
      // constraint is not woken by its own pruning
      if (c != 0) {
        throw Store.failException;
      }
      return;
    }

    // after the two shifts z equals x shifted by c, a fixpoint unless x only keeps its bounds
    x.domain.inShiftFast(store.level, x, z.domain, -c);
    z.domain.inShiftFast(store.level, z, x.domain, c);
    if (x.domain.domainId() == IntDomain.BOUND_DOMAIN_ID) {
      x.domain.inShiftFast(store.level, x, z.domain, -c);
    }
  }

  @Override
  public void notConsistency(final Store store) {

    if (x == z) {
      if (c == 0) {
        throw Store.failException;
      }
      return;
    }

    do {

      store.propagationHasOccurred = false;

      if (x.singleton()) {
        z.domain.inComplement(store.level, z, x.min() + c);
      }

      if (z.singleton()) {
        x.domain.inComplement(store.level, x, z.min() - c);
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean notSatisfied() {
    if (x == z) {
      return c != 0;
    }
    if (x.max() + c < z.min() || x.min() + c > z.max()) {
      return true;
    }
    // no value of x shifted by c is a value of z
    IntDomain xDom = x.dom();
    IntDomain zDom = z.dom();
    for (int i = 0, n = xDom.noIntervals(); i < n; i++) {
      if (zDom.isIntersecting(xDom.leftElement(i) + c, xDom.rightElement(i) + c)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    if (x == z) {
      return c == 0;
    }
    int xMin = x.min();
    int zMin = z.min();
    return x.singleton(xMin) && z.singleton(zMin) && xMin + c == zMin;
  }

  @Override
  public String toString() {

    return id() + " : XplusCeqZ(" + x + ", " + c + ", " + z + " )";
  }

  @Override
  public XplusCeqZ copy(VarMap map) {
    return new XplusCeqZ(map.get(x), c, map.get(z));
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != XplusCeqZ.class || x == z) {
      return false;
    }
    return trail.variable(entry) == z
        ? ShiftExplanation.explain(trail, entry, z, x, c, out)
        : ShiftExplanation.explain(trail, entry, x, z, -(long) c, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == XplusCeqZ.class
        && x != z
        && ShiftExplanation.explainFailure(trail, z, x, c, out);
  }

  // the equality, for entailment and negation
  @Override
  public LinearForm linearForm() {
    return getClass() == XplusCeqZ.class && x != z
        ? new LinearForm(new IntVar[] {x, z}, new long[] {1, -1}, -(long) c, LinearForm.EQ)
        : null;
  }

  @Override
  public boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    LinearForm f = linearForm();
    if (f == null) {
      return false;
    }
    if (entailed) {
      return f.explainEntailed(trail, position, out);
    }
    return ShiftExplanation.disjointBefore(trail, position, z, x, c, out);
  }
}
