/*
 * XeqY.java
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
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.ShiftExplanation;

/**
 * Constraints X #= Y.
 *
 * <p>Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XeqY extends AbstractConstraintXandY implements Copyable<XeqY>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs constraint X = Y.
   *
   * @param x variable x.
   * @param y variable y.
   */
  public XeqY(IntVar x, IntVar y) {

    super(idNumber, x, y);
  }

  @Override
  public void impose(Store store) {

    if (satisfied()) {
      // XeqY is trivially consistent.
      return;
    }

    super.impose(store);
  }

  @Override
  public void consistency(final Store store) {

    // domain consistency; after the two intersections x and y are equal, a fixpoint unless x only
    // keeps its bounds
    x.domain.in(store.level, x, y.domain);
    y.domain.in(store.level, y, x.domain);
    if (x.domain.domainId() == IntDomain.BOUND_DOMAIN_ID) {
      x.domain.in(store.level, x, y.domain);
    }
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void notConsistency(final Store store) {

    if (y.singleton()) {
      x.domain.inComplement(store.level, x, y.value());
    }

    if (x.singleton()) {
      y.domain.inComplement(store.level, y, x.value());
    }
  }

  @Override
  public boolean notSatisfied() {
    return !x.domain.isIntersecting(y.domain);
  }

  @Override
  public boolean satisfied() {
    int xMin = x.min();
    return x == y || x.singleton(xMin) && y.singleton(xMin);
  }

  @Override
  public String toString() {
    return id() + " : XeqY(" + x + ", " + y + " )";
  }

  @Override
  public XeqY copy(VarMap map) {
    return new XeqY(map.get(x), map.get(y));
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != XeqY.class || x == y) {
      return false;
    }
    return trail.variable(entry) == y
        ? ShiftExplanation.explain(trail, entry, y, x, 0, out)
        : ShiftExplanation.explain(trail, entry, x, y, -(long) 0, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == XeqY.class
        && x != y
        && ShiftExplanation.explainFailure(trail, y, x, 0, out);
  }

  // the equality as a linear form, for entailment and negation
  private LinearForm equality() {
    return getClass() == XeqY.class && x != y
        ? new LinearForm(new IntVar[] {x, y}, new long[] {1, -1}, 0, LinearForm.EQ)
        : null;
  }

  @Override
  public boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    LinearForm f = equality();
    if (f == null) {
      return false;
    }
    if (entailed) {
      return f.explainEntailed(trail, position, out);
    }
    return ShiftExplanation.disjointBefore(trail, position, y, x, 0, out);
  }

  @Override
  public boolean explainNegated(AtomicTrail trail, int entry, EntryList out) {
    LinearForm f = equality();
    return f != null && f.negated().explain(trail, entry, out);
  }

  @Override
  public boolean explainNegatedFailure(AtomicTrail trail, EntryList out) {
    LinearForm f = equality();
    return f != null && f.negated().explainFailure(trail, out);
  }
}
