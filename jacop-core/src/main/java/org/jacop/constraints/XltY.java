/*
 * XltY.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearExplanation;

/**
 * Constraint X {@literal <} Y.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XltY extends AbstractXcompY implements Copyable<XltY>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs the constraint X {@literal <} Y.
   *
   * @param x variable x.
   * @param y variable y.
   */
  public XltY(IntVar x, IntVar y) {
    super(idNumber, x, y);
  }

  @Override
  protected boolean readsMinOfX() {
    return true;
  }

  @Override
  public void consistency(final Store store) {
    if (x == y) {
      // x op x never holds; pruning one bound at a time on the same variable would not reach a
      // fixpoint in one call
      throw Store.failException;
    }
    x.domain.inMax(store.level, x, y.max() - 1);
    y.domain.inMin(store.level, y, x.min() + 1);
  }

  @Override
  public void notConsistency(final Store store) {

    x.domain.inMin(store.level, x, y.min());
    y.domain.inMax(store.level, y, x.max());
  }

  @Override
  public boolean notSatisfied() {
    return x == y || x.min() >= y.max();
  }

  @Override
  public boolean satisfied() {
    return x.max() < y.min();
  }

  @Override
  public String toString() {
    return id() + " : XltY(" + x + ", " + y + " )";
  }

  @Override
  public XltY copy(VarMap map) {
    return new XltY(map.get(x), map.get(y));
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == XltY.class
        && x != y
        && LinearExplanation.explain(
            trail, entry, new IntVar[] {x, y}, new long[] {1, -1}, true, false, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == XltY.class
        && x != y
        && LinearExplanation.explainFailure(
            trail, new IntVar[] {x, y}, new long[] {1, -1}, -1, true, false, out);
  }
}
