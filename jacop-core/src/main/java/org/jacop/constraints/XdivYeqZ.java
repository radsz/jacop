/*
 * XdivYeqZ.java
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

/**
 * Constraint X div Y #= Z, with the division rounding towards zero.
 *
 * <p>Bounds consistency: every bound has a support with the other variables in their intervals (see
 * {@link DivModPowBounds#div}).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XdivYeqZ extends AbstractXopYeqZ implements Copyable<XdivYeqZ>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs a constraint X div Y = Z.
   *
   * @param x variable x.
   * @param y variable y.
   * @param z variable z.
   */
  public XdivYeqZ(IntVar x, IntVar y, IntVar z) {
    super(idNumber, x, y, z);
  }

  @Override
  public void consistency(final Store store) {

    y.domain.inComplement(store.level, y, 0);

    do {
      store.propagationHasOccurred = false;
      long[] b = {x.min(), x.max(), y.min(), y.max(), z.min(), z.max()};
      if (!DivModPowBounds.div(b)) {
        throw Store.failException;
      }
      x.domain.in(store.level, x, (int) b[0], (int) b[1]);
      y.domain.in(store.level, y, (int) b[2], (int) b[3]);
      z.domain.in(store.level, z, (int) b[4], (int) b[5]);
    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return BoxExplanation.explain(trail, entry, new IntVar[] {x, y, z}, DivModPowBounds::div, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return BoxExplanation.explainFailure(trail, new IntVar[] {x, y, z}, DivModPowBounds::div, out);
  }

  @Override
  public boolean satisfied() {
    // integer division rounds towards zero, as in consistency()
    return grounded() && y.min() != 0 && z.min() == x.min() / y.min();
  }

  @Override
  public String toString() {

    return id() + " : XdivYeqZ(" + x + ", " + y + ", " + z + " )";
  }

  @Override
  public XdivYeqZ copy(VarMap map) {
    return new XdivYeqZ(map.get(x), map.get(y), map.get(z));
  }
}
