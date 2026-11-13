/*
 * Same.java
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

/**
 * Same (same of the Global Constraint Catalog): y is a permutation of x, that is the two lists hold
 * the same multiset of values.
 *
 * <p>It is domain consistent, with the flow network of N. Beldiceanu, I. Katriel and S. Thiel,
 * "Filtering algorithms for the Same constraint", CPAIOR 2004; see {@link AbstractSame}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class Same extends AbstractSame implements Copyable<Same> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs the constraint.
   *
   * @param x the first list
   * @param y the second list; x and y need the same length
   */
  public Same(IntVar[] x, IntVar[] y) {
    super(x, y, false);
    this.numberId = idNumber.incrementAndGet();
  }

  @Override
  public String toString() {
    return toString("Same");
  }

  @Override
  public Same copy(VarMap map) {
    return new Same(map.get(x), map.get(y));
  }
}
