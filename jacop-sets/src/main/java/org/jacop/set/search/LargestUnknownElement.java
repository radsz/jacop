/*
 * LargestUnknownElement.java
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

package org.jacop.set.search;

import org.jacop.core.IntDomain;
import org.jacop.search.ComparatorVariable;
import org.jacop.set.core.SetVar;

/**
 * Prefers the set variable with the largest undecided element (in the least upper bound, not in the
 * greatest lower bound): MiniZinc's largest for set_search, as Gecode's SET_VAR_MAX_MAX.
 *
 * @param <T> type of variable being used in the search.
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LargestUnknownElement<T extends SetVar> implements ComparatorVariable<T> {

  /** Creates the comparator. */
  public LargestUnknownElement() {
    // No-op: comparator does not require initialization.
  }

  /** The largest undecided element, or Integer.MIN_VALUE for a decided set. */
  private static int element(SetVar v) {
    IntDomain undecided = v.dom().lub().subtract(v.dom().glb());
    return undecided.isEmpty() ? Integer.MIN_VALUE : undecided.max();
  }

  @Override
  public int compare(double left, T v) {
    int right = element(v);
    if (left > right) {
      return 1;
    }
    if (left < right) {
      return -1;
    }
    return 0;
  }

  @Override
  public int compare(T leftVar, T rightVar) {
    int left = element(leftVar);
    int right = element(rightVar);
    return Integer.compare(left, right);
  }

  @Override
  public double metric(T v) {
    return element(v);
  }
}
