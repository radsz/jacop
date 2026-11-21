/*
 * MaxRegretFloat.java
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

package org.jacop.floats.search;

import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.ComparatorVariable;

// import org.jacop.core.ValueEnumeration;

/**
 * Defines a MaxRegretFloat comparator for Variables.
 *
 * @param <T> variable of type FloatVar.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class MaxRegretFloat<T extends FloatVar> implements ComparatorVariable<T> {

  /** It constructs MaxRegretFloat comparator. */
  public MaxRegretFloat() {
    // Default constructor; no state to initialize.
  }

  /**
   * Compares a metric value with a variable's regret (difference between smallest and second
   * smallest values).
   *
   * @param ldiff the metric value to compare
   * @param v the variable whose regret is compared
   * @return negative if v has smaller regret, positive if larger, zero if equal
   */
  public int compare(double ldiff, T v) {

    double rmin = v.min();
    double rminNext = ((FloatIntervalDomain) v.domain).nextValue(rmin);

    double rdiff = rminNext - rmin;

    return Double.compare(ldiff, rdiff);
  }

  /**
   * Compares two variables based on their regret values.
   *
   * @param left the first variable to compare
   * @param right the second variable to compare
   * @return negative if left has smaller regret, positive if larger, zero if equal
   */
  public int compare(T left, T right) {

    double lmin = left.min();
    double lminNext = ((FloatIntervalDomain) left.domain).nextValue(lmin);

    double ldiff = lminNext - lmin;

    double rmin = right.min();
    double rminNext = ((FloatIntervalDomain) right.domain).nextValue(rmin);

    double rdiff = rminNext - rmin;

    return Double.compare(ldiff, rdiff);
  }

  /**
   * Computes the metric value for a variable based on its regret.
   *
   * @param o the variable to compute the metric for
   * @return the regret value (difference between smallest and second smallest domain values)
   */
  public double metric(T o) {

    double omin = o.min();
    double ominNext = ((FloatIntervalDomain) o.domain).nextValue(omin);

    return ominNext - omin;
  }
}
