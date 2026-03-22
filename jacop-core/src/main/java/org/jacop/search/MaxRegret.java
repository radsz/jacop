/*
 * MaxRegret.java
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

package org.jacop.search;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;

/**
 * Defines a MaxRegret comparator for Variables. It selects variables with maximum regret, which is
 * the difference between the smallest and second smallest value in the domain. This heuristic helps
 * identify variables where choosing the wrong value would be most costly.
 *
 * @param <T> variable of type IntVar.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class MaxRegret<T extends IntVar> implements ComparatorVariable<T> {

  /** It constructs MaxRegret comparator. */
  public MaxRegret() {
    // Intentionally empty: default constructor requires no initialization.
  }

  /**
   * Compares a metric value (regret) with a variable's regret value.
   *
   * @param ldiff the metric value to compare.
   * @param v the variable to compare against.
   * @return positive if ldiff has higher priority, negative if v has higher priority, 0 if equal.
   */
  public int compare(double ldiff, T v) {

    ValueEnumeration rEnum = v.domain.valueEnumeration();

    int rmin = rEnum.nextElement();
    int rminNext;
    if (rEnum.hasMoreElements()) {
      rminNext = rEnum.nextElement();
    } else {
      rminNext = IntDomain.MAX_INT;
    }

    int rdiff = rminNext - rmin;

    if (ldiff > rdiff) {
      return 1;
    }
    if (ldiff < rdiff) {
      return -1;
    }
    return 0;
  }

  /**
   * Compares two variables based on their regret values. Variables with larger regret have higher
   * priority.
   *
   * @param left the first variable to compare.
   * @param right the second variable to compare.
   * @return positive if left has higher priority, negative if right has higher priority, 0 if
   *     equal.
   */
  public int compare(T left, T right) {

    ValueEnumeration lEnum = left.domain.valueEnumeration();

    int lmin = lEnum.nextElement();
    int lminNext;
    if (lEnum.hasMoreElements()) {
      lminNext = lEnum.nextElement();
    } else {
      lminNext = IntDomain.MAX_INT;
    }

    int ldiff = lminNext - lmin;

    ValueEnumeration rEnum = right.domain.valueEnumeration();

    int rmin = rEnum.nextElement();
    int rminNext;
    if (rEnum.hasMoreElements()) {
      rminNext = rEnum.nextElement();
    } else {
      rminNext = IntDomain.MAX_INT;
    }

    int rdiff = rminNext - rmin;

    return Integer.compare(ldiff, rdiff);
  }

  /**
   * Computes the metric for a variable, which is the regret value (difference between smallest and
   * second smallest domain value).
   *
   * @param o the variable for which the metric is computed.
   * @return the regret value for the variable.
   */
  public double metric(T o) {

    ValueEnumeration oEnum = o.domain.valueEnumeration();

    int omin = oEnum.nextElement();
    int ominNext;
    if (oEnum.hasMoreElements()) {
      ominNext = oEnum.nextElement();
    } else {
      ominNext = IntDomain.MAX_INT;
    }

    return (double) ominNext - omin;
  }
}
