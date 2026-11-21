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
    return Double.compare(ldiff, regret(v));
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
    return Long.compare(regret(left), regret(right));
  }

  /**
   * Computes the metric for a variable, which is the regret value (difference between smallest and
   * second smallest domain value).
   *
   * @param o the variable for which the metric is computed.
   * @return the regret value for the variable.
   */
  public double metric(T o) {
    return regret(o);
  }

  /**
   * The regret of a fixed variable is 0: it has no second value. Variable selection skips fixed
   * variables, but priority search ranks fixed priority variables too.
   */
  private static long regret(IntVar v) {
    ValueEnumeration e = v.domain.valueEnumeration();
    int min = e.nextElement();
    return e.hasMoreElements() ? (long) e.nextElement() - min : 0;
  }
}
