/*
 * LargestDomain.java
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

import org.jacop.core.Var;

/**
 * Defines LargestDomain comparator for Variables. Variable with the largest domain has the
 * priority.
 *
 * @param <T> it specifies the class of the variable being used in this variable selection method.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class LargestDomain<T extends Var> implements ComparatorVariable<T> {

  /** It constructs variable comparator based on the largest domain priority. */
  public LargestDomain() {
    // Intentionally empty: default constructor requires no initialization.
  }

  /**
   * Compares a metric value with a variable's domain size.
   *
   * @param left the metric value to compare.
   * @param v the variable to compare against.
   * @return positive if left has higher priority, negative if v has higher priority, 0 if equal.
   */
  public int compare(double left, T v) {
    int right = v.getSize();

    if (left > right) {
      return 1;
    }
    if (left < right) {
      return -1;
    }
    return 0;
  }

  /**
   * Compares two variables based on their domain sizes. Variables with larger domains have higher
   * priority.
   *
   * @param leftVar the first variable to compare.
   * @param rightVar the second variable to compare.
   * @return positive if leftVar has higher priority, negative if rightVar has higher priority, 0 if
   *     equal.
   */
  public int compare(T leftVar, T rightVar) {
    int left = leftVar.getSize();
    int right = rightVar.getSize();

    return Integer.compare(left, right);
  }

  /**
   * Computes the metric for a variable, which is its domain size.
   *
   * @param v the variable for which the metric is computed.
   * @return the domain size of the variable.
   */
  public double metric(T v) {
    return v.getSize();
  }
}
