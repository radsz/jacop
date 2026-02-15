/*
 * LargestMin.java
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

/**
 * Defines a LargestMin comparator for Variables. It prefers variables which have larger minimal
 * value in their domain.
 *
 * @param <T> type of IntVar being compared.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class LargestMin<T extends IntVar> implements ComparatorVariable<T> {

  /** It constructs LargestMin Comparator. */
  public LargestMin() {
    // Intentionally empty: default constructor requires no initialization.
  }

  /**
   * Compares a metric value with a variable's minimum domain value.
   *
   * @param left the metric value to compare.
   * @param v the variable to compare against.
   * @return positive if left has higher priority, negative if v has higher priority, 0 if equal.
   */
  public int compare(double left, T v) {
    int right = v.dom().min();
    if (left > right) {
      return 1;
    }
    if (left < right) {
      return -1;
    }
    return 0;
  }

  /**
   * Compares two variables based on their minimum domain values. Variables with larger minimum
   * values have higher priority.
   *
   * @param leftVar the first variable to compare.
   * @param rightVar the second variable to compare.
   * @return positive if leftVar has higher priority, negative if rightVar has higher priority, 0 if
   *     equal.
   */
  public int compare(T leftVar, T rightVar) {
    int left = leftVar.dom().min();
    int right = rightVar.dom().min();
    return Integer.compare(left, right);
  }

  /**
   * Computes the metric for a variable, which is the minimum value in its domain.
   *
   * @param v the variable for which the metric is computed.
   * @return the minimum value in the variable's domain.
   */
  public double metric(T v) {
    return v.dom().min();
  }
}
