/*
 * MostConstrainedStatic.java
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
 * Defines a MostConstraintStatic comparator for Variables. It selects variables with the most
 * constraints originally attached to them. The constraint count is static (from the initial problem
 * state).
 *
 * @param <T> type of variable being compared.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class MostConstrainedStatic<T extends Var> implements ComparatorVariable<T> {

  /** It constructs MostConstraintStatic comparator. */
  public MostConstrainedStatic() {}

  /**
   * Compares a metric value with a variable's original constraint count.
   *
   * @param left the metric value to compare.
   * @param v the variable to compare against.
   * @return positive if left has higher priority, negative if v has higher priority, 0 if equal.
   */
  public int compare(double left, T v) {
    int right = v.sizeConstraintsOriginal();
    if (left > right) {
      return 1;
    }
    if (left < right) {
      return -1;
    }
    return 0;
  }

  /**
   * Compares two variables based on their original constraint counts. Variables with more
   * constraints have higher priority.
   *
   * @param leftVar the first variable to compare.
   * @param rightVar the second variable to compare.
   * @return positive if leftVar has higher priority, negative if rightVar has higher priority, 0 if
   *     equal.
   */
  public int compare(T leftVar, T rightVar) {
    int left = leftVar.sizeConstraintsOriginal();
    int right = rightVar.sizeConstraintsOriginal();
    return Integer.compare(left, right);
  }

  /**
   * Computes the metric for a variable, which is its original number of attached constraints.
   *
   * @param o the variable for which the metric is computed.
   * @return the original number of constraints attached to the variable.
   */
  public double metric(T o) {
    return o.sizeConstraintsOriginal();
  }
}
