/*
 * SmallestMax.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * Defines a SmallestMax comparator for Variables. The variable with maximum value 5 will have a
 * priority over variable with maximum value equal 10.
 *
 * @param <T> type of variable being used in the search.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
public class SmallestMax<T extends IntVar> implements ComparatorVariable<T> {

  /** It constructs the variable comparator based on the smallest maximal value from the domain. */
  public SmallestMax() {}

  /**
   * Compares a metric value with a variable's maximum domain value.
   *
   * @param left the metric value to compare.
   * @param var the variable to compare against.
   * @return positive if left has higher priority, negative if var has higher priority, 0 if equal.
   */
  public int compare(double left, T var) {
    int right = var.dom().max();
    if (left < right) {
      return 1;
    }
    if (left > right) {
      return -1;
    }
    return 0;
  }

  /**
   * Compares two variables based on their maximum domain values. Variables with smaller maximum
   * values have higher priority.
   *
   * @param leftVar the first variable to compare.
   * @param rightVar the second variable to compare.
   * @return positive if leftVar has higher priority, negative if rightVar has higher priority, 0 if
   *     equal.
   */
  public int compare(T leftVar, T rightVar) {
    int left = leftVar.dom().max();
    int right = rightVar.dom().max();
    return Integer.compare(right, left);
  }

  /**
   * Computes the metric for a variable, which is the maximum value in its domain.
   *
   * @param var the variable for which the metric is computed.
   * @return the maximum value in the variable's domain.
   */
  public double metric(T var) {
    return var.dom().max();
  }
}
