/*
 * WeightedDegree.java
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

import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Defines a WeightedDegree comparator for variables. Every time a constraint failure is encountered
 * all variables within the scope of that constraints have increased weight. The comparator will
 * choose the variable with the highest weight divided by its size.
 *
 * <p>This implementation is not equivalent to AfcMaxDeg since it takes all accumulated failures for
 * a variable while AfcMaxDeg sums up weights for still active constraints only!
 *
 * @param <T> type of variable being compared.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class WeightedDegree<T extends Var> implements ComparatorVariable<T> {

  protected WeightedDegree() {}

  /**
   * Constructs a WeightedDegree comparator and enables variable weight management in the store.
   *
   * @param store the constraint store for which weight management is enabled.
   */
  public WeightedDegree(Store store) {
    store.variableWeightManagement = true;
  }

  /**
   * Compares a precomputed metric value against the weighted degree metric of the given variable.
   *
   * @param left the precomputed metric value.
   * @param v the variable whose metric is computed and compared.
   * @return a negative integer, zero, or a positive integer as left is less than, equal to, or
   *     greater than the variable's metric.
   */
  public int compare(double left, T v) {

    double right = v.weight / v.getSizeFloat();

    return Double.compare(left, right);
  }

  /**
   * Compares two variables based on their weighted degree divided by domain size.
   *
   * @param leftVar the first variable to compare.
   * @param rightVar the second variable to compare.
   * @return a negative integer, zero, or a positive integer as leftVar's metric is less than, equal
   *     to, or greater than rightVar's metric.
   */
  public int compare(T leftVar, T rightVar) {

    double left = leftVar.weight / leftVar.getSizeFloat();

    double right = rightVar.weight / rightVar.getSizeFloat();

    return Double.compare(left, right);
  }

  /**
   * Computes the weighted degree metric for the given variable (weight divided by domain size).
   *
   * @param v the variable for which the metric is computed.
   * @return the weighted degree metric value.
   */
  public double metric(T v) {

    return v.weight / v.getSizeFloat();
  }
}
