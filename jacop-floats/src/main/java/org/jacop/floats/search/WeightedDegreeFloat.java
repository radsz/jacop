/*
 * WeightedDegreeFloat.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.search;

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.ComparatorVariable;

/**
 * Defines a WeightedDegreeFloat comparator for Variables. Every time a constraint failure is
 * encountered all variables within the scope of that constraints have increased weight. The
 * comparator will choose the variable with the highest weight divided by its size.
 *
 * @param <T> type of variable being compared.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.10
 */
public class WeightedDegreeFloat<T extends Var> implements ComparatorVariable<T> {

  private WeightedDegreeFloat() {}

  /**
   * Constructs a WeightedDegreeFloat comparator and enables variable weight management in the
   * store.
   *
   * @param store the constraint store where variable weights will be tracked
   */
  public WeightedDegreeFloat(Store store) {
    store.variableWeightManagement = true;
  }

  /**
   * Compares a metric value with a variable's weighted degree (weight divided by domain size).
   *
   * @param left the metric value to compare
   * @param var the variable whose weighted degree is compared
   * @return negative if var has smaller weighted degree, positive if larger, zero if equal
   */
  public int compare(double left, T var) {

    double right = ((double) var.weight) / var.getSizeFloat();

    return Double.compare(left, right);
  }

  /**
   * Compares two variables based on their weighted degree values.
   *
   * @param leftVar the first variable to compare
   * @param rightVar the second variable to compare
   * @return negative if leftVar has smaller weighted degree, positive if larger, zero if equal
   */
  public int compare(T leftVar, T rightVar) {

    double left = ((double) leftVar.weight) / leftVar.getSizeFloat();

    double right = ((double) rightVar.weight) / rightVar.getSizeFloat();

    return Double.compare(left, right);
  }

  /**
   * Computes the metric value for a variable based on its weighted degree.
   *
   * @param var the variable to compute the metric for
   * @return the weighted degree (variable weight divided by domain size)
   */
  public double metric(T var) {

    return var.weight / var.getSizeFloat();
  }
}
