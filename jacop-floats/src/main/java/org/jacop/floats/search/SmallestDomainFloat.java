/*
 * SmallestDomainFloat.java
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

import org.jacop.core.Var;
import org.jacop.search.ComparatorVariable;

/**
 * Defines a Smallest Domain comparator for Variables. The variable with the smallest domain has the
 * priority.
 *
 * @param <T> type of variable being used in the search.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class SmallestDomainFloat<T extends Var> implements ComparatorVariable<T> {

  /** It constructs a smallest domain variable comparator. */
  public SmallestDomainFloat() {
    // Default constructor; no state to initialize.
  }

  /**
   * Compares a metric value with a variable's domain size.
   *
   * @param left the metric value to compare
   * @param v the variable whose domain size is compared
   * @return negative if v has smaller domain, positive if larger, zero if equal
   */
  public int compare(double left, T v) {
    double right = v.getSizeFloat();

    return Double.compare(right, left);
  }

  /**
   * Compares two variables based on their domain sizes.
   *
   * @param leftVar the first variable to compare
   * @param rightVar the second variable to compare
   * @return negative if leftVar has smaller domain, positive if larger, zero if equal
   */
  public int compare(T leftVar, T rightVar) {
    double left = leftVar.getSizeFloat();
    double right = rightVar.getSizeFloat();

    return Double.compare(right, left);
  }

  /**
   * Computes the metric value for a variable based on its domain size.
   *
   * @param v the variable to compute the metric for
   * @return the domain size of the variable
   */
  public double metric(T v) {
    return v.getSizeFloat();
  }
}
