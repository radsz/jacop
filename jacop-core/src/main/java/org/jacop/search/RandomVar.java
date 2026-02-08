/*
 * RandomVar.java
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

import java.util.Random;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Defines a RandomVar comparator for variables. It selects variables randomly.
 *
 * @param <T> type of variable being used in the search.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class RandomVar<T extends Var> implements ComparatorVariable<T> {

  final Random generator = Store.seedPresent() ? new Random(Store.getSeed()) : new Random();

  /** It constructs RandomVar Comparator. */
  public RandomVar() {}

  /**
   * Compares a metric value with a randomly generated value for a variable.
   *
   * @param left the metric value to compare.
   * @param var the variable to compare against.
   * @return positive if left has higher priority, negative if var has higher priority, 0 if equal.
   */
  public int compare(double left, T var) {
    double right = generator.nextFloat();
    return Double.compare(right, left);
  }

  /**
   * Compares two variables using randomly generated values. This provides random variable
   * selection.
   *
   * @param leftVar the first variable to compare.
   * @param rightVar the second variable to compare.
   * @return positive if leftVar has higher priority, negative if rightVar has higher priority, 0 if
   *     equal.
   */
  public int compare(T leftVar, T rightVar) {
    double left = generator.nextFloat();
    double right = generator.nextFloat();
    return Double.compare(right, left);
  }

  /**
   * Computes the metric for a variable, which is a randomly generated value.
   *
   * @param o the variable for which the metric is computed.
   * @return a random value between 0 and 1.
   */
  public double metric(T o) {
    return generator.nextFloat();
  }
}
