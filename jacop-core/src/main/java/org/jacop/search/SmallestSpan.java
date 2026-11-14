/*
 * SmallestSpan.java
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
 * Defines a SmallestSpan comparator for variables. It prefers variables whose domain spans fewer
 * values, max - min + 1, holes included. It breaks the ties of {@link SmallestDomain} in the
 * variable selection {@code first_fail} of FlatZinc with {@code -Dorg.jacop.fz.firstFailTie=span}:
 * among the variables with the fewest values, those with the values closest together first, as
 * OR-Tools CP-SAT ranks the variables of {@code first_fail} (its {@code CHOOSE_MIN_DOMAIN_SIZE}
 * compares max - min + 1).
 *
 * @param <T> type of variable being used in the search.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class SmallestSpan<T extends IntVar> implements ComparatorVariable<T> {

  /** It constructs a SmallestSpan comparator. */
  public SmallestSpan() {
    // Intentionally empty: default constructor requires no initialization.
  }

  private static long span(IntVar v) {
    return (long) v.max() - v.min() + 1;
  }

  /**
   * Compares a metric value with a variable's span.
   *
   * @param left the metric value to compare.
   * @param v the variable to compare against.
   * @return positive if left has higher priority, negative if v has higher priority, 0 if equal.
   */
  public int compare(double left, T v) {
    return Double.compare((double) span(v), left);
  }

  /**
   * Compares two variables based on their spans. Variables with smaller spans have higher priority.
   *
   * @param leftVar the first variable to compare.
   * @param rightVar the second variable to compare.
   * @return positive if leftVar has higher priority, negative if rightVar has higher priority, 0 if
   *     equal.
   */
  public int compare(T leftVar, T rightVar) {
    return Long.compare(span(rightVar), span(leftVar));
  }

  /**
   * Computes the metric for a variable, its span max - min + 1.
   *
   * @param v the variable for which the metric is computed.
   * @return the span of the variable's domain.
   */
  public double metric(T v) {
    return (double) span(v);
  }
}
