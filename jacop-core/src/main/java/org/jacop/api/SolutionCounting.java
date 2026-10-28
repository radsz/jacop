/*
 * SolutionCounting.java
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
package org.jacop.api;

import org.jacop.core.IntVar;

/**
 * Extra functionality of a constraint: it counts its solutions over the current domains, projected
 * on a subset of its variables. Presolve uses the count to measure how tight the constraint is on
 * those variables, the fraction of their tuples that extend to a solution.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public interface SolutionCounting {

  /**
   * Counts the tuples of the current domains of {@code subset} that extend to a solution of the
   * constraint over the current domains of its other variables.
   *
   * @param subset some of the constraint's variables, without repetition; the others are projected
   *     out.
   * @param work most elementary steps the count may take.
   * @return the natural logarithm of the count, {@link Double#NEGATIVE_INFINITY} if there is no
   *     solution, or {@link Double#NaN} if the count would take more than {@code work} steps.
   */
  double logSolutions(IntVar[] subset, long work);
}
