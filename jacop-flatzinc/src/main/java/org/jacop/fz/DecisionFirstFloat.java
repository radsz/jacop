/*
 * DecisionFirstFloat.java
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

package org.jacop.fz;

import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import org.jacop.core.Var;
import org.jacop.search.ComparatorVariable;

/**
 * The variable choice of free search (-f) over float variables: the largest domain first, among the
 * variables of the model before the ones MiniZinc introduced for intermediate results
 * (var_is_introduced, is_defined_var). Splitting an intermediate result such as the exponential of
 * hart6 (declared var float, so of width 1e150) halves a range the model's own variables x1..x6 in
 * [0, 1] fix anyway: free search split it for 300 s without a solution, where the annotated search
 * on x1..x6 proves the optimum in 10 s.
 *
 * @param <T> the type of the variables
 */
final class DecisionFirstFloat<T extends Var> implements ComparatorVariable<T> {

  private final Set<Var> introduced = Collections.newSetFromMap(new IdentityHashMap<>());

  /**
   * Creates the comparator.
   *
   * @param introduced the variables chosen only once the other ones are fixed
   */
  DecisionFirstFloat(Collection<? extends Var> introduced) {
    this.introduced.addAll(introduced);
  }

  /**
   * The width of the domain for a variable of the model, and a value in (-1, 0) that grows with the
   * width for an introduced one, so that every variable of the model comes first.
   */
  @Override
  public double metric(T v) {
    double size = v.getSizeFloat();
    return introduced.contains(v) ? -1 / (1 + size) : size;
  }

  @Override
  public int compare(double left, T v) {
    return Double.compare(left, metric(v));
  }

  @Override
  public int compare(T leftVar, T rightVar) {
    return Double.compare(metric(leftVar), metric(rightVar));
  }
}
