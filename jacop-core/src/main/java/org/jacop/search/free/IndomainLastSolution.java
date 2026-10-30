/*
 * IndomainLastSolution.java
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
package org.jacop.search.free;

import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.core.IntVar;
import org.jacop.search.Indomain;

/**
 * Solution-based phase saving (Demirović et al. 2018): the value a variable had in the last
 * solution, if it is still in its domain, otherwise the value of the wrapped heuristic. Before the
 * first solution it is the wrapped heuristic.
 *
 * <p>It is a {@link SearchMonitor}: add it to the {@link FreeSearch} it is used in, so that it sees
 * the solutions.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class IndomainLastSolution implements Indomain<IntVar>, SearchMonitor {

  private final IntVar[] vars;
  private final Indomain<IntVar> fallback;
  private final Map<IntVar, Integer> saved = new IdentityHashMap<>();

  /**
   * Creates the heuristic.
   *
   * @param vars the variables whose values are saved at each solution.
   * @param fallback the value heuristic used when there is no saved value in the domain.
   */
  public IndomainLastSolution(IntVar[] vars, Indomain<IntVar> fallback) {
    this.vars = vars.clone();
    this.fallback = fallback;
  }

  @Override
  public int indomain(IntVar v) {
    Integer value = saved.get(v);
    if (value != null && v.domain.contains(value)) {
      return value;
    }
    return fallback.indomain(v);
  }

  /**
   * Gives values as if they were those of a last solution, for example a solution found by local
   * search before the free search starts.
   *
   * @param hinted the variables.
   * @param values their values.
   */
  public void hint(IntVar[] hinted, int[] values) {
    for (int i = 0; i < hinted.length; i++) {
      saved.put(hinted[i], values[i]);
    }
  }

  @Override
  public void onSolution(FreeSearch search) {
    for (IntVar v : vars) {
      if (v.singleton()) {
        saved.put(v, v.value());
      }
    }
  }

  @Override
  public String toString() {
    return "IndomainLastSolution(" + fallback + ")";
  }
}
