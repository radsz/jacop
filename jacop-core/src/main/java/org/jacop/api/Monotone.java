/*
 * Monotone.java
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

import org.jacop.core.Var;

/**
 * A constraint that tells in which directions each of its variables can move without making the
 * constraint false. Presolve's dual reductions read it; a constraint that does not implement it is
 * taken to forbid both directions for every variable.
 *
 * <p>Linear constraints need not implement it: presolve reads their linear form.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public interface Monotone {

  /** The variable can take any smaller value of its domain. */
  int DECREASE = 1;

  /** The variable can take any larger value of its domain. */
  int INCREASE = 2;

  /**
   * Returns the directions in which a variable can move: {@link #DECREASE} if every assignment of
   * the current domains that satisfies the constraint still satisfies it when only {@code v} takes
   * a smaller value of its domain, {@link #INCREASE} likewise for a larger value, both, or 0.
   *
   * @param v a variable of the constraint.
   * @return the directions, a combination of {@link #DECREASE} and {@link #INCREASE}.
   */
  int freeDirections(Var v);
}
