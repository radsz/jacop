/*
 * MonotoneDefinition.java
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
 * A constraint that defines one of its variables as a function of the others that is monotone in
 * each of them, such as {@code r = a /\ b}. Presolve's dual reductions read it: another variable
 * can move when the defined variable can follow it.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public interface MonotoneDefinition {

  /**
   * Returns the defined variable.
   *
   * @return the defined variable, or null if the constraint does not define one now (for example
   *     because it is fixed).
   */
  Var defined();

  /**
   * Tells how the defined variable depends on another variable of the constraint.
   *
   * @param v a variable of the constraint other than the defined one.
   * @return 1 if the defined value does not decrease when {@code v} increases, -1 if it does not
   *     increase, 0 if neither is known.
   */
  int monotonicity(Var v);
}
