/*
 * Entry.java
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

package org.jacop.presolve;

import org.jacop.core.Var;

/**
 * What a derivation did with one variable of the parent store, and so how postsolve gives it a
 * value.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public sealed interface Entry {

  /**
   * The variable has a counterpart in the child store; postsolve restricts the variable to the
   * counterpart's domain, its value once the child has a solution.
   *
   * @param copy the counterpart in the child store.
   */
  record Kept(Var copy) implements Entry {}

  /**
   * The variable is fixed in the parent at the level of the derivation and occurs in no constraint
   * of the child, so the child has no counterpart and postsolve leaves the value as it is.
   */
  record Fixed() implements Entry {}

  /**
   * The variable is neither fixed nor in a constraint, and it was not asked to be kept, so the
   * child has no counterpart; postsolve leaves its domain as it is, so it can take any value.
   */
  record Free() implements Entry {}

  /**
   * The variable occurred only in clauses that presolve removed: it is neither fixed nor in the
   * child, and postsolve gives it a value that satisfies the removed clauses.
   */
  record Eliminated() implements Entry {}
}
