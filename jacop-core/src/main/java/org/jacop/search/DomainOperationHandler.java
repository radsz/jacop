/*
 * DomainOperationHandler.java
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

import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Handler interface for type-specific domain operations in search algorithms. This interface allows
 * search classes to perform domain operations (inValue, inComplement, etc.) on different variable
 * types without directly depending on their concrete implementations.
 *
 * <p>Implementations of this interface should be provided by the respective modules: -
 * IntDomainOperationHandler in jacop-core - FloatDomainOperationHandler in jacop-floats (if needed)
 * - SetDomainOperationHandler in jacop-sets
 *
 * @author Generated for multi-module refactoring
 * @version 4.11
 */
public interface DomainOperationHandler {

  /**
   * Checks if this handler can process the given variable type.
   *
   * @param var the variable to check
   * @return true if this handler can process the variable, false otherwise
   */
  boolean isApplicable(Var var);

  /**
   * Assigns a specific value to the variable's domain. For IntVar: assigns the integer value. For
   * SetVar: adds the value to the GLB (Greatest Lower Bound) or LUB complement.
   *
   * @param store the store containing the variable
   * @param var the variable to assign
   * @param value the value to assign
   * @param leftBranch true if this is the left branch (for SetVar: use GLB), false for right branch
   */
  void inValue(Store store, Var var, int value, boolean leftBranch);

  /**
   * Removes a specific value from the variable's domain (complement operation). For IntVar: removes
   * the integer value. For SetVar: removes from GLB or adds to LUB complement.
   *
   * @param store the store containing the variable
   * @param var the variable to modify
   * @param value the value to remove
   * @param leftBranch true if this is the left branch (for SetVar: use LUB complement), false for
   *     right branch
   */
  void inComplement(Store store, Var var, int value, boolean leftBranch);

  /**
   * Gets a string representation of the variable's domain for display purposes.
   *
   * @param var the variable
   * @return string representation of the domain
   */
  String getDomainString(Var var);
}
