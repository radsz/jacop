/*
 * RemoveLevelLate.java
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

import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;

/**
 * Interface that provides ability to configure constraint store to replace a particular type of
 * constraints into another one.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public interface Replaceable<T extends Constraint> {

  /**
   * Returns the class type that this replaceable constraint handler is designed for.
   *
   * @return the constraint class type
   */
  Class<T> forClass();

  /**
   * Checks if the given constraint can be replaced.
   *
   * @param constraint the constraint to check
   * @return true if the constraint can be replaced, false otherwise
   */
  boolean isReplaceable(T constraint);

  /**
   * Replaces the constraint with a decomposed version.
   *
   * @param constraint the constraint to replace
   * @return the decomposed constraint
   */
  DecomposedConstraint<Constraint> replace(T constraint);
}
