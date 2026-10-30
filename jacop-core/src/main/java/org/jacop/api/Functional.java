/*
 * Functional.java
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

import java.util.function.ToIntFunction;
import org.jacop.core.IntVar;

/**
 * A constraint that gives the value of one of its variables as a function of the others, as {@code
 * value = list[index]} does for {@code value}. Local search keeps such a variable at the value of
 * the function when it is a defined variable of the model.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface Functional {

  /**
   * Returns the variable whose value the constraint gives.
   *
   * @return the variable.
   */
  IntVar functionalResult();

  /**
   * Returns the value of {@link #functionalResult()} for which the constraint holds, given the
   * values of its other variables.
   *
   * @param value the value of each other variable of the constraint.
   * @return the value of the result.
   */
  int functionalValue(ToIntFunction<IntVar> value);
}
