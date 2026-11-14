/*
 * Violation.java
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
 * A constraint that measures how far given values of its variables are from satisfying it, without
 * changing any domain. Local search evaluates such constraints directly; others it evaluates by
 * propagating a copy.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface Violation {

  /**
   * Returns how much the constraint is violated when its variables take the given values: 0 when it
   * holds, otherwise a positive amount (1 for a constraint that has no measure of its own).
   *
   * @param value the value of each variable of the constraint.
   * @return the violation.
   */
  long violation(ToIntFunction<IntVar> value);
}
