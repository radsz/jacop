/*
 * SelectingViolation.java
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
 * A {@link Violation} that reads one variable of a list, the one an index variable selects (an
 * element constraint {@code list[index] = value}). Its violation changes with a variable of the
 * list only while the index selects that variable, so local search need not measure it again when
 * any other variable of the list moves: Comet's element invariant (Van Hentenryck and Michel,
 * Constraint-Based Local Search, MIT Press 2005, chapter 5).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface SelectingViolation extends Violation {

  /**
   * Returns the index variable.
   *
   * @return the variable whose value selects a variable of the list.
   */
  IntVar selector();

  /**
   * Returns the list the index selects from.
   *
   * @return the variables of the list, by position.
   */
  IntVar[] selectable();

  /**
   * Returns the value of the index that selects the first variable of the list; value {@code
   * firstSelector() + p} selects position p.
   *
   * @return the index value of position 0.
   */
  int firstSelector();

  /**
   * Returns the variables the violation reads whatever the index selects, other than the index.
   *
   * @return the other variables read always, such as the value of an element constraint.
   */
  IntVar[] alwaysRead();
}
