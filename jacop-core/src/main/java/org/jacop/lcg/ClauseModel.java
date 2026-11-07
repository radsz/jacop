/*
 * ClauseModel.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.lcg;

import org.jacop.core.IntVar;

/**
 * Clauses a constraint gives a lazy clause generation solver in its place: the solver then
 * propagates and explains the constraint by unit propagation over them, and the constraint itself
 * is not propagated. Literals are non-zero ints, negated by their sign.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface ClauseModel {

  /**
   * A new literal that stands for no atom of a variable, such as a node of a layered graph.
   *
   * @return its positive literal
   */
  int newLiteral();

  /**
   * The literal of {@code x = v}.
   *
   * @param x a variable that is not fixed
   * @param v a value of its domain
   * @return the literal
   */
  int valueLiteral(IntVar x, int v);

  /**
   * Adds a clause, which the solver may not keep in this array.
   *
   * @param literals the literals, one of which holds
   * @param size how many of the first literals form the clause
   */
  void clause(int[] literals, int size);
}
