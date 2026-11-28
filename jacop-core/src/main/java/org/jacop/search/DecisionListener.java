/*
 * DecisionListener.java
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

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * Is told of each decision of a depth-first search before the search takes it, and can skip the
 * right branch of a decision. A decision is either a variable and a value (x = v on the left, x !=
 * v on the right) or a choice constraint (c on the left, not c on the right); the decision is taken
 * at the given store level, which the search removes before the right branch and again after it.
 *
 * @param <T> the type of the variables of the search.
 */
public interface DecisionListener<T extends Var> {

  /**
   * Executed before the left branch of a decision, at its level, before the search changes the
   * store.
   *
   * @param var the variable of the decision, or null for a choice constraint.
   * @param choice the choice constraint, or null for a decision on a variable.
   * @param level the store level of the decision.
   */
  void leftDecision(T var, PrimitiveConstraint choice, int level);

  /**
   * Executed before the right branch of a decision, at its level, before the search changes the
   * store.
   *
   * @param var the variable of the decision, or null for a choice constraint.
   * @param choice the choice constraint, or null for a decision on a variable.
   * @param level the store level of the decision.
   * @return false to skip the right branch, which then counts as a branch without a solution.
   */
  boolean rightDecision(T var, PrimitiveConstraint choice, int level);
}
