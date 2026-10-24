/*
 * SearchMonitor.java
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

package org.jacop.search.free;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * Receives the events of a {@link FreeSearch}. Learning heuristics (weighted degree, last conflict,
 * phase saving) implement it to update their state; all methods do nothing by default.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface SearchMonitor {

  /**
   * Called when the search starts, after the initial propagation at the root succeeded.
   *
   * @param search the search.
   */
  default void onStart(FreeSearch search) {}

  /**
   * Called after a decision has been taken on a variable, before propagation. The left branch is
   * {@code var = value}, the right branch {@code var != value}.
   *
   * @param var the variable of the decision.
   * @param value the value of the decision.
   * @param left true for the left branch, false for the right branch.
   */
  default void onDecision(Var var, int value, boolean left) {}

  /**
   * Called after a decision has been taken on a constraint, before propagation. The left branch
   * imposes the constraint, the right branch its negation.
   *
   * @param choice the constraint of the decision.
   * @param left true for the left branch, false for the right branch.
   */
  default void onDecision(PrimitiveConstraint choice, boolean left) {}

  /**
   * Called when propagation fails.
   *
   * @param failed the constraint whose propagation failed, or null when the failure did not come
   *     from a constraint (for example the objective bound).
   * @param decision the variable of the decision that led to the failure, or null when the failure
   *     happened at the root or after a constraint decision.
   */
  default void onFailure(Constraint failed, Var decision) {}

  /**
   * Called when a run ends and the search restarts from the root.
   *
   * @param search the search.
   */
  default void onRestart(FreeSearch search) {}

  /**
   * Called when a solution is found, with the store in the solution state.
   *
   * @param search the search.
   */
  default void onSolution(FreeSearch search) {}
}
