/*
 * ImproveSolution.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.search.sgmpcs;

import org.jacop.core.Var;

/**
 * Defines an interface for defining different methods for selecting next search decision to be
 * taken. The search decision called choice point will be first enforced and later upon backtrack a
 * negation of that search decision will be enforced.
 *
 * @param <T> type of the variable for which choice point is being created.
 * @author krzysztof Kuchcinski
 * @version 4.10
 */
public interface ImproveSolution<T extends Var> {

  /**
   * Searches for a solution starting from an empty initial state.
   *
   * @param failLimit the maximum number of failures allowed during search.
   * @return true if a solution was found, false otherwise.
   */
  boolean searchFromEmptySolution(int failLimit);

  /**
   * Searches for a solution starting from the given elite solution.
   *
   * @param solution the elite solution to start the search from.
   * @param failLimit the maximum number of failures allowed during search.
   * @return true if an improved solution was found, false otherwise.
   */
  boolean searchFromEliteSolution(int[] solution, int failLimit);

  /**
   * Returns the cost of the current best solution.
   *
   * @return the current solution cost.
   */
  int getCurrentCost();

  /**
   * Returns the current best solution as an array of variable values.
   *
   * @return the solution values.
   */
  int[] getSolution();

  /**
   * Returns the number of failures encountered during the last search.
   *
   * @return the number of fails.
   */
  int getNumberFails();

  /**
   * Returns the fail limit used in the last search.
   *
   * @return the fail limit.
   */
  int getFailLimit();

  /**
   * Enables or disables printing of search information.
   *
   * @param p true to enable printing, false to disable.
   */
  void setPrintInfo(boolean p);

  /**
   * Sets the time limit for the search.
   *
   * @param timeOut the timeout in milliseconds.
   */
  void setTimeOut(long timeOut);
}
