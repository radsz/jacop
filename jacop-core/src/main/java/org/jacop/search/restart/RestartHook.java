/*
 * RestartHook.java
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

package org.jacop.search.restart;

import org.jacop.core.Store;

/**
 * Code run by {@link RestartSearch} at the root of every run, as MiniZinc's {@code on_restart}
 * needs: it fixes variables whose values depend on the restart (the status of the last run, values
 * of the last solution, random values) before the search of the run starts.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public interface RestartHook {

  /** Status of the first run, and of every run until the first solution is found. */
  int START = 1;

  /** Status after a run that was cut by its fail limit without finding a solution. */
  int UNKNOWN = 2;

  /** Status after a run that explored its whole tree without finding a solution. */
  int UNSAT = 3;

  /** Status after a run that found a solution. */
  int SAT = 4;

  /**
   * Fixes the variables of the hook at the root of a run. It is called at the run's own store
   * level, so the changes are undone when the run ends.
   *
   * @param store the constraint store.
   * @param status the outcome of the last run, one of {@link #START}, {@link #UNKNOWN}, {@link
   *     #UNSAT} and {@link #SAT}.
   * @throws org.jacop.core.FailException if a value cannot be assigned.
   */
  void restart(Store store, int status);

  /** Records the values of a solution; called after each solution while it is assigned. */
  void solution();

  /**
   * Returns whether the model asked to end the search as complete. It is checked before each run.
   *
   * @return true if the search must stop and is complete.
   */
  boolean completeMarked();
}
