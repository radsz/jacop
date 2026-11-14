/*
 * SgmpcsCalculator.java
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

import lombok.Getter;
import lombok.Setter;
import org.jacop.search.ConsistencyListener;

/**
 * Defines interface for a calculator for restart search.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public abstract class Calculator implements ConsistencyListener {

  @Getter long numberFails;

  @Getter @Setter long failLimit;

  // whether the current run was stopped by its fail limit
  boolean limitReached;

  ConsistencyListener child;

  /** It computes and sets a new fail limit for the restart strategy. */
  public abstract void newLimit();

  /**
   * Starts the sequence of fail limits again from its first value, for example after a solution.
   * The default keeps the current limit.
   */
  public void reset() {
    startRun(failLimit);
  }

  /**
   * Starts a new run with the given fail limit.
   *
   * @param limit the number of failures the run may have.
   */
  final void startRun(long limit) {
    numberFails = 0;
    limitReached = false;
    failLimit = Math.max(0, limit);
  }

  /**
   * It is executed right after consistency of the current search node. The return code specifies if
   * the search should continue with or exit the current search node.
   */
  public boolean executeAfterConsistency(boolean consistent) {

    if (child != null) {
      child.executeAfterConsistency(consistent);
    }

    if (numberFails > failLimit) {
      // only a node that would otherwise be explored is cut by the limit
      limitReached |= consistent;
      return false;
    } else if (!consistent) {
      numberFails++;
    }

    return consistent;
  }

  /**
   * Checks if the current run was cut short by its fail limit. A run may have as many failures as
   * its limit; the search is stopped at the next node after one more failure, as in Gecode. A run
   * that explores its whole tree before that is complete.
   *
   * @return true if the run was stopped by the fail limit, false otherwise.
   */
  public boolean pointsExhausted() {
    return limitReached;
  }

  /**
   * Sets an array of children consistency listeners.
   *
   * @param children the array of consistency listeners to be set as children.
   */
  public void setChildrenListeners(ConsistencyListener[] children) {}

  /**
   * Sets a single child consistency listener.
   *
   * @param child the consistency listener to be set as a child.
   */
  public void setChildrenListeners(ConsistencyListener child) {
    this.child = child;
  }
}
