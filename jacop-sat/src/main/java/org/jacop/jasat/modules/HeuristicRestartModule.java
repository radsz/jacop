/*
 * HeuristicRestartModule.java
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

package org.jacop.jasat.modules;

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.ConflictListener;

/**
 * A module that indicates if a restart would be useful now. Currently based on number of conflicts
 * since last restart. Each restart makes the next restart twice harder to reach.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class HeuristicRestartModule implements ConflictListener, BackjumpListener {

  // should we restart ?
  public boolean shouldRestart;

  // number of conflicts
  private long conflictCount;

  // number of conflicts needed to restart
  private long threshold;

  // factor to increase the threshold by
  private double thresholdIncreaseRate;

  /**
   * Called when a conflict is detected during solving.
   *
   * @param clause the clause that caused the conflict
   * @param level the decision level at which the conflict occurred
   */
  public void onConflict(MapClause clause, int level) {
    conflictCount++;

    if (conflictCount > threshold) {
      shouldRestart = true;
    }
  }

  /**
   * Called when the solver performs a backjump operation.
   *
   * @param oldLevel the decision level before the backjump
   * @param newLevel the decision level after the backjump
   */
  public void onBackjump(int oldLevel, int newLevel) {
    // Restart heuristic does not need to react to backjump; only onRestart is used.
  }

  /**
   * Called when the solver restarts from a given decision level.
   *
   * @param oldLevel the decision level from which the restart occurs
   */
  public void onRestart(int oldLevel) {
    // increase the number of conflicts needed to restart
    threshold = Math.round(threshold * thresholdIncreaseRate);

    // reset counter
    conflictCount = 0;
    shouldRestart = false;
  }

  /**
   * Initializes the heuristic restart module and registers it with the solver core.
   *
   * @param core the solver core instance
   */
  public void initialize(Core core) {
    conflictCount = 0;
    threshold = core.config.restartConflictThreshold;
    thresholdIncreaseRate = core.config.restartThresholdIncreaseRate;

    // register
    core.conflictModules[core.numConflictModules++] = this;
    core.restartModules[core.numRestartModules++] = this;
  }
}
