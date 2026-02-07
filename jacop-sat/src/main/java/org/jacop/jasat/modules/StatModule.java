/*
 * StatModule.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.modules;

import java.util.TimerTask;
import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.AbstractClausesDatabase;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.interfaces.AssertionListener;
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.ClauseListener;
import org.jacop.jasat.modules.interfaces.ConflictListener;
import org.jacop.jasat.modules.interfaces.ForgetListener;
import org.jacop.jasat.modules.interfaces.PropagateListener;
import org.jacop.jasat.modules.interfaces.StartStopListener;

/**
 * Collects statistics about the solver.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.10
 */
public final class StatModule
    implements AssertionListener,
        BackjumpListener,
        ConflictListener,
        ForgetListener,
        ClauseListener,
        PropagateListener,
        StartStopListener {

  // indicates whether a thread should be run to print stats regularly
  private final boolean threaded;
  private Core core;
  private long numRestarts;
  private long numConflicts;
  private long numBackjumps;
  private long numAssertions;
  private long numForget;
  private long numClauseAdd;
  private long numLearntClauses;
  private long numClauseRemoved;
  private long numPropagate;
  // task to print regularly stats
  private TimerTask task;

  /**
   * Create a StatModule. It can schedule
   *
   * @param threaded true if threaded
   */
  public StatModule(boolean threaded) {
    this.threaded = threaded;
  }

  /**
   * Called when the solver restarts from a given decision level.
   *
   * @param oldLevel the decision level from which the restart occurs
   */
  public void onRestart(int oldLevel) {
    numRestarts++;
  }

  /**
   * Called when a conflict is detected during solving.
   *
   * @param clause the clause that caused the conflict
   * @param level the decision level at which the conflict occurred
   */
  public void onConflict(MapClause clause, int level) {
    numConflicts++;
  }

  /**
   * Called when the solver performs a backjump operation.
   *
   * @param oldLevel the decision level before the backjump
   * @param newLevel the decision level after the backjump
   */
  public void onBackjump(int oldLevel, int newLevel) {
    numBackjumps++;
  }

  /**
   * Called when a literal is asserted at a specific decision level.
   *
   * @param literal the literal being asserted
   * @param level the decision level at which the assertion occurs
   */
  public void onAssertion(int literal, int level) {
    numAssertions++;
  }

  /** Called when the solver performs a forget operation to remove learnt clauses. */
  public void onForget() {
    numForget++;
  }

  /**
   * Called when a literal is propagated through unit propagation.
   *
   * @param literal the literal being propagated
   * @param clauseId the identifier of the clause causing the propagation
   */
  public void onPropagate(int literal, int clauseId) {
    numPropagate++;
  }

  /**
   * Called when a new clause is added to the solver.
   *
   * @param clause the clause being added as an array of literals
   * @param clauseId the unique identifier assigned to the clause
   * @param isModelClause true if the clause is from the original model, false if it is a learnt
   *     clause
   */
  public void onClauseAdd(int[] clause, int clauseId, boolean isModelClause) {
    numClauseAdd++;

    if (!isModelClause) {
      numLearntClauses++;
    }
  }

  /**
   * Called when a clause is removed from the solver.
   *
   * @param clauseId the identifier of the clause being removed
   */
  public void onClauseRemoval(int clauseId) {
    numClauseRemoved++;
  }

  /** Called when the solver stops its search process. */
  public void onStop() {
    // kill the thread
    if (task != null) {
      task.cancel();
    }

    // print stats
    logStats();
  }

  /** Called when the solver starts its search process. */
  public void onStart() {
    if (threaded) {
      task =
          new TimerTask() {
            @Override
            public void run() {
              logStats();
            }
          };

      // schedule this task regularly
      core.timer.schedule(task, 5000, 5000);
    }
  }

  /** Print current stats with solver's logc2 method. */
  public void logStats() {
    printBlank();
    printLine(true);

    long timeDiff = Math.max(core.getTimeDiff("start"), 1); // to avoid 0

    logStat("restarts", numRestarts, timeDiff);
    logStat("conflicts", numConflicts, timeDiff);
    logStat("assertions", numAssertions, timeDiff);
    logStat("backjumps", numBackjumps, timeDiff);
    logStat("forget", numForget, timeDiff);
    logStat("added clauses", numClauseAdd, timeDiff);
    logStat("learn clauses", numLearntClauses, timeDiff);
    logStat("removed clauses", numClauseRemoved, timeDiff);
    logStat("propagations", numPropagate, timeDiff);

    printBlank();

    // summary
    core.logc(2, "trail state: %d/%d", core.trail.size(), core.getMaxVariable());
    core.logc(2, "database store state: %d", core.dbStore.size());
    for (int i = 0; i < core.dbStore.currentIndex; i++) {
      AbstractClausesDatabase db = core.dbStore.databases[i];
      core.logc(2, "%s in state %d", db.getClass().getName(), db.size());
    }

    printLine(false);
    printBlank();
  }

  /** Logs one line of stat (for one parameter). */
  private void logStat(String stat, long num, long timeDiff) {
    core.logc(2, "%-20s: %-10s (%d/s)", stat, num, num * 1000 / timeDiff);
  }

  /** Prints a line, starting a block if @param start is true, ending the block otherwise. */
  private void printLine(boolean start) {
    if (start) {
      core.logc(2, "/==================================");
    } else {
      core.logc(2, "\\==================================");
    }
  }

  private void printBlank() {
    core.logc(2, "");
  }

  /**
   * Initializes the statistics module and registers it with the solver core for all relevant
   * events.
   *
   * @param core the solver core instance
   */
  public void initialize(Core core) {
    this.core = core;

    core.assertionModules[core.numAssertionModules++] = this;
    core.backjumpModules[core.numBackjumpModules++] = this;
    core.conflictModules[core.numConflictModules++] = this;
    core.forgetModules[core.numForgetModules++] = this;
    core.restartModules[core.numRestartModules++] = this;
    core.clauseModules[core.numClauseModules++] = this;
    core.propagateModules[core.numPropagateModules++] = this;
    core.startStopModules[core.numStartStopModules++] = this;
  }
}
