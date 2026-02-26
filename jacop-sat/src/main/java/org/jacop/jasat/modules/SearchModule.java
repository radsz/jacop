/*
 * SearchModule.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.TimerTask;
import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.SolverState;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.interfaces.ExplanationListener;
import org.jacop.jasat.modules.interfaces.SolutionListener;
import org.jacop.jasat.modules.interfaces.StartStopListener;

/**
 * A basic searching component, which controls the solver to solve the problem.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class SearchModule
    implements SolutionListener, ExplanationListener, StartStopListener {

  // the error margin for timeout. If time elapsed > timeout - TIME_MARGIN,
  // the search will stop. Written in milliseconds.
  private static final long TIME_MARGIN = 50;

  // the core instance
  public Core core;

  // tracks activity of literals
  public ActivityModule activity;

  // module used to choose literals based on activity
  public HeuristicAssertionModule assertionH;

  // module used to know if a restart is good
  public HeuristicRestartModule restartH;

  // timeout for search
  private long timeout;

  // used to stop search
  private boolean mustStop;

  // thread used for timeouts
  private TimerTask task;

  // next clause to learn
  private MapClause clauseToLearn;

  /** Search implementation, without timeout (search until solution is found). */
  public SearchModule() {
    // Default constructor; timeout and other fields are set by the solver.
  }

  /**
   * Called when a conflict explanation clause is generated.
   *
   * @param explanation the explanation clause derived from conflict analysis
   */
  public void onExplain(MapClause explanation) {
    clauseToLearn = explanation;
  }

  /**
   * Called when a solution is found or when the problem is determined to be unsatisfiable.
   *
   * @param solution true if a solution was found, false if the problem is unsatisfiable
   */
  public void onSolution(boolean solution) {
    mustStop = true;
  }

  /**
   * Perform search on the given solver, without limit of time. Must be called at most once after
   * initialize() was called.
   */
  public void onStart() {

    // setup timeout architecture
    if (timeout > 0) {
      core.logc("begin solving, time limit: %d ms", timeout);
      // in case of timeout, add a task to stop after the timeout
      initializeTask();
    } else {
      core.logc("begin solving, no time limit");
    }

    search();

    core.stop();
    core.logc("end solving");
  }

  /** Stops search. */
  public void onStop() {
    // cancel task
    if (task != null) {
      task.cancel();
    }
    mustStop = true;
  }

  /** Handles conflict state: restart or backjump. Returns new current level. */
  private int handleConflict(int currentLevel) {
    if (ASSERTS_ENABLED && !(core.currentLevel > 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (restartH.shouldRestart) {
      core.restart();
      if (ASSERTS_ENABLED && !(core.currentLevel == 0)) {
        throw new IllegalStateException("Assertion failed");
      }
      return core.currentLevel;
    }
    int bjLevel = core.getLevelToBackjump();
    if (ASSERTS_ENABLED && !(bjLevel < currentLevel)) {
      throw new IllegalStateException("Assertion failed");
    }
    core.backjumpToLevel(bjLevel);
    core.triggerIdleEvent();
    if (clauseToLearn != null) {
      core.triggerLearnEvent(clauseToLearn);
      clauseToLearn = null;
    }
    return core.currentLevel;
  }

  /** Main search loop. */
  private void search() {
    int currentLevel = 0;

    while (!mustStop) {
      if (core.currentState == SolverState.CONFLICT) {
        currentLevel = handleConflict(currentLevel);
      } else {
        currentLevel++;
        int nextLiteral = assertionH.findNextVar();
        if (nextLiteral == 0) {
          if (ASSERTS_ENABLED && !(core.hasSolution())) {
            throw new IllegalStateException("Assertion failed");
          }
          break;
        }
        core.assertLiteral(nextLiteral, currentLevel);
      }
    }
  }

  /** Creates a thread and runs it. */
  private void initializeTask() {

    // after a while, stop search
    task =
        new TimerTask() {
          @Override
          public void run() {
            core.stop();
            core.logc("timeout occurred");
          }
        };

    // schedule task for timeout
    long realTimeout = timeout - TIME_MARGIN;
    core.timer.schedule(task, realTimeout);
  }

  @Override
  public String toString() {
    return "SearchModule";
  }

  /**
   * Initializes the search module and registers it with the solver core.
   *
   * @param core the solver core instance
   */
  public void initialize(Core core) {
    timeout = core.config.timeout > 0 ? core.config.timeout : 0;

    // add itself to the Core
    this.core = core;
    core.search = this;

    // register for events
    core.solutionModules[core.numSolutionModules++] = this;
    core.explanationModules[core.numExplanationModules++] = this;
    core.startStopModules[core.numStartStopModules++] = this;

    // create heuristic and forget heuristic modules
    activity = new ActivityModule();
    assertionH = new HeuristicAssertionModule(activity);
    restartH = new HeuristicRestartModule();
    core.addComponent(activity);
    core.addComponent(assertionH);
    core.addComponent(restartH);
  }
}
