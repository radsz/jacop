/*
 * DebugModule.java
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

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.interfaces.AssertionListener;
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.ClauseListener;
import org.jacop.jasat.modules.interfaces.ConflictListener;
import org.jacop.jasat.modules.interfaces.ExplanationListener;
import org.jacop.jasat.modules.interfaces.ForgetListener;
import org.jacop.jasat.modules.interfaces.PropagateListener;
import org.jacop.jasat.modules.interfaces.SolutionListener;
import org.jacop.jasat.modules.interfaces.StartStopListener;
import org.jacop.jasat.utils.Utils;

/**
 * Module used for debug : it logs every event it is informed of.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.10
 */
public final class DebugModule
    implements AssertionListener,
        BackjumpListener,
        ConflictListener,
        PropagateListener,
        SolutionListener,
        ForgetListener,
        ExplanationListener,
        ClauseListener,
        StartStopListener {

  private final MapClause mapClause = new MapClause();
  private Core core;

  /**
   * Called when the solver restarts from a given decision level.
   *
   * @param level the decision level from which the restart occurs
   */
  public void onRestart(int level) {
    printLine(true);

    core.logc(3, "restart from level %d", level);

    printLine(false);
    printBlank();
  }

  /**
   * Called when a conflict is detected during solving.
   *
   * @param conflictClause the clause that caused the conflict
   * @param level the decision level at which the conflict occurred
   */
  public void onConflict(MapClause conflictClause, int level) {
    printLine(true);

    core.logc(3, "conflict at level %d", level);
    printClause("conflict clause :", conflictClause);
    printTrail("var state:       ", conflictClause);
    printLine(false);
    printBlank();
  }

  /**
   * Called when the solver performs a backjump operation.
   *
   * @param oldLevel the decision level before the backjump
   * @param newLevel the decision level after the backjump
   */
  public void onBackjump(int oldLevel, int newLevel) {
    printLine(true);

    core.logc(3, "backjump from %d to %d", oldLevel, newLevel);

    printLine(false);
    printBlank();
  }

  /**
   * Called when a literal is asserted at a specific decision level.
   *
   * @param literal the literal being asserted
   * @param level the decision level at which the assertion occurs
   */
  public void onAssertion(int literal, int level) {
    printLine(true);

    core.logc(3, "(at level %d) assertion %d", level, literal);

    printLine(false);
    printBlank();
  }

  /**
   * Called when a literal is propagated through unit propagation.
   *
   * @param literal the literal being propagated
   * @param clauseId the identifier of the clause causing the propagation
   */
  public void onPropagate(int literal, int clauseId) {
    printLine(true);

    core.logc(3, "propagate literal %s", literal);

    printLine(false);
    printBlank();
  }

  /**
   * Called when a solution is found or when the problem is determined to be unsatisfiable.
   *
   * @param satisfiable true if a solution was found, false if the problem is unsatisfiable
   */
  public void onSolution(boolean satisfiable) {
    printLine(true);

    core.logc(3, "current level: %d", core.currentLevel);
    int numOfSetVar = core.trail.size();
    core.logc(3, "number of set vars: %d", numOfSetVar);
    core.logc(3, "solver state: %s", core.currentState);

    printLine(false);
    printBlank();
  }

  /**
   * Called when a conflict explanation clause is generated.
   *
   * @param explanation the explanation clause derived from conflict analysis
   */
  public void onExplain(MapClause explanation) {
    printLine(true);
    printClause("explanation clause : ", explanation);
    printTrail("var state :          ", explanation);

    printLine(false);
    printBlank();
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
    String c = Utils.showClause(clause);
    core.logc(3, "add clause (%s): %s", isModelClause ? "model" : "learnt", c);
  }

  /**
   * Called when a clause is removed from the solver.
   *
   * @param clauseId the identifier of the clause being removed
   */
  public void onClauseRemoval(int clauseId) {
    core.logc(3, "remove clause %d", clauseId);
  }

  /** Called when the solver performs a forget operation to remove learnt clauses. */
  public void onForget() {
    printLine(true);
    core.logc(3, "forget() called");
    printLine(false);
    printBlank();
  }

  /** Called when the solver starts its search process. */
  public void onStart() {
    printLine(true);
    core.logc(3, "solver started at %d", core.getTime("start"));
    printLine(false);
    printBlank();
  }

  /** Called when the solver stops its search process. */
  public void onStop() {
    printLine(true);
    core.logc(3, "solver stopped at %d", core.getTime("stop"));
    printLine(false);
    printBlank();
  }

  private void printLine(boolean start) {
    if (start) {
      core.logc(3, "/==================================");
    } else {
      core.logc(3, "\\==================================");
    }
  }

  private void printBlank() {
    core.logc(3, "");
  }

  private void printTrail(String prefix, MapClause clause) {
    StringBuilder sb = new StringBuilder(prefix).append("[ ");
    for (int var : clause.literals.keySet()) {
      int value = core.trail.values[var];
      if (value >= 0) {
        sb.append(' ');
      }
      sb.append(value);
      sb.append(' ');
    }
    core.logc(3, sb.append(']').toString());
  }

  private void printClause(String prefix, MapClause mapClause) {
    StringBuilder sb = new StringBuilder(prefix).append("[ ");
    for (int var : mapClause.literals.keySet()) {
      boolean pos = mapClause.literals.get(var);
      sb.append(pos ? ' ' : '-');
      sb.append(var);
      sb.append(' ');
    }
    core.logc(3, sb.append(']').toString());
  }

  /**
   * Initializes the debug module and registers it with the solver core for all relevant events.
   *
   * @param core the solver core instance
   */
  public void initialize(Core core) {
    this.core = core;

    core.assertionModules[core.numAssertionModules++] = this;
    core.backjumpModules[core.numBackjumpModules++] = this;
    core.conflictModules[core.numConflictModules++] = this;
    core.forgetModules[core.numForgetModules++] = this;
    core.propagateModules[core.numPropagateModules++] = this;
    core.solutionModules[core.numSolutionModules++] = this;
    core.explanationModules[core.numExplanationModules++] = this;
    core.clauseModules[core.numClauseModules++] = this;
    core.startStopModules[core.numStartStopModules++] = this;

    mapClause.clear();
  }
}
