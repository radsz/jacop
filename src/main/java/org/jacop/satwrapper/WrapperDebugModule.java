/*
 * WrapperDebugModule.java
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

package org.jacop.satwrapper;

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
 * a class used to debug, but with additional data
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public final class WrapperDebugModule
    implements AssertionListener, BackjumpListener, ConflictListener, PropagateListener, SolutionListener, ForgetListener,
    ExplanationListener, ClauseListener, StartStopListener, WrapperComponent {

    private Core core;
    private MapClause mapClause = new MapClause();

    // the associate wrapper
    private SatWrapper wrapper;


    public void onRestart(int oldLevel) {
        printLine(true);
        core.logc(3, "restart from level %d <=> CP level %d", oldLevel, wrapper.store.level);
        printLine(false);
        printBlank();
    }


    public void onConflict(MapClause conflictClause, int level) {
        printLine(true);
        core.logc(3, "conflict at level " + level);
        core.logc("conflict clause : " + conflictClause + " meaning " + wrapper.showClauseMeaning(conflictClause));
        printLine(false);
        printBlank();
    }


    public void onBackjump(int oldLevel, int newLevel) {
        printLine(true);
        core.logc(3, "backjump from " + oldLevel + "( CP " + wrapper.satToCpLevels[oldLevel] + ") to " + newLevel + " (CP "
            + wrapper.satToCpLevels[newLevel] + ")");
        printLine(false);
        printBlank();
    }


    public void onAssertion(int literal, int level) {
        printLine(true);

        if (literal == 26 && level == 1)
            Thread.dumpStack();

        core.logc(3, "(at SAT level " + level + ", CP level " + wrapper.store.level + ") assertion : " + literal + " meaning " + wrapper
            .showLiteralMeaning(literal));
        printLine(false);
        printBlank();
    }


    public void onPropagate(int literal, int clauseId) {
        printLine(true);
        core.logc(3, "propagate at level %d literal %d meaning %s", core.currentLevel, literal, wrapper.showLiteralMeaning(literal));
        // very dirty hack
        if (core.dbStore.uniqueIdToDb(clauseId) == 0)
            core.logc(3, "cause: special database");
        else {
            mapClause.clear();
            core.dbStore.resolutionWith(clauseId, mapClause);
            core.logc(3, "cause: " + mapClause + " meaning " + wrapper.showClauseMeaning(mapClause));
        }
        printLine(false);
        printBlank();
    }


    public void onSolution(boolean satisfiable) {
        printLine(true);
        core.logc(3, "current level : " + core.currentLevel);
        int numOfSetVar = core.trail.size();
        core.logc(3, "number of set vars : " + numOfSetVar);
        core.logc(3, "solver state : " + core.currentState);
        printLine(false);
        printBlank();
    }


    public void onExplain(MapClause explanation) {
        printLine(true);
        core.logc("explanation clause : " + explanation + " meaning " + wrapper.showClauseMeaning(explanation));
        printTrail("var state :          ", explanation);
        printLine(false);
        printBlank();
    }


    public void onClauseAdd(int[] clause, int clauseId, boolean isModelClause) {
        String c = Utils.showClause(clause);
        mapClause.clear();
        mapClause.addAll(clause);
        core.logc(3,
            "add clause " + (isModelClause ? "(model) " : "(learnt) ") + c + " at level " + core.currentLevel + " meaning " + wrapper
                .showClauseMeaning(mapClause));

    }


    public void onClauseRemoval(int clauseId) {
        core.logc(3, "remove clause " + clauseId);
    }


    public void onForget() {
        printLine(true);
        core.logc(3, "forget() called");
        printLine(false);
        printBlank();
    }


    public void onStart() {
        printLine(true);
        core.logc(3, "solver started at " + core.getTime("start"));
        printLine(false);
        printBlank();
    }

    public void onStop() {
        printLine(true);
        core.logc(3, "solver stopped at " + core.getTime("stop"));
        printLine(false);
        printBlank();
    }

    private void printLine(boolean start) {
        if (start)
            core.logc(3, "/==================================");
        else
            core.logc(3, "\\==================================");
    }

    private void printBlank() {
        core.logc(3, "");
    }

    private void printTrail(String prefix, MapClause clause) {
        StringBuilder sb = new StringBuilder().append("[ ");
        for (int var : clause.literals.keySet()) {
            int value = core.trail.values[var];
            if (value >= 0)
                sb.append(' ');
            sb.append(value);
            sb.append(' ');
        }
        core.logc(3, prefix + sb.append(']'));
    }

    public void initialize(Core core) {
        this.core = core;

        core.assertionModules[core.numAssertionModules++] = this;
        core.backjumpModules[core.numBackjumpModules++] = this;
        core.conflictModules[core.numConflictModules++] = this;
        core.forgetModules[core.numForgetModules++] = this;
        core.propagateModules[core.numPropagateModules++] = this;
        core.restartModules[core.numRestartModules++] = this;
        core.solutionModules[core.numSolutionModules++] = this;
        core.explanationModules[core.numExplanationModules++] = this;
        core.clauseModules[core.numClauseModules++] = this;
        core.startStopModules[core.numStartStopModules++] = this;

        mapClause.clear();
        core.verbosity = 3;
    }


    public void initialize(SatWrapper wrapper) {
        this.wrapper = wrapper;
        initialize(wrapper.core);
    }

}
