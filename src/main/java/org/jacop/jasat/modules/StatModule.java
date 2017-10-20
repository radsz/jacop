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
 * collects statistics about the solver
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */
public final class StatModule
    implements AssertionListener, BackjumpListener, ConflictListener, ForgetListener, ClauseListener, PropagateListener, StartStopListener {

    private Core core;

    private long numRestarts = 0;

    private long numConflicts = 0;

    private long numBackjumps = 0;

    private long numAssertions = 0;

    private long numForget = 0;

    private long numClauseAdd = 0;

    private long numLearntClauses = 0;

    private long numClauseRemoved = 0;

    private long numPropagate = 0;

    // indicates whether a thread should be run to print stats regularly
    private final boolean threaded;

    // task to print regularly stats
    private TimerTask task = null;


    public void onRestart(int oldLevel) {
        numRestarts++;
    }


    public void onConflict(MapClause clause, int level) {
        numConflicts++;
    }


    public void onBackjump(int oldLevel, int newLevel) {
        numBackjumps++;
    }


    public void onAssertion(int literal, int level) {
        numAssertions++;
    }


    public void onForget() {
        numForget++;
    }


    public void onPropagate(int literal, int clauseId) {
        numPropagate++;
    }


    public void onClauseAdd(int[] clause, int clauseId, boolean isModelClause) {
        numClauseAdd++;

        if (!isModelClause)
            numLearntClauses++;
    }


    public void onClauseRemoval(int clauseId) {
        numClauseRemoved++;
    }


    public void onStop() {
        // kill the thread
        if (task != null)
            task.cancel();

        // print stats
        logStats();
    }


    public void onStart() {
        if (threaded) {
            task = new TimerTask() {
                @Override public void run() {
                    logStats();
                }
            };

            // schedule this task regularly
            core.timer.schedule(task, 5000, 5000);
        }

    }

    /**
     * print current stats with solver's logc2 method
     */
    public final void logStats() {
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
        for (int i = 0; i < core.dbStore.currentIndex; ++i) {
            AbstractClausesDatabase db = core.dbStore.databases[i];
            core.logc(2, "%s in state %d", db.getClass().getName(), db.size());
        }

        printLine(false);
        printBlank();
    }

    /**
     * logs one line of stat (for one parameter)
     */
    private final void logStat(String stat, long num, long timeDiff) {
        core.logc(2, "%-20s: %-10s (%d/s)", stat, num, num * 1000 / timeDiff);
    }

    /**
     * prints a line, starting a block if @param start is true, ending
     * the block otherwise
     */
    private void printLine(boolean start) {
        if (start)
            core.logc(2, "/==================================");
        else
            core.logc(2, "\\==================================");
    }

    private void printBlank() {
        core.logc(2, "");
    }

    /**
     * Create a StatModule. It can schedule
     * @param threaded true if threaded
     */
    public StatModule(boolean threaded) {
        this.threaded = threaded;
    }


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
