/*
 * HeuristicRestartModule.java
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
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.ConflictListener;

/*
 * TODO: some idea about the heuristic:
 * do not decide to restart only depending on some variable and the number of
 * conflicts since the last restart; instead, use some "scheme".
 * 
 * This scheme would be :
 * 1) restart often (like, every 500 conflicts) for some
 * number of times N. This aims at finding good activities about literals.
 * 2) Then, perform a long run without restart (or maybe 2 runs ?), 
 * to try to reach a solution (too frequent restarts predate termination), 
 * like 2000 or 3000 conflicts at most.
 * 
 * If it fails, do the same thing with a slightly higher value of N.
 */

/**
 * A module that indicates if a restart would be useful now.
 * Currently based on number of conflicts since last restart. Each restart makes
 * the next restart twice harder to reach.
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */
public final class HeuristicRestartModule implements ConflictListener, BackjumpListener {

    // should we restart ?
    public boolean shouldRestart = false;

    // number of conflicts
    private long conflictCount = 0;

    // number of conflicts needed to restart
    private long threshold;

    // factor to increase the threshold by
    private double THRESHOLD_INCREASE_RATE;



    public void onConflict(MapClause clause, int level) {
        conflictCount++;

        if (conflictCount > threshold)
            shouldRestart = true;
    }


    public void onBackjump(int oldLevel, int newLevel) {
    }


    public void onRestart(int oldLevel) {
        // increase the number of conflicts needed to restart
        threshold = Math.round(threshold * THRESHOLD_INCREASE_RATE);

        // reset counter
        conflictCount = 0;
        shouldRestart = false;
    }


    public void initialize(Core core) {
        conflictCount = 0;
        threshold = core.config.RESTART_CONFLICT_THRESHOLD;
        THRESHOLD_INCREASE_RATE = core.config.RESTART_THRESHOLD_INCREASE_RATE;

        // register
        core.conflictModules[core.numConflictModules++] = this;
        core.restartModules[core.numRestartModules++] = this;
    }

}
