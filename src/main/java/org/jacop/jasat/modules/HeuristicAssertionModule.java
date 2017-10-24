/*
 * HeuristicAssertionModule.java
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
import org.jacop.jasat.core.SolverComponent;
import org.jacop.jasat.core.Trail;

/**
 * module used to guide research by selecting the next literal to assert
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */
public final class HeuristicAssertionModule implements SolverComponent {

    // solver instance
    private Core core;

    // trail instance (from the solver)
    private Trail trail;

    // the activity count
    private ActivityModule activity;

    /**
     * this is the main heuristic function, which tries to guess which
     * literal is the most interesting to set now.
     * Can trigger SAT if no unset variable is found.
     * @return a literal with no current value. Polarity counts.
     */
    public int findNextVar() {

        int answer = 0;

        // using activity
        int var = activity.getLiteralToAssert();
        if (var != 0)
            return var;

        // the basic way, for remaining vars
        int maxVariable = core.getMaxVariable();
        for (var = 1; var <= maxVariable; ++var) {
            if (!trail.isSet(var)) {
                answer = var;
                break;
            }
        }

        if (answer == 0) {
            assert trail.size() == core.getMaxVariable();
            core.triggerSatEvent();
        }
        return answer;
    }



    public void initialize(Core core) {
        this.core = core;
        this.trail = core.trail;
    }


    public HeuristicAssertionModule(ActivityModule activity) {
        this.activity = activity;
    }

}
