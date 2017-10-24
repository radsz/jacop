/*
 * BackjumpListener.java
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
package org.jacop.jasat.modules.interfaces;

import org.jacop.jasat.core.SolverComponent;

/**
 * interface for components that listen for backjumps, or restarts
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */
public interface BackjumpListener extends SolverComponent {

    /**
     * Called when the solver backtracks. It will also be called when the
     * solver restarts.
     *
     * components that want to be warned about backjumps should
     * put themselves in Core.backjumpModules.
     * @param oldLevel  the level at which the solver was before backtracking
     * @param newLevel  the level to which the solver backtracks
     */
    void onBackjump(int oldLevel, int newLevel);



    /**
     * called when the solver restarts.
     *
     * components that want to be warned about restarts should
     * put themselves in Core.restartModules.
     * @param oldLevel the level at which the solver was before restarting
     */
    void onRestart(int oldLevel);

}
