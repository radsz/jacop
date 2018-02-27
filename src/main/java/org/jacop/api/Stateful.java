/*
 * Stateful.java
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

package org.jacop.api;

/**
 * Interface to mark the need of an entity to receive information about level being removed.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */
public interface Stateful {

    /**
     * This function is called in case of the backtrack, so a constraint can
     * clear the queue of changed variables which is no longer valid. This
     * function is called *before* all timestamps, variables, mutablevariables
     * have reverted to their previous value.
     *
     * @param level the level which is being removed.
     */
    void removeLevel(int level);

    /**
     * This function can be overriden by any constraint to specify dynamic conditions (based on
     * the domain of variables at imposition level to decide if it is a stateful constraint.
     *
     * @return true if constraint is stateful.
     */
    default boolean isStateful() {
        return true;
    }

}
