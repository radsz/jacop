/*
 * BasicPreprocessor.java
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

package org.jacop.jasat.utils;

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.utils.structures.IntVec;

/**
 * a basic preprocessor. It aims at removing trivial clauses
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public class BasicPreprocessor {

    // flag to indicate the status of the currently processed clause
    private final static int UNTOUCHED = 0;
    private final static int SIMPLIFIED = 1;
    private final static int TRIVIAL = 2;


    // the core this preprocessor will add clauses to
    private Core core;

    // local clause
    private MapClause localClause = new MapClause();

    /**
     * add a clause (just parsed from a file, e.g.) to the solver, after
     * processing
     *
     * @param clause clause to be added
     */
    public void addModelClause(IntVec clause) {

        // simplify the clause. If trivial, just return
        switch (simplifyClause(clause)) {
            case UNTOUCHED:
                core.addModelClause(clause);
                break;
            case SIMPLIFIED:
                core.addModelClause(localClause.toIntArray(core.pool));
                break;
            case TRIVIAL:
                break;  // do nothing
            default:
                throw new AssertionError("should not have this value");
        }
    }

    /**
     * simplify the clause by removing duplicates and checking for
     * triviality.
     *
     * @param clause the clause to simplify
     * @return the status of the clause (see at beginning)
     */
    private int simplifyClause(IntVec clause) {
        localClause.clear();
        // state of the clause
        int state = UNTOUCHED;

        for (int i = 0; i < clause.numElem; ++i) {
            int literal = clause.array[i];

            // trivial clause
            if (localClause.containsLiteral(literal))
                state = SIMPLIFIED;
            else if (localClause.addLiteral(literal))
                return TRIVIAL;
        }

        // clause is not trivial
        return state;
    }


    public BasicPreprocessor(Core core) {
        this.core = core;
    }

}
