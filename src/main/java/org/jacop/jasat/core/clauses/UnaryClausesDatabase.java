/*
 * UnaryClausesDatabase.java
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

package org.jacop.jasat.core.clauses;

import java.io.BufferedWriter;
import java.io.IOException;

import org.jacop.jasat.utils.Utils;

/**
 * A database for unit clauses (length 1). It only accepts those.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */

public final class UnaryClausesDatabase extends AbstractClausesDatabase {

    /**
     * TODO: Radek, just curious
     *
     * how is the conflict raised by this database?
     * how is the propagation done? After clauses are added, how is the unit propagation taking place?
     *
     * => conflicts are only raised when a clause is added, because either
     * we propagate the only literal of the clause, either it is false (=> conflict)
     * However, a good question is: what if we add such a clause at level > 0
     * and some backjump goes under this level, maybe we should watch literals
     * after all. ==> FIXME
     *
     * Is the addClause a right place to do above? Would it cause troubles for consistency of state
     * of different components?
     *
     */
    private static final int INITIAL_SIZE = 100;

    // the clauses
    private int[] clauses = new int[INITIAL_SIZE];

    // current max index
    private int currentIndex = 0;

    // number of removed clauses
    private int numRemoved = 0;

    /**
     * TODO: Radek,
     *
     * why would you bother with having any code for removal when nothing is being actually removed.
     * Why not disallow removal altogether and call it StaticUnaryClausesDatabase?
     *
     */

    public int addClause(int[] clause, boolean isModel) {

        assert clause.length == 1;

        int newIndex = currentIndex++;
        int newId = indexToUniqueId(newIndex);

        // resize if needed
        if (newIndex >= clauses.length) {
            int newSize = newIndex * 2;
            clauses = Utils.resize(clauses, newSize, clauses.length, pool);
        }

        // set clause
        clauses[newIndex] = clause[0];

        // propagate the literal if it is not yet set
        int literal = clause[0];
        int var = (literal < 0) ? -literal : literal;
        int value = trail.values[var];
        if (value == 0)
            core.triggerPropagateEvent(literal, newId);
        else if (value == -literal) {
            MapClause conflictClause = core.explanationClause;
            conflictClause.clear();
            conflictClause.addLiteral(literal);
            core.triggerConflictEvent(conflictClause);
        } else
            assert value == literal;

        return newId;
    }


    public void removeClause(int clauseId) {
        assert clauseId < currentIndex;
        numRemoved++;
        clauses[clauseId] = 0;
        // nothing to do (not worthy to remember empty slots)
    }


    public boolean canRemove(int clauseId) {
        return true;
    }


    public MapClause resolutionWith(int clauseId, MapClause clause) {
        int clauseIndex = dbStore.uniqueIdToIndex(clauseId);
        assert clauseIndex < currentIndex;

        int literal = clauses[clauseIndex];
        // try to remove -literal. If it fails, add literal
        //if (! clause.removeLiteral(-literal))
        //	clause.addLiteral(literal);
        clause.partialResolveWith(literal);

        return clause;
    }



    public void backjump(int level) {
        // nothing to do
    }


    public void assertLiteral(int literal) {
        // nothing to do

        /**
         * TODO: Radek, Really nothing to do? What about checking that there is no conflict
         * with asserted literal?
         *
         * => literals are already asserted (all clauses here are unit clauses)
         */
    }

    @Override public int rateThisClause(int[] clause) {
        if (clause.length == 1)
            return CLAUSE_RATE_I_WANT_THIS_CLAUSE;
        else
            return CLAUSE_RATE_UNSUPPORTED;
    }

    @Override public String toString(String prefix) {
        StringBuilder sb = new StringBuilder().append("unary clause database\n");
        for (int i = 0; i < currentIndex; ++i)
            sb.append("[" + clauses[i] + "]\n");
        return sb.toString();
    }

    @Override public int size() {
        return currentIndex - numRemoved;
    }

    @Override public void toCNF(BufferedWriter output) throws IOException {

        for (int i = 0; i < currentIndex; i++) {
            int offset = i;
            if (clauses[offset] != 0) {
                output.write(Integer.toString(clauses[offset]));
                output.write(" 0\n");
            }
        }

    }

}
