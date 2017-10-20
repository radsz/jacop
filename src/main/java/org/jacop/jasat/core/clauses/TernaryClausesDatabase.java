/*
 * TernaryClausesDatabase.java
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
 * A database for ternary clauses. It only accepts those.
 *
 * It does not work with watched literals. All literals are 
 * watching and if any of them changes then clause is being 
 * checked for unit propagation. 
 *
 * Pros : no need to change watches. 
 * Cons : need to check the clause every time any literal changes.
 *
 * TODO, check if this the efficient way of dealing with ternary clauses. 
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */

public final class TernaryClausesDatabase extends AbstractClausesDatabase {

    private static final int INITIAL_SIZE = 90;

    // the clauses
    private int[] clauses = new int[INITIAL_SIZE];

    // some util array
    private int[] curValues = new int[3];
    private int[] curLit = new int[3];

    // current clause index
    private int currentIndex = 0;

    // number of removed clauses
    private int numRemoved = 0;

    public int addClause(int[] clause, boolean isModel) {

        assert clause.length == 3;

        int clauseIndex = currentIndex++;
        int clauseId = indexToUniqueId(clauseIndex);

        int offset = 3 * clauseIndex;

        // resize if needed
        if (offset + 2 >= clauses.length) {
            int newSize = (offset + 2) * 2;
            clauses = Utils.resize(clauses, newSize, clauses.length, pool);
        }

        // set clause
        clauses[offset] = clause[0];
        clauses[offset + 1] = clause[1];
        clauses[offset + 2] = clause[2];

        // is clause unit, satisfied, satisfiable or conflict ?
        notifyClause(clauseIndex);

        // remember those vars watch this clause
        addWatch(clause[0], clauseIndex);
        addWatch(clause[1], clauseIndex);
        addWatch(clause[2], clauseIndex);

        return clauseId;
    }


    public void assertLiteral(int literal) {
        int var = (literal > 0) ? literal : -literal; //Math.abs(literal);

        if (watchLists.length <= var || watchLists[var] == null) {
            return;
        }

        // notify all clauses
        int[] clauses = watchLists[var];
        for (int i = 1; i < clauses[0]; ++i) {
            int clauseIndex = clauses[i];

            // notify this clause
            int state = notifyClause(clauseIndex);

            // conflict, abort
            if (state == ClauseState.UNSATISFIABLE_CLAUSE) {
                return;
            }
        }
    }


    public void removeClause(int clauseId) {
        int clauseIndex = dbStore.uniqueIdToIndex(clauseId);
        numRemoved++;

        // remove this clause from watched clauses
        int offset = clauseIndex * 3;
        removeWatch(clauses[offset], clauseIndex);
        removeWatch(clauses[offset + 1], clauseIndex);
        removeWatch(clauses[offset + 2], clauseIndex);

        clauses[offset] = 0;
        clauses[offset + 1] = 0;
        clauses[offset + 2] = 0;

    }

    public boolean canRemove(int clauseId) {
        return true;
    }


    public MapClause resolutionWith(int clauseId, MapClause clause) {
        int clauseIndex = dbStore.uniqueIdToIndex(clauseId);
        assert clauseIndex < currentIndex;
        assert clause.isUnsatisfiableIn(trail);

        int offset = clauseIndex * 3;

        for (int i = offset; i <= offset + 2; ++i) {
            int literal = clauses[i];
            // try to remove -literal. If it fails, add literal
            //if (! clause.removeLiteral(-literal))
            //	clause.addLiteral(literal);
            clause.partialResolveWith(literal);

        }
        return clause;
    }


    public void backjump(int level) {
        // nothing to do
    }

    @Override public int rateThisClause(int[] clause) {
        if (clause.length == 3) {
            return CLAUSE_RATE_I_WANT_THIS_CLAUSE;
        } else {
            return CLAUSE_RATE_UNSUPPORTED;
        }
    }

    /**
     * when something changed, find the status of the clause
     * @param clauseIndex  index of the clause
     * @return the state of the clause
     */
    private final int notifyClause(int clauseIndex) {

        int offset = clauseIndex * 3;

        int numUnknown = 0;    // number of literals not set

        // store current values and literals
        for (int i = 0; i < 3; ++i) {
            int literal = clauses[offset + i];
            int var = Math.abs(literal);
            curLit[i] = literal;
            int value = trail.values[var];

            if (value == literal) {
                return ClauseState.SATISFIED_CLAUSE;
            } else if (value == 0) {
                if (numUnknown == 1) {
                    return ClauseState.UNKNOWN_CLAUSE;
                } else {
                    numUnknown++;
                }
            }
            curValues[i] = value;
        }
        // neither unknown nor satisfied
        assert numUnknown <= 1;

        int clauseId = indexToUniqueId(clauseIndex);
        if (numUnknown == 0) {
            // conflict
            MapClause conflictClause = core.explanationClause;
            conflictClause.clear();
            conflictClause.addLiteral(clauses[offset]);
            conflictClause.addLiteral(clauses[offset + 1]);
            conflictClause.addLiteral(clauses[offset + 2]);
            core.triggerConflictEvent(conflictClause);
            return ClauseState.UNSATISFIABLE_CLAUSE;
        }

        for (int i = 0; i < 3; ++i) {
            if (curValues[i] == 0) {
                core.triggerPropagateEvent(curLit[i], clauseId);
                return ClauseState.SATISFIED_CLAUSE;
            }
        }

        throw new AssertionError("should not reach this point");
    }

    @Override public int size() {
        return currentIndex - numRemoved;
    }

    @Override public void toCNF(BufferedWriter output) throws IOException {

        for (int i = 0; i < currentIndex; i++) {
            int offset = i * 3;
            if (clauses[offset] != 0 && clauses[offset + 1] != 0 && clauses[offset + 2] != 0) {
                output.write(Integer.toString(clauses[offset]));
                output.write(" ");
                output.write(Integer.toString(clauses[offset + 1]));
                output.write(" ");
                output.write(Integer.toString(clauses[offset + 2]));
                output.write(" 0\n");
            }
        }

    }
}
