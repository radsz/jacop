/*
 * ConflictLearning.java
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

package org.jacop.jasat.core;

import org.jacop.jasat.core.clauses.DatabasesStore;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.utils.structures.IntStack;

/**
 * A solver component for conflict learning. (first UIP algorithm)
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */

public final class ConflictLearning implements SolverComponent {

    private Core core;

    // faster access to some objects
    private DatabasesStore dbStore;
    private Trail trail;

    /**
     * It computes to which level we should backjump to solve the conflict
     * explained by @param explanationClause
     *
     * @param explanationClause  used for backjumping computation
     * @return a level
     */
    public int getLevelToBackjump(MapClause explanationClause) {

        // this is a conflict, I hope
        assert core.currentState == SolverState.CONFLICT;
        assert core.currentLevel > 0 : "cannot backjump from level 0";
        // did we met the highest literal in the clause ?
        boolean firstOne = true;

        IntStack assertionStack = trail.assertionStack;
        // find the first asserted literal before the one in explainClause
        for (int i = assertionStack.size() - 1; i >= 0; --i) {
            int var = assertionStack.array[i];

            // this literal is in the clause
            if (explanationClause.containsVariable(var)) {
                // return the level of the second clause literal of the trail
                if (firstOne) {
                    // ok, we met the first, the next one is the good one
                    // core.logc(3,
                    // "ignore at level "+core.currentLevel+" var "+literal);
                    explanationClause.assertedLiteral = -trail.values[var];
                    firstOne = false;
                } else {
                    int level = trail.getLevel(var);
                    // core.logc(3, "at level "+level+ " var is unit "+literal);
                    return level;
                }
            }
        }

		/*
     * TODO: see if iterating over the clause would be more efficient
		 */

        // default case
        return 0;
    }

    /**
     * It builds the explanation clause made of all literals that were involved in
     * a conflict (ie which are in the clause and were asserted, or were
     * asserted and  triggered, in another clause, the propagation of a literal
     * present in the current clause)
     *
     * @param explanationClause  the SetClause we use, which must be initialized
     * to the conflict clause
     */
    public void applyExplainUIP(MapClause explanationClause) {

        assert !explanationClause.isEmpty();
        assert explanationClause.isUnsatisfiableIn(trail);

        // count how many literals from current level the clause contains
        int curLevel = core.currentLevel;
        int startingPosition = trail.size() - 1;

        IntStack assertionStack = trail.assertionStack;

        while (true) {

            // find the literal to resolve
            int lastLiteralPosition = findPositionTopLiteral(explanationClause, curLevel, startingPosition);
            // if none, abort
            if (lastLiteralPosition == -1) {
                explanationClause.backjumpLevel = getLevelToBackjump(explanationClause);
                return;
            }
            //throw new AssertionError("no literal of current level??");

            // resolve with its explanation
            applyExplain(explanationClause, assertionStack.array[lastLiteralPosition]);

            startingPosition = lastLiteralPosition - 1;
        }

		/*
		 * TODO : if the resulting clause is too complicated, use subsumption
		 * to get a simpler clause ?
		 */
    }

    /**
     * It gets the position of last set literal of the clause.
     *
     * @param explanationClause  the clause
     * @param level  the level of selectable literals
     * @return the last set literal of the clause, at current level, or 0 if none
     * has been found
     */
    private final int findPositionTopLiteral(MapClause explanationClause, int level, int startingPosition) {
        // TODO : improve perfs.

        for (int i = startingPosition; i >= 0; --i) {
            int var = trail.assertionStack.array[i];
            assert var > 0;

            assert trail.isSet(var);

            // we reached the asserted literal -- the first set in its level
            if (trail.isAsserted(var))
                return -1;
            // we passed under the level
            if (trail.getLevel(var) < level)
                return -1;

            // suitable literal, it is in the clause
            if (explanationClause.containsVariable(var))
                return i;

        }

        // none has been found
        return -1;
    }

    /**
     * performs one step of resolution for conflict explanation on given
     * explanation clause.
     * @param  explanationClause the explanation clause
     * @param  literal  the literal that must be resolved
     */
    private final void applyExplain(MapClause explanationClause, int literal) {
        assert explanationClause.containsVariable(literal);
        assert trail.isSet(Math.abs(literal));
        assert !trail.isAsserted(Math.abs(literal));

        // perform resolution
        int clauseId = trail.getExplanation(Math.abs(literal));
        dbStore.resolutionWith(clauseId, explanationClause);
    }

    public void initialize(Core core) {
        this.core = core;
        core.conflictLearning = this;
        this.dbStore = core.dbStore;
        this.trail = core.trail;
    }
}
