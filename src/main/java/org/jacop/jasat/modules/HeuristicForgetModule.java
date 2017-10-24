/*
 * HeuristicForgetModule.java
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

import java.util.Iterator;
import java.util.LinkedList;

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.ExplanationListener;
import org.jacop.jasat.modules.interfaces.ForgetListener;



/*
 * TODO : finish the implementation
 */


/**
 * A component that selects clauses to forget when solver.forget() is called.
 * It may also call forget() after a restart.
 * Heuristic is from glucose.
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */
public final class HeuristicForgetModule implements ForgetListener, ExplanationListener, BackjumpListener {

    // after how many learnt clauses can we try to forget() ?
    public int LEARNT_CLAUSES_NUMBER_THRESHOLD = 1000;

    /**
     * threshold of activity under which a clause is removed
     */
    public double FORGET_THRESHOLD = 10;

    // solver instance
    private Core core;

    // lists of learnt clauses, indexed by their LBD
    @SuppressWarnings("unchecked") private LinkedList<Integer>[] learntClauses = (LinkedList<Integer>[]) new LinkedList[6];

    /**
     * When a forget() event occurs, this component will try to find clauses
     * that can be forgotten, i.e. that are :
     * - not very active (useless)
     * - not the explanation for a currently set literal
     */

    public void onForget() {
        assert core.currentLevel == 0;

        // delete at most half of the clauses
        int numClausesToRemove = core.dbStore.size() / 2;
        core.logc(2, "try to forget %d clauses...", numClausesToRemove);


        // only forget clauses with lbd greater than 2
        LBD:
        for (int lbd = 5; lbd > 2; --lbd) {
            Iterator<Integer> clauseIterator = learntClauses[lbd].iterator();
            while (clauseIterator.hasNext()) {
                if (numClausesToRemove <= 0)
                    break LBD;  // stop forgetting

                // try to remove this clause
                int clauseId = clauseIterator.next();
                if (core.canRemove(clauseId)) {
                    core.removeClause(clauseId);
                    clauseIterator.remove();
                    numClausesToRemove--;
                }
            }
        }
    }

    /**
     * when a restart occurs, it may be a good occasion to forget clauses
     */

    public void onRestart(int level) {
        if (shouldTriggerForget())
            core.forget();
    }



    public void onBackjump(int oldLevel, int newLevel) {
        throw new AssertionError("should not be called");
    }


    public void onExplain(MapClause explanation) {
        if (explanation.size() > 2) {
            // only try to remember clauses longer than 2

            int lbd = Math.min(computeLBD(explanation), learntClauses.length - 1);

            assert lbd > 0 && lbd < learntClauses.length;

            // TODO : try to bind it with the ID of the clause, because it
            // will be added soon
            // learntClauses[lbd].add(42);
        }
    }

    /**
     * should we forget now ? Will always return false if the current level
     * is not 0
     * @return true if the heuristic advises to forget AND the level is 0
     */
    public final boolean shouldTriggerForget() {
        return core.currentLevel == 0 && numberOfLearntClauses() > LEARNT_CLAUSES_NUMBER_THRESHOLD;
    }

    /**
     * @return the number of learnt clauses one can hope to delete
     */
    private int numberOfLearntClauses() {
        int answer = 0;
        for (int i = 0; i < learntClauses.length; ++i)
            answer += learntClauses[i].size();
        return answer;
    }

    /**
     * compute the LBD (Literal Block Distance) of a clause
     * @param clause  the clause
     * @return the LBD of this clause
     */
    private int computeLBD(MapClause clause) {
        // TODO : compute the number

        return 0;
    }



    public void initialize(Core core) {
        this.core = core;

        // reset lists of clauses
        for (int i = 0; i < learntClauses.length; ++i)
            learntClauses[i] = new LinkedList<Integer>();

        core.forgetModules[core.numForgetModules++] = this;
        core.explanationModules[core.numExplanationModules++] = this;
        core.restartModules[core.numRestartModules++] = this;
    }

}
