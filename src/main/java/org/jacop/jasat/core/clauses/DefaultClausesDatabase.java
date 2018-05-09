/*
 * DefaultClausesDatabase.java
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

/*
 * Radek:
 * TODO
 * Math.abs() is quite inefficient implementation, 
 * maybe there is some simple bit operation assuming 
 * that our ints will not be very close to the limit of int?
 * 
 * Simon:
 * we need the absolute value of literals in some places, and i do not know
 * a trivial bitwise operation that gives that... But if there is one, of course
 * it is worth replacing Math.abs()!
 *
 * Kris:
 * Replacing Math.abs() by direct code "(l < 0) ? -l : l" in program statements; not in assertions ;)
 */


/**
 *
 * A standard database of clauses, implemented in an efficient way such that insertion
 * or removal of clauses works fast.
 *
 * Two-watched literals are used for fast unit propagation. The two first
 * literals of each clauses are the watches.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */
public final class DefaultClausesDatabase extends AbstractClausesDatabase {

    /**
     *
     * @TODO efficiency.
     *
     * It accepts binary or longer clauses. 
     *
     * Should we assume that clauses are at least length 4? Does it make the code quicker? 
     *
     */
    private static final int DEFAULT_INITIAL_NUMBER_OF_CLAUSES = 100;
    // the array of clauses
    private int[][] clauses = new int[DEFAULT_INITIAL_NUMBER_OF_CLAUSES][];
    // the index of the current empty slot.
    private int currentIndex = 0;
    // number of removed clauses
    private int numRemoved = 0;

    /**
     * Notify the watches that this literal is set, updating the watched clauses
     * and propagating literals if pertinent. If a conflict occurs, the solver
     * conflict Event will be triggered. This is the main part of unit
     * propagation for the solver.
     *
     * It always creates a list of new watched list (newWatchedList).
     *
     * @param literal  the literal that is being set
     */
    public void assertLiteral(int literal) {

        assert trail.getLevel(Math.abs(literal)) == core.currentLevel;

        assert checkWatches4var(Math.abs(literal)) == null;

        /* get the watched clauses for this literal;
         * for each such clause, find its state, and if needed, propagate,
         * find a new watch or trigger conflict
         */

        // get the current watched clauses for the variable
        int var = (literal < 0) ? -literal : literal;
        if (watchLists.length <= var || watchLists[var] == null) {
            return;
        }

        // watched clauses for this literal
        int[] watchList = watchLists[var];
        // value of the literal in the trail
        int myValue = trail.values[var];
        assert myValue != 0;

        // new watched clauses[], to replace the current one after propagation
        int newSize = Math.max(watchList[0], MINIMUM_VAR_WATCH_SIZE);
        int[] newWatchList = pool.getNew(newSize);
        int newWatchNum = 1;

        // iterate on watched clauses
        IterateOnWatchedClauses:
        for (int i = 1, n = watchList[0]; i < n; ++i) {

            // the clause and its index
            int clauseIndex = watchList[i];

            int[] clause = clauses[clauseIndex];

            // is the literal the first or second watch ?
            int myWatchPos = (clause[0] == var || -clause[0] == var) ? 0 : 1;
            int myWatch = clause[myWatchPos];

            /*
             * case a1)  myWatch satisfies the clause, keep watching it and continue
             */
            if (myWatch == myValue) {
                newWatchList[newWatchNum++] = clauseIndex;
                continue IterateOnWatchedClauses;
            }

            // get the other watch and its value, and perform some checks
            int otherWatch = clause[1 - myWatchPos];
            int otherValue = trail.values[(otherWatch < 0) ? -otherWatch : otherWatch];

            assert Math.abs(myWatch) == var;
            assert otherWatch * myWatch != 0; // none is zero
            assert doesWatch(myWatch, clauseIndex);
            assert doesWatch(otherWatch, clauseIndex);

            /*
             * case a2)  clause satisfied by the other watch, keep watching it 
             * and go on with next clause
             */
            if (otherValue == otherWatch) {
                // keep the watch
                newWatchList[newWatchNum++] = clauseIndex;
                continue IterateOnWatchedClauses;
            }

            /*
             * case b)  both watches are wrong. Try to find 2 other
             */
            if (myValue == -myWatch && otherValue == -otherWatch) {

                /*
                 * try to find 2 other watches in the rest of the clause
                 */
                int watch1pos = -1;  // position (index) of first watch
                int watch2pos = -1;  // position of second watch
                int countWatches = 0;  // number of (real) watches found
        /*
                 * iterate until two watches are found or the whole clause is explored
                 */
                /**
                 * @TODO, Searching for new watches always starts from the beginning, 
                 * potentially very inefficient, should start from the last position
                 * or at least random position.
                 */
                for (int j = 2; j < clause.length && countWatches < 2; ++j) {

                    int lit = clause[j];
                    int value = trail.values[(lit < 0) ? -lit : lit];
                    if (value == 0) {
                        // new watch, remember it
                        if (countWatches == 0) {
                            watch1pos = j;
                        } else {
                            watch2pos = j;
                        }
                        countWatches++;

                    } else if (value == lit) {
                        /*
                         * case b1)  satisfiable, continue watching
                         * We are done with this clause
                         */
                        newWatchList[newWatchNum++] = clauseIndex;
                        continue IterateOnWatchedClauses;  // done with this clause
                    }
                }

                /*
                 * analyse results
                 */
                assert countWatches <= 2;
                switch (countWatches) {
                    case 0:
                        /*
                         * case b2)  unsatisfiable (conflict), keep both old watches, 
                         * trigger conflict and exit
                         */
                        newWatchList[newWatchNum++] = clauseIndex;
                        // trigger conflict
                        MapClause conflictClause = core.explanationClause;
                        conflictClause.clear();
                        conflictClause.addAll(clause);
                        assert conflictClause.isUnsatisfiableIn(trail);
                        core.triggerConflictEvent(conflictClause);
                        // copy remaining elements of watchList to the newWatchList
                        /**
                         * @TODO: What System.arraycopy for efficiency of copying the remaining elements?
                         */
                        for (int j = i + 1; j < watchList[0]; ++j) {
                            newWatchList[newWatchNum++] = watchList[j];
                        }
                        // stop iterating on watchList
                        break IterateOnWatchedClauses;

                    case 1:
                        /*
                         * case b3)  unit clause. We keep myWatch as a watch,
                         * because it is among the literals asserted at the very last
                         * level (the current level)
                         */
                        assert watch1pos != myWatchPos;
                        assert watch1pos >= 2;
                        assert trail.values[Math.abs(clause[watch1pos])] == 0;  // check unit clause
                        // keep watching it
                        newWatchList[newWatchNum++] = clauseIndex;

                        /*
                         * propagate the new first watch, because the clause is unit
                         */
                        int uniqueClauseId = indexToUniqueId(clauseIndex);
                        assert new MapClause(clause).isUnitIn(trail);
                        assert new MapClause(clause).isUnitIn(clause[watch1pos], trail);
                        core.triggerPropagateEvent(clause[watch1pos], uniqueClauseId);
                        continue IterateOnWatchedClauses;
                    case 2:
                        /* 
                         * case b4)  two new watches have been found. Forget about
                         * the two old watches, they are obsolete.
                         */
                        // put watches
                        swap(clause, 0, watch1pos);
                        swap(clause, 1, watch2pos);
                        // update the watch lists
                        /**
                         * @TODO, Analysis.
                         *
                         * Removing watch in this manner takes linear time to go through the list
                         * of watches, maybe this literal which is no longer capable of watching 
                         * is soon to be computed for assertion and operation check watch will be 
                         * performed anyway? 
                         */
                        removeWatch(otherWatch, clauseIndex); // we must remove the old watch
                        addWatch(clause[0], clauseIndex);
                        addWatch(clause[1], clauseIndex);
                        assert trail.values[Math.abs(clause[0])] == 0;
                        assert trail.values[Math.abs(clause[1])] == 0;
                        continue IterateOnWatchedClauses;
                    default:
                        throw new AssertionError("wrong case!");
                }
            }

            // the current literal should be the second watch, to simplify many things
            //			if (myWatchPos == 0) {
            //				swap(clause, 0, 1);
            //				myWatchPos = 1;
            //			}

            /*
             * case c)  Maybe unit clause, maybe unknown clause if another watch
             * can be found
             */
            assert otherValue == 0; // myValue cannot be 0, the literal has just been asserted
            // try to find another watch
            // iterate on all literals but the first (which is the unit literal, otherWatch)
            for (int j = 2; j < clause.length; ++j) {
                int lit = clause[j];
                int value = trail.values[(lit < 0) ? -lit : lit];
                if (value == 0 || value == lit) {
                    /*
                     * case c1)  a watch! burn! we have found another watch and
                     * thus, we do not need to watch this clause anymore.
                     */
                    /*
                     * case c2)  a satisfied literal. swap it with current literal
                     */
                    swap(clause, myWatchPos, j);
                    addWatch(lit, clauseIndex);
                    continue IterateOnWatchedClauses;

                }

            }

            /*
             * case c3) no watch has been found, this is a unit clause. We still
             * watch the clause (backjump), and we propagate the unit literal
             */
            // the literal still watches the clause (among highest level literals)
            newWatchList[newWatchNum++] = clauseIndex;
            // unit propagate the real watch (myWatch cannot be == 0)
            int uniqueClauseId = indexToUniqueId(clauseIndex);
            assert new MapClause(clause).isUnitIn(trail);
            core.triggerPropagateEvent(otherWatch, uniqueClauseId);

        } // IterateOnWatchedClauses

        /*
         * cleanup: put the new array of watched clauses in place of the old one
         */
        // remember which clauses we watch from now
        if (newWatchNum == 1) { // no clauses
            watchLists[var] = null;
            pool.storeOld(newWatchList); // useless because empty
        } else {
            assert newWatchNum > 1;
            // save the length of the array, and the array itself
            newWatchList[0] = newWatchNum;
            watchLists[var] = newWatchList;
        }

        // for (int c : watchList)
        //	assert checkWatches4Clause(c) == null;

        // recycle old watch list
        pool.storeOld(watchList);

        assert checkWatches4var(Math.abs(literal)) == null;

    }

    // TODO : reuse empty slots ?
    public int addClause(int[] clause, boolean isModel) {

        assert clause.length >= 2;

        int clauseIndex = currentIndex++;
        // compute unique ID for the clause
        int clauseId = indexToUniqueId(clauseIndex);

        // add the clause
        ensureSize(currentIndex);
        clauses[clauseIndex] = clause;

        /*
         * try to find the watches
         */

        int watch1pos = -1, watch2pos = -1;  // position of watches
        int highestPos = -1, highestLevel = -1;  // literal with highest level
        int secondHighestPos = -1, secondHighestLevel = -1; // literal with second highest level
        int numFoundWatch = 0; // how many watches did we found?
		/*
         * search for watches or literals asserted at current level
         */
        for (int i = 0; i < clause.length && numFoundWatch < 2; ++i) {
            int literal = clause[i];
            int value = trail.values[(literal < 0) ? -literal : literal];

            if (value == 0 || value == literal) {
                if (numFoundWatch == 1) {
                    // there is already one watch
                    watch2pos = i;
                } else {
                    assert numFoundWatch == 0;
                    watch1pos = i;
                }
                numFoundWatch++;
            } else {
                // falsified literal. Maybe it is interesting because of its level
                assert value == -literal;
                assert highestLevel >= secondHighestLevel;
                int level = trail.getLevel((literal < 0) ? -literal : literal);
                if (level >= highestLevel) {
                    // shift current, highest and second highest literals
                    secondHighestLevel = highestLevel;
                    secondHighestPos = highestPos;
                    highestLevel = level;
                    highestPos = i;
                } else if (level > secondHighestLevel) {
                    // replace second highest literal
                    secondHighestLevel = level;
                    secondHighestPos = i;
                }
            }
        } // loop


        switch (numFoundWatch) {
            /*
             * case b)  unknown clause, just add both watches.
             */
            case 2:
                assert watch1pos != watch2pos;
                putAt0And1(clause, watch1pos, watch2pos);
                break;
            /*
             * case c)  unit clause (we found exactly one unset literal),
             * add unit literal as first watch and highest set literal as
             * second watch
             */
            case 1:
                assert watch2pos == -1;
                putAt0And1(clause, watch1pos, highestPos);
                // trigger propagation of the first literal if not already fixed literal satisfying the clause.
                if (trail.values[(clause[0] < 0) ? -clause[0] : clause[0]] == 0)
                    ;
                core.triggerPropagateEvent(clause[0], clauseId);
                break;
            /*
             * case d)  conflict clause, just add the two highest literals
             * as watches and trigger conflict
             */
            case 0:
                assert highestPos != secondHighestPos;
                putAt0And1(clause, highestPos, secondHighestPos);
                // trigger conflict
                MapClause conflictClause = core.explanationClause;
                conflictClause.clear();
                conflictClause.addAll(clause);
                assert conflictClause.isUnsatisfiableIn(trail);
                core.triggerConflictEvent(conflictClause);
                break;

            default:
                throw new AssertionError("wrong number of found watches");
        }
        // anyway, add watches and return the ID
        addWatch(clause[0], clauseIndex);
        addWatch(clause[1], clauseIndex);

        assert (checkWatches4Clause(clauseIndex) == null);

        //for (int literal : clause)
        //	assert checkWatches4var(Math.abs(literal)) == null;

        return clauseId;
    }


    public void removeClause(int clauseIndex) {

        numRemoved++;

        // watches do not watch this clause anymore
        int watch0 = clauses[clauseIndex][0];
        int watch1 = clauses[clauseIndex][1];
        removeWatch(watch0, clauseIndex);
        removeWatch(watch1, clauseIndex);

        // recycle int[] and
        pool.storeOld(clauses[clauseIndex]);
        clauses[clauseIndex] = null;

    }


    public boolean canRemove(int clauseId) {
        return true;
    }


    public MapClause resolutionWith(int clauseId, MapClause explanation) {

        /**
         * TODO, clauseId is it already not unique general id, and just clause id within the database.
         */
        int[] clause = clauses[uniqueIdToIndex(clauseId)];

        for (int i = 0; i < clause.length; ++i) {
            int literal = clause[i];
            // resolution !
            // try to remove -literal. If it fails, add literal
            //if (! explanation.removeLiteral(-literal))
            //	explanation.addLiteral(literal);
            explanation.partialResolveWith(literal);

        }
        return explanation;
    }

    @Override public int rateThisClause(int[] clause) {

        if (clause.length <= 1) {
            return CLAUSE_RATE_UNSUPPORTED;
        }

        // give an average rate, this database is versatile
        return CLAUSE_RATE_AVERAGE;
    }

    @Override public int size() {
        return currentIndex - numRemoved;
    }

    /**
     * returns to the given level
     */

    public void backjump(int level) {
        // nothing to do
    }

    /**
     * (used for debug) checks if the 2 first literals of the clauses
     * are exactly the set of literals that watch this clause
     * @param clauseIndex  the index of the clause
     */
    @SuppressWarnings("unused") private String checkWatches4Clause(int clauseIndex) {
        int[] clause = clauses[clauseIndex];
        assert doesWatch(clause[0], clauseIndex);
        assert doesWatch(clause[1], clauseIndex);
        for (int j = 2; j < clause.length; ++j) {
            assert !doesWatch(clause[j], clauseIndex);
        }
        return null;
    }

    /**
     * (used for debug) checks if the 2 first literals of the clauses
     * are exactly the set of literals that watch this clause
     * @param clauseIndex  the index of the clause
     */
    @SuppressWarnings("unused") private String checkWatches4var(int var) {

        if (watchLists.length <= var) {
            return null;
        }

        int[] watchList = watchLists[var];

        if (watchList == null) {
            return null;
        }

        for (int i = 1, n = watchList[0]; i < n; ++i) {

            // the clause and its index
            int clauseIndex = watchList[i];
            int[] clause = clauses[clauseIndex];
            assert doesWatch(clause[0], clauseIndex);
            assert doesWatch(clause[1], clauseIndex);
            for (int j = 2; j < clause.length; ++j) {
                assert !doesWatch(clause[j], clauseIndex) :
                    "Too many watches on var " + var + " watches also on " + j + " " + new MapClause(clause).toString();
            }
        }

        return null;

    }

    /*
     * TODO: seriously improve performances. This code has been written to
     * be correct (because it is not that trivial and it is 2:30AM) but
     * it probably could be faster.
     */

    /**
     * assuming i != j, this modifies clause so that the elements
     * that were at position i and j will now be at position 0 and 1 (i.e.
     * clause[i] becomes clause[0] and clause[j] becomes clause[1])
     * @param clause  the clause to modify
     * @param i  the first index
     * @param j  the second index
     */
    private final void putAt0And1(int[] clause, int i, int j) {
        assert i >= 0 && i < clause.length;
        assert j >= 0 && j < clause.length;
        assert i != j;

        if (i > 1) {
            if (j > 1) {
                // no risk of collision
                swap(clause, 0, i);
                swap(clause, 1, j);
            } else {
                // i > 1, j is 0 or 1
                if (j == 0) {
                    swap(clause, 1, j);
                    swap(clause, 0, i);
                } else {
                    // j == 1
                    swap(clause, 0, i);
                }
            }
        } else if (j > 1) {
            // i is 0 or 1, j > 1
            if (i == 0) {
                swap(clause, 1, j);
            } else {
                swap(clause, 0, i);
                swap(clause, 1, j);
            }
        } else {
            // j and i are 0 and 1
            if (i == 0) {
                assert j == 1;
            } else {
                assert i == 1 && j == 0;
                swap(clause, 0, 1);
            }
        }
    }

    /**
     * be sure that the database can contain @param size clauses
     * @param size  the number of clauses
     */
    public void ensureSize(int size) {
        assert currentIndex <= clauses.length;
        assert size >= 0;

        if (size >= clauses.length) {
            int newSize = 2 * size; // take some safety margin
            clauses = Utils.resize(clauses, newSize, currentIndex);
        }
    }

    @Override public void toCNF(BufferedWriter output) throws IOException {

        for (int i = 0; i < currentIndex; i++) {

            int[] clause = clauses[i];

            if (clause != null) {

                for (int j = 0; j < clause.length; j++) {
                    output.write(Integer.toString(clause[j]));
                    output.write(" ");
                }
                output.write("0\n");
            }
        }

    }
}
