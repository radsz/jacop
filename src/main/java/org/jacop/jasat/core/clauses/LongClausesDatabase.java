/*
 * LongClausesDatabase.java
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
import java.util.Random;

import org.jacop.jasat.utils.Utils;

/*
 * TODO : code bcp, and maybe reuse watch node lists in some other databases
 */


/**
 * A pool of long clauses, implemented with two watched an blocking literals
 * to minimize cache misses.
 *
 * @author Radoslaw Szymanek
 * @version 4.5
 */

public final class LongClausesDatabase extends AbstractClausesDatabase {

    private static final int DEFAULT_INITIAL_NUMBER_OF_CLAUSES = 100;

    private static final int SIZE_OF_CLAUSE_CACHE = 8;

    // the index of the current empty slot.
    private int currentIndex = 0;

    // the pool of clauses
    private int[][] clauses = new int[DEFAULT_INITIAL_NUMBER_OF_CLAUSES][];

    // the small pool of literals of clauses that can be used for watching.
    private int[][] literalsCache = new int[DEFAULT_INITIAL_NUMBER_OF_CLAUSES][];

    public int addClause(int[] clause, boolean isModel) {
        // TODO : reuse empty slots ?
        assert clause.length > 2 * SIZE_OF_CLAUSE_CACHE;

        int newIndex = currentIndex++;

        // add the clause
        ensureSize(currentIndex);

        clauses[newIndex] = clause;
        literalsCache[newIndex] = pool.getNew(SIZE_OF_CLAUSE_CACHE);

        // find watches for this clause
        assert Math.abs(clause[0]) != Math.abs(clause[1]); // different watches
        addWatch(clause[0], newIndex);
        addWatch(clause[1], newIndex);

        // compute unique ID for the clause
        int clauseId = indexToUniqueId(newIndex);
        return clauseId;
    }

    /**
     * Put it one place so there is only one Random generator for the whole SAT solver.
     * TODO: Radek.
     */

    Random generator = new Random();

    public void assertLiteral(int literal) {

		/* get the watched clauses for this literal;
		 * for each such clause, find its state, and if needed, propagate,
		 * find a new watch or trigger conflict
		 */

        // get the current watched clauses for the variable
        assert literal != 0;
        int var = (literal < 0) ? -literal : literal;

        // The variable associated with the literal is not watching any clauses.
        if (watchLists.length <= var || watchLists[var] == null)
            return;

        assert watchLists[var] != null;
        int[] varClauses = watchLists[var];

        int positionOfFirstAvailablePlace = varClauses[0];

        // watched clauses
        for (int i = 1; i < positionOfFirstAvailablePlace; ++i) {

            int clauseIndex = varClauses[i];
            int[] cache = literalsCache[clauseIndex];
            int[] clause = clauses[clauseIndex];

            // is the literal the first or second watch ?
            int myWatchPos = (((cache[0] < 0) ? -cache[0] : cache[0]) == var ? 0 : 1);

            // get watches, and perform some checks
            int otherWatch = cache[1 - myWatchPos];
            int myWatch = cache[myWatchPos];

            assert Math.abs(myWatch) == var;
            assert otherWatch * myWatch != 0; // none is zero

			/*
			 *  updates watches, and see how the clause evolved. 
			 *  
			 *  The watch that no longer can watch unknown clause 
			 *  is substituted by another watch. 
			 */

            // clause is satisfied, because of the watch triggering this function.
            if (cache[myWatchPos] == literal)
                continue;
            // clause is satisfied, because of the other watch for this clause.
            if (isSatisfied(cache[otherWatch]))
                continue;

            // maybe watch replacement can be found in cache.
            for (int no = 2; no < SIZE_OF_CLAUSE_CACHE; no++) {
                if (isActiveOrSatisfied(cache[no])) {
                    varClauses[i] = varClauses[--positionOfFirstAvailablePlace];
                    varClauses[0] = positionOfFirstAvailablePlace;
                    addWatch(cache[no], clauseIndex);
                    cache[myWatchPos] = cache[no];
                    cache[no] = myWatch;
                    continue;
                }
            }

            // maybe watch replacement can be find in main clause array.
            // replace cache with new potential watches later on.
            int startingPosition = generator.nextInt(clause.length - 1);
            int currentPosition = startingPosition + 1;
            int right = cache.length - 1;

            while (currentPosition < clause.length) {

                if (right == 2)
                    break;

                if (isActiveOrSatisfied(clause[currentPosition]))
                    cache[right--] = clause[currentPosition];

                currentPosition++;

            }

            currentPosition = 0;
            while (currentPosition <= startingPosition) {

                if (right == 2)
                    break;

                if (isActiveOrSatisfied(clause[currentPosition]))
                    cache[right--] = clause[currentPosition];

                currentPosition++;

            }

            if (right == cache.length - 1) {

                // state = ClauseState.UNSATISFIABLE_CLAUSE;
                MapClause conflictClause = core.explanationClause;
                conflictClause.clear();
                int[] localClause = clauses[clauseIndex];
                conflictClause.addAll(localClause);
                core.triggerConflictEvent(conflictClause);

                break;

            }

            if (right == cache.length - 2) {
                if (isActive(cache[cache.length - 1])) {

                    // Unit propagation.

                    /**
                     * TODO: Radek, can we trigger propagation right away or should we wait until all watches are checked.
                     */
                    int clauseId = indexToUniqueId(clauseIndex);
                    core.triggerPropagateEvent(cache[cache.length - 1], clauseId);

                    continue;
                }
            }


            // watch replacement can be found in cache.
            for (int no = 2; no < SIZE_OF_CLAUSE_CACHE; no++) {
                if (isActiveOrSatisfied(cache[no])) {
                    varClauses[i] = varClauses[--positionOfFirstAvailablePlace];
                    varClauses[0] = positionOfFirstAvailablePlace;
                    addWatch(cache[no], clauseIndex);
                    cache[myWatchPos] = cache[no];
                    cache[no] = myWatch;
                    continue;
                }
            }


            throw new AssertionError("should not happen, bad int");


        } // clauseIterate

        // remember which clauses we watch from now
        if (positionOfFirstAvailablePlace == 1) {
            // recycle old watches
            pool.storeOld(watchLists[var]);
            watchLists[var] = null;
        }

    }

    public void removeClause(int clauseId) {
        // TODO Auto-generated method stub

    }

    public boolean canRemove(int clauseId) {
        // TODO Auto-generated method stub
        return false;
    }

    public MapClause resolutionWith(int clauseIndex, MapClause clause) {
        // TODO Auto-generated method stub
        return null;
    }

    public void backjump(int level) {
        // TODO Auto-generated method stub

    }

    public int rateThisClause(int[] clause) {

        if (clause.length > (SIZE_OF_CLAUSE_CACHE << 2))
            return CLAUSE_RATE_I_WANT_THIS_CLAUSE;
        else
            return CLAUSE_RATE_UNSUPPORTED;

    }

    public int size() {
        // TODO Auto-generated method stub
        return 0;
    }



    /**
     * be sure that the database can contain numberOfClauses clauses
     *
     * @param size the size of the database to be ensured
     */
    public void ensureSize(int size) {

        assert currentIndex <= clauses.length;
        assert size >= 0;

        if (size >= clauses.length) {
            int newSize = 2 * size; // take some safety margin
            clauses = Utils.resize(clauses, newSize, currentIndex);
            literalsCache = Utils.resize(literalsCache, newSize, currentIndex);
        }

    }


    /**
     * is the literal at position @param literalPos satisfied in current trail ?
     */
    private final boolean isSatisfied(int literal) {
        return trail.values[(literal < 0) ? -literal : literal] == literal;
    }


    /**
     * is the literal at position @param literalPos satisfied or active ?
     */
    private final boolean isActiveOrSatisfied(int literal) {

        int value = trail.values[(literal < 0) ? -literal : literal];
        return value == 0 || value == literal;

    }

    /**
     * is the literal at position @param literalPos satisfied or active ?
     */
    private final boolean isActive(int literal) {

        return trail.values[(literal < 0) ? -literal : literal] == 0;

    }



    //
    //
    //
    //
    //
    //	// the pool of watch list nodes
    //	private GenericMemoryPool<WatcherListNode> nodesPool =
    //		new GenericMemoryPool<WatcherListNode>(new WatcherListNode());
    //
    //	// watches for each variable (var => list of clauses)
    //	private HashMap<Integer, WatcherListNode> varWatches =
    //		new HashMap<Integer, WatcherListNode>();
    //
    //
    //
    //
    //
    //	/**
    //	 * Notify the watches that this literal is set, updating the watched clauses
    //	 * and propagating literals if pertinent. If a conflict occurs, the solver
    //	 * conflict Event will be triggered. This is the main part of unit
    //	 * propagation for the solver.
    //	 * @param literal	the literal that is being set
    //	 */
    //	@SuppressWarnings("unused")
    //	@Override
    //	public void assertLiteral(int literal) {
    //		/* get the watched clauses for this literal;
    //		 * for each such clause, find its state, and if needed, propagate,
    //		 * find a new watch or trigger conflict
    //		 */
    //
    //		// get the current watched clauses for the variable
    //		assert literal != 0;
    //		int var = Math.abs(literal);
    //		ensureSize(var);
    //		longEnsureVarWatch(var);
    //		WatcherListNode firstNode = varWatches.get(var);
    //		WatcherListNode node = firstNode;
    //
    //		if (node == null)	return;
    //
    //		// watched clauses
    //		clauseIterate:
    //		do {
    //			int clauseIndex = node.clauseIndex;
    //			// TODO !
    //			/*
    //			// is the literal the first or second watch ?
    //			int myWatchPos = (Math.abs(clause[0]) == var ? 0 : 1);
    //
    //			// get watches, and perform some checks
    //			int otherWatch = clause[1 - myWatchPos];
    //			int myWatch = clause[myWatchPos];
    //			assert Math.abs(myWatch) == var;
    //			assert otherWatch * myWatch != 0; // none is zero
    //			assert varWatchesClause(myWatch, clauseIndex);
    //			assert varWatchesClause(otherWatch, clauseIndex);
    //
    //			// the current watch must have been set
    //			assert ! isActive(clauseIndex, myWatchPos);
    //
    //			// updates watches, and see how the clause evolved
    //
    //			ClauseState state = updateWatches(clauseIndex);
    //
    //			// does myWatch still watch this clause ?
    //			if (clause[0] == myWatch || clause[1] == myWatch) {
    //				// yes, remember it
    //				newVarClauses[newVarClauses[0]++] = clauseIndex;
    //			}
    //
    //			// does otherWatch still watch this clause ?
    //			if (clause[0] != otherWatch && clause[1] != otherWatch) {
    //				// no, it must no watch it anymore
    //				removeVarWatch(otherWatch, clauseIndex);
    //				assert ! varWatchesClause(otherWatch, clauseIndex);
    //			}
    //
    //			// is clause[0] aware it watches this clause ?
    //			if (clause[0] != otherWatch && clause[0] != myWatch) {
    //				assert ! varWatchesClause(clause[0], clauseIndex);
    //				addVarWatch(clause[0], clauseIndex);
    //			}
    //
    //			// is clause[1] aware it watches this clause ?
    //			if (clause[1] != otherWatch && clause[1] != myWatch) {
    //				assert ! varWatchesClause(clause[1], clauseIndex);
    //				addVarWatch(clause[1], clauseIndex);
    //			}
    //			switch(state) {
    //			case SATISFIED_CLAUSE:
    //			case UNKNOWN_CLAUSE:
    //				continue clauseIterate;	// next watched clause
    //
    //			case UNSATISFIABLE_CLAUSE:
    //				// conflict ! the conflict event has already been triggered
    //
    //				// remember the watched clauses we did not examine
    //				int numOtherClauses = varClauses[0] - i - 1;
    //				System.arraycopy(varClauses, i+1, newVarClauses,
    //					newVarClauses[0], numOtherClauses);
    //				newVarClauses[0] += numOtherClauses;
    //
    //				// stop propagating through clauses
    //				break clauseIterate;
    //			}
    //			*/
    //			node = node.next;
    //		} while (node != null && node != firstNode); // clauseIterate
    //
    //	}
    //
    //
    //	@Override
    //	public void removeClause(int clauseId) {
    //		assert core.currentState == SolverState.UNKNOWN;
    //
    //		int clauseIndex = dbStore.uniqueIdToIndex(clauseId);
    //		assert clauseIndex < currentIndex;
    //
    //		// watches do not watch this clause anymore
    //		int watch0 = clauses[clauseIndex][0];
    //		int watch1 = clauses[clauseIndex][1];
    //		longRemoveVarWatch(watch0, clauseIndex);
    //		longRemoveVarWatch(watch1, clauseIndex);
    //
    //		// recycle int[] and
    //		pool.storeOld(clauses[clauseIndex]);
    //		clauses[clauseIndex] = null;
    //	}
    //
    //	@Override
    //	public boolean canRemove(int clauseId) {
    //		return true;
    //	}
    //
    //
    //	@Override
    //	public MapClause resolutionWith(int clauseId,
    //									MapClause clause) {
    //		int[] localClause = clauses[dbStore.uniqueIdToIndex(clauseId)];
    //
    //		for (int literal : localClause) {
    //			// resolution !
    //			if (clause.containsLiteral(-literal)) {
    //				clause.removeLiteral(-literal);
    //			} else {
    //				clause.addLiteral(literal);
    //			}
    //		}
    //		return clause;
    //	}
    //
    //	@Override
    //	public int rateThisClause(int[] clause) {
    //		if (clause.length == 1)
    //			return CLAUSE_RATE_UNSUPPORTED;
    //
    //		// give an average rate, this database is versatile
    //		return CLAUSE_RATE_AVERAGE;
    //	}
    //
    //
    //	@Override
    //	public int size() {
    //		return currentIndex;
    //	}
    //
    //
    //	@Override
    //	public String toString(String prefix) {
    //		StringBuilder builder = new StringBuilder();
    //		for (int clauseIndex = 0; clauseIndex < currentIndex; ++clauseIndex) {
    //			int[] clause = clauses[clauseIndex];
    //			// add prefix
    //			builder.append(prefix);
    //
    //			// add literals
    //			for (int i = 0; i < clause.length; ++i) {
    //				int literal = clause[i];
    //				builder.append(literal);
    //				builder.append(" ");
    //			}
    //			builder.append(0);	// to end the clause
    //			if (clauseIndex < currentIndex-1)
    //				builder.append('\n');
    //		}
    //
    //		return builder.toString();
    //	}
    //
    //
    //	/**
    //	 * returns to the given level, mainly by trying to find watches for all
    //	 * clauses in uglyClauses
    //	 */
    //	@Override
    //	public void backjump(int level) {
    //		assert level < core.currentLevel;
    //
    //
    //	}
    //
    //	// TODO !
    //	/**
    //	 * Finds as many watches as needed for this clause. It can trigger some
    //	 * events if the clause is unit or unsatisfiable in current trail.
    //	 * It does *NOT* update or use varWatches !
    //	 * @param clauseIndex	the clause index
    //	 * @return	the state of the clause
    //	 */
    //	private int updateWatches(int clauseIndex) {
    //		assert dbStore.uniqueIdToIndex(clauseIndex) == clauseIndex;
    //
    //		int nextPos = 0;	// the next interesting position to search watches
    //
    //		/*
    //		 * case when at least one watch is satisfied
    //		 */
    //
    //		// if at least one watch is useful, should be watch0
    //		if ((! 	isActiveOrSatisfied(clauseIndex, 0))
    //			&&  isActiveOrSatisfied(clauseIndex, 1)) {
    //			swap(clauseIndex, 0, 1);
    //		}
    //
    //		// if the clause is satisfied, by watch0
    //		if (isSatisfied(clauseIndex, 0)) {
    //
    //			// the watch1 is still active or satisfied, nothing to do !
    //			if (isActive(clauseIndex, 1) || isSatisfied(clauseIndex, 1)) {
    //				// both watches can be kept
    //			} else {
    //				// the second watch is obsolete
    //				int newWatchPos = nextSatisfiableLiteral(clauseIndex, 2);
    //				if (newWatchPos == -1) {
    //					// no active literal, find the last set literal
    //					// (clause[0] excluded)
    //					newWatchPos = lastSetLiteralPos(clauseIndex, 1);
    //				}
    //				assert newWatchPos > 0;
    //
    //				swap(clauseIndex, 1, newWatchPos);
    //			}
    //			return ClauseState.SATISFIED_CLAUSE;
    //		}
    //
    //
    //		/*
    //		 * case when no watch is satisfied
    //		 */
    //
    //		// find the first active watch. If impossible, trigger conflict
    //		if (isActive(clauseIndex, 0)) {
    //			nextPos = 1;
    //
    //		} else if (isActive(clauseIndex, 1)) {
    //			// swap two first literals
    //			nextPos = 2;
    //			swap(clauseIndex, 0, 1);
    //		} else {
    //			assert isUnsatisfied(clauseIndex, 0);
    //			assert isUnsatisfied(clauseIndex, 1);
    //
    //			// can we find a satisfiable literal ?
    //			int literalPos = nextSatisfiableLiteral(clauseIndex, 2);
    //			if (literalPos == -1) {
    //				// no active literal at all ! conflict.
    //
    //				assert isUnsatisfiable(clauseIndex);
    //
    //				MapClause conflictClause = core.explanationClause;
    //				conflictClause.clear();
    //				int[] clause = clauses[clauseIndex];
    //				conflictClause.addAll(clause);
    //				core.triggerConflictEvent(conflictClause);
    //
    //				// find watches that will be good when backjumping
    //				literalPos = lastSetLiteralPos(clauseIndex, 0);
    //				assert literalPos != -1;
    //				swap(clauseIndex, 0, literalPos);
    //				// to find the second highest literal, start at 1
    //				literalPos = lastSetLiteralPos(clauseIndex, 1);
    //				assert literalPos != -1;
    //				swap(clauseIndex, 1, literalPos);
    //
    //				return ClauseState.UNSATISFIABLE_CLAUSE;
    //			} else {
    //				// we found one such literal
    //
    //				assert isActiveOrSatisfied(clauseIndex, literalPos);
    //				swap(clauseIndex, 0, literalPos);
    //				nextPos = literalPos + 1;
    //			}
    //		}
    //
    //		// from now, we have one watch
    //		assert isActiveOrSatisfied(clauseIndex, 0);
    //
    //		// try to find another satisfiable literal
    //		int literalPos = nextSatisfiableLiteral(clauseIndex, nextPos);
    //
    //		// only one active literal, unit propagation
    //		if (literalPos == -1) {
    //			// is this literal active ? then, propagate it. else, the clause
    //			// is satisfied anyway
    //			if (isActive(clauseIndex, 0)) {
    //				int unitLiteral = clauses[clauseIndex][0];
    //				int clauseId = indexToUniqueId(clauseIndex);
    //				core.triggerPropagateEvent(unitLiteral, clauseId);
    //			}
    //
    //			// find another watch, false but suitable for backjumping
    //			literalPos = lastSetLiteralPos(clauseIndex, 1);
    //			assert isUnsatisfied(clauseIndex, literalPos);
    //			swap(clauseIndex, 1, literalPos);
    //
    //			return ClauseState.SATISFIED_CLAUSE;
    //		} else {
    //
    //			// we have another watch, set it
    //			assert isActiveOrSatisfied(clauseIndex, literalPos);
    //			swap(clauseIndex, 1, literalPos);
    //
    //			// is the clause satisfied or unknown ?
    //			if (isSatisfied(clauseIndex, 0) || isSatisfied(clauseIndex, 1))
    //				return ClauseState.SATISFIED_CLAUSE;
    //			else
    //				return ClauseState.UNKNOWN_CLAUSE;
    //		}
    //	}
    //
    //
    //	/**
    //	 * finds the last asserted literal of the clause, which will make a good
    //	 * watch literal in case of backjump. Slow.
    //	 * Precondition : every literal from startIndex to the end of the clause
    //	 * is set in the current trail.
    //	 * @param clauseIndex	the (index of the) clause
    //	 * @param startIndex	the start index. every literal on the left is ignored
    //	 * @return	the index of the last asserted literal in the right part of
    //	 * the clause
    //	 */
    //	private int lastSetLiteralPos(int clauseIndex, int startIndex) {
    //
    //		int[] clause = clauses[clauseIndex];
    //		assert startIndex < clause.length;
    //
    //		// find the set literal with the highest level
    //		int higherLevel = 0;
    //		int bestPos = startIndex;
    //		for (int i = startIndex; i < clause.length; ++i) {
    //			int literal = clause[i];
    //			int var = Math.abs(literal);
    //
    //			assert trail.isSet(var);
    //			int level = trail.getLevel(var);
    //
    //			if (level >= higherLevel) {
    //				bestPos = i;
    //				higherLevel = level;
    //			}
    //
    //		}
    //
    //		assert trail.isSet(Math.abs(clause[bestPos])) : "literal must be set";
    //		return bestPos;
    //	}
    //
    //
    //	/**
    //	 * finds the next active or satisfied literal in the clause,
    //	 * starting at startIndex
    //	 * @param clauseIndex	index of the clause
    //	 * @param startIndex	starting index, everything on the left is ignored
    //	 * @return				-1 if no such literal exists, the index of the
    //	 * first literal found otherwise
    //	 */
    //	private final int nextSatisfiableLiteral(int clauseIndex, int startIndex) {
    //
    //		int length = clauses[clauseIndex].length;
    //
    //		for (int i = startIndex; i < length; ++i) {
    //			if (isActiveOrSatisfied(clauseIndex, i))
    //				return i;
    //		}
    //		return -1;
    //	}
    //
    //	/**
    //	 * ensures that varWatches.get(var) will succeed with a correct content.
    //	 * @param var	the var we want to be able to add clauses to watch to
    //	 */
    //	private final void longEnsureVarWatch(int var) {
    //		assert var > 0;
    //
    //		// be sure var is a key of the varWatches
    //		if (! varWatches.containsKey(var)) {
    //			varWatches.put(var, null);
    //		}
    //	}
    //
    //	/**
    //	 * predicate : is the literal at position @param watchPos still active, ie
    //	 * not set in the trail ?
    //	 * @param literalPos	the position of a literal in the clause
    //	 * @return	true if the watch is still useful
    //	 */
    //	private final boolean isActive(int clauseIndex, int literalPos) {
    //		assert literalPos >= 0;
    //		assert literalPos < clauses[clauseIndex].length;
    //
    //		int literal = clauses[clauseIndex][literalPos];
    //		int var = Math.abs(literal);
    //		int value = trail.values[var];
    //		return value == 0;
    //	}
    //
    //	/**
    //	 * predicate : is the literal at position @param literalPos unsatisfied in
    //	 * the current trail ?
    //	 * @param clauseIndex	the clause
    //	 * @param literalPos	the index of the literal to check
    //	 * @return	true if the current value of the literal is false in the trail
    //	 */
    //	private final boolean isUnsatisfied(int clauseIndex, int literalPos) {
    //		assert literalPos >= 0;
    //		assert literalPos < clauses[clauseIndex].length;
    //
    //		int literal = clauses[clauseIndex][literalPos];
    //		int var = Math.abs(literal);
    //		int value = trail.values[var];
    //		return value == -literal;
    //	}
    //
    //
    //	/**
    //	 * is the literal at position @param literalPos satisfied in current trail ?
    //	 */
    //	private final boolean isSatisfied(int clauseIndex, int literalPos) {
    //		assert literalPos >= 0;
    //		assert literalPos < clauses[clauseIndex].length;
    //
    //		int literal = clauses[clauseIndex][literalPos];
    //		int var = Math.abs(literal);
    //		int value = trail.values[var];
    //		return value == literal;
    //	}
    //
    //	/**
    //	 * is the literal at position @param literalPos satisfied or active ?
    //	 */
    //	private final boolean isActiveOrSatisfied(int clauseIndex, int literalPos) {
    //		assert literalPos >= 0;
    //		assert literalPos < clauses[clauseIndex].length;
    //
    //		int literal = clauses[clauseIndex][literalPos];
    //		int var = Math.abs(literal);
    //		int value = trail.values[var];
    //		return value == 0 || value == literal;
    //	}
    //
    //	/**
    //	 * predicate used for assertions. It checks if the clause is really
    //	 * unsatisfiable, the *slow* way.
    //	 * @param clauseIndex	the clause
    //	 * @return	true if all literals in the clause are false
    //	 */
    //	private final boolean isUnsatisfiable(int clauseIndex) {
    //		int[] clause = clauses[clauseIndex];
    //		for (int i = 0; i < clause.length; ++i) {
    //			int literal = clause[i];
    //			int var = Math.abs(literal);
    //			int value = trail.values[var];
    //			if (value != - literal)
    //				return false;
    //		}
    //		return true;
    //	}
    //
    //
    //	/**
    //	 * adds a watch (var => clause), ie make var watch clause
    //	 * @param literal		the watching literal
    //	 * @param clauseIndex	the index of clause to watch. Not a unique ID.
    //	 */
    //	private final void longAddVarWatch(int literal, int clauseIndex) {
    //		assert literal != 0;
    //		assert dbStore.uniqueIdToIndex(clauseIndex) == clauseIndex;
    //		assert ! varWatchesClause(literal, clauseIndex);
    //		int var = Math.abs(literal);
    //
    //		// get the watched clauses for the variable var
    //		longEnsureVarWatch(var);
    //		WatcherListNode oldNode = varWatches.get(var);
    //
    //		// get a new node for this var
    //		WatcherListNode curNode = getNewWatcherNode();
    //		curNode.clauseIndex = clauseIndex;
    //
    //		// manage pointers
    //		if (oldNode != null) {
    //			// if there is already a node in the list, insert this node
    //			if (oldNode.previous != null) {
    //				assert oldNode.next != null;
    //
    //				curNode.next = oldNode;
    //				curNode.previous = oldNode.previous;
    //				oldNode.previous = curNode;
    //				curNode.previous.next = curNode;
    //			} else {
    //				// only 2 elements
    //				curNode.next = curNode.previous = oldNode;
    //				oldNode.next = oldNode.previous = curNode;
    //			}
    //
    //		} else {
    //			// only node
    //			curNode.previous = curNode.next = null;
    //			varWatches.put(var, curNode);
    //		}
    //	}
    //
    //	/**
    //	 * removes the clause from the list of clauses that literal watches
    //	 * @param literal		the literal
    //	 * @param clauseIndex	the clause to remove
    //	 */
    //	private final void longRemoveVarWatch(int literal, int clauseIndex) {
    //		assert varWatchesClause(literal, clauseIndex);
    //
    //		int var = Math.abs(literal);
    //		WatcherListNode node = varWatches.get(var);
    //		assert node != null;
    //
    //		do {
    //			if (node.clauseIndex == clauseIndex) {
    //				// this is the good node !
    //				node.previous.next = node.next;
    //				node.next.previous = node.previous;
    //				break;
    //			} else {
    //				node = node.next;
    //			}
    //		} while(true);	// if literal does not watch clauseIndex, loop forever...
    //
    //		assert !varWatchesClause(literal, clauseIndex);
    //	}
    //
    //
    //
    //	/**
    //	 * @returns a new WatcherListNode, with null pointers
    //	 */
    //	private final WatcherListNode getNewWatcherNode() {
    //		WatcherListNode node = nodesPool.getNew();
    //		if (node == null) 	node = new WatcherListNode();
    //		return node;
    //	}
    //
    //
    //	/**
    //	 * swaps the two literals at i and j in the clause
    //	 * @param clauseIndex	the index of the clause
    //	 */
    //	private final void swap(int clauseIndex, int i, int j) {
    //		if (i == j)
    //			return;
    //
    //		int[] clause = clauses[clauseIndex];
    //		int temp = clause[i];
    //		clause[i] = clause[j];
    //		clause[j] = temp;
    //	}
    //
    //	/**
    //	 * watcher list, i.e. the list of clauses a literal watches.
    //	 * This is a node of such double-linked list.
    //	 * @author simon
    //	 *
    //	 */
    //	private class WatcherListNode implements Factory<WatcherListNode> {
    //
    //		public WatcherListNode previous;
    //		public WatcherListNode next;
    //
    //		// the element of the list
    //		public int clauseIndex;
    //
    //		// some literals from the clause
    //		@SuppressWarnings("unused")	// TODO : work on watche list nodes
    //		public int[] blockingLiterals;
    //
    //		@Override
    //		public WatcherListNode newInstance() {
    //			return new WatcherListNode();
    //		}
    //	}
    //

    @Override public void toCNF(BufferedWriter output) throws IOException {
        throw new UnsupportedOperationException("Not supported yet.");
    }

}
