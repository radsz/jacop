/*
 * AbstractClausesDatabase.java
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
import java.util.Arrays;

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.SolverComponent;
import org.jacop.jasat.core.Trail;
import org.jacop.jasat.utils.MemoryPool;
import org.jacop.jasat.utils.Utils;

/**
 *
 * This class specifies an abstract class for clauses pools. 
 *
 * Those databases must use a MemoryPool to allocate their structures. 
 *
 * All ClausesDatabases have access to the DatabasesStore they belong to, so that they can 
 * convert the clauses unique ID to their local clauses index, and conversely.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */

public abstract class AbstractClausesDatabase implements SolverComponent, ClauseDatabaseInterface {

    // some default values for clauses rates
    protected static final int CLAUSE_RATE_UNSUPPORTED = 0;

    protected static final int CLAUSE_RATE_LOW = 2;

    protected static final int CLAUSE_RATE_AVERAGE = 5;

    protected static final int CLAUSE_RATE_WELL_SUPPORTED = 8;

    protected static int CLAUSE_RATE_I_WANT_THIS_CLAUSE = 20;


    // the minimal size of (var => clauses) watches
    protected static final int MINIMUM_VAR_WATCH_SIZE = 10;

    // memory pool for fast int[] allocation/deallocation
    public MemoryPool pool;

    // trail
    public Trail trail;

    // main solver structure
    public Core core;

    // Databases store for clauseId <-> clauseIndex
    public DatabasesStore dbStore;

    // the index of this database in the store
    public int databaseIndex;

    /**
     * @TODO efficiency.
     *
     * Do we really need fix one way of expensive watchLists for all databases ?!?
     * BinaryClausesDatabase should have its own way of doing watched literals.
     *
     */

    /**
     *
     * The first dimension corresponds to the index of the variable for which the watches are stored.
     * The second index at position equal to 0 then it specifies the first free position to put index of next watched clause.
     * The second index at position equal to n then it specifies the clause index of the n-th watched clause.
     *
     */
    protected int[][] watchLists = new int[10][];

    /**
     * TODO: try with hashmap (and associate watches with signed literals
     * and not only vars, to examinate first clauses that may trigger a conflict
     */
    // the other way to have watches
    // protected IntHashMap<int[]> watches = new IntHashMap<int[]>();

    /**
     * Indicates how much this database is optimized for this clause. The
     * Database that gives the higher rank will get the clause.
     * @param clause a clause to rate
     * @return a non negative integer indicating how much the database is interested in this clause
     */
    public abstract int rateThisClause(int[] clause);

    /**
     * Called by the databaseStore, to inform the DatabasesStore of which
     * index it has.
     * @param index the index of the database
     */
    public final void setDatabaseIndex(int index) {
        this.databaseIndex = index;
    }

    /**
     * @return the index of this database in the DatabasesStore
     */
    public final int getDatabaseIndex() {
        return databaseIndex;
    }

    /**
     * gets an unique ID from a clause index in this clause database
     * @param clauseIndex  a local clause index
     * @return an unique ID
     */
    public final int indexToUniqueId(int clauseIndex) {
        return dbStore.indexesToUniqueId(clauseIndex, databaseIndex);
    }

    /**
     * gets a local index from the unique ID
     * @param clauseId  the unique Id
     * @return the index of the clause it corresponds to
     */
    public final int uniqueIdToIndex(int clauseId) {
        return dbStore.uniqueIdToIndex(clauseId);
    }

    /**
     * @param literal the literal to check
     * @param clauseIndex the clause id for checking
     * @return true if the literal watches the clause, false otherwise
     */
    protected final boolean doesWatch(int literal, int clauseIndex) {

        int var = Math.abs(literal);

        if (watchLists.length <= var || watchLists[var] == null)
            return false;

        int[] watchList = watchLists[var];
        for (int i = 1; i < watchList[0]; ++i) {
            if (watchList[i] == clauseIndex)
                return true;
        }

        return false;
    }

    /**
     * ensures that varWatches.get(var) will succeed with a correct content.
     * @param var  the var we want to be able to add clauses to watch to
     */
    protected final void ensureWatch(int var) {

        assert var > 0;

        // already has a watch-list
        if (watchLists.length > var && watchLists[var] != null)
            return;

        // create new int[]
        int[] watchList = pool.getNew(MINIMUM_VAR_WATCH_SIZE);
        watchList[0] = 1; // first empty slot = 1;

        // put it as value for var
        if (watchLists.length <= var) {
            int oldLength = watchLists.length;
            watchLists = Utils.resize(watchLists, 2 * var);
            Arrays.fill(watchLists, oldLength, watchLists.length, null);
        }

        watchLists[var] = watchList;

    }

    /**
     * adds a watch (var {@literal =>} clause), ie make var watch clause
     * @param literal    the watching literal
     * @param clauseIndex  the index of clause to watch. Not a unique ID.
     */
    protected final void addWatch(int literal, int clauseIndex) {

        assert literal != 0;
        assert dbStore.uniqueIdToIndex(clauseIndex) == clauseIndex;
        assert !doesWatch(literal, clauseIndex);

        int var = Math.abs(literal);
        // get the watched clauses for the variable var
        ensureWatch(var);

        int[] watchList = watchLists[var];

        assert watchList[0] <= watchList.length;
        assert watchList[0] > 0;

        // resize if too small
        if (watchList[0] == watchList.length) {
            int newSize = watchList.length * 2;
            watchList = Utils.resize(watchList, newSize, watchList.length, pool);
            watchLists[var] = watchList;
        }

        watchList[watchList[0]] = clauseIndex;
        watchList[0]++; // remember new empty slot

    }

    /**
     * removes the clause from the list of clauses that literal watches
     * @param literal    the literal
     * @param clauseIndex  the clause to remove
     */
    protected final void removeWatch(int literal, int clauseIndex) {

        /**
         * @TODO Efficiency check, improvement.
         *
         * removeWatch potentially expensive (linear), if it is called
         * one by one to remove all watches then it will be potentially
         * quadratic ;( instead of constant function to remove all watches.
         *
         */
        assert doesWatch(literal, clauseIndex);

        int var = Math.abs(literal);
        int[] watchList = watchLists[var];

        // find the index of the clause in the int[]. Start from the
        // right so that recently added clauses are found faster.
        for (int i = watchList[0] - 1; i > 0; --i) {
            if (watchList[i] == clauseIndex) {
                // this is the clause, remove it by putting the last
                // clause index here
                watchList[0]--;

                // this was the only clause the var watched
                if (watchList[0] == 1) {
                    pool.storeOld(watchList);
                    watchLists[var] = null;
                }

                // put the last element at this place
                swap(watchList, i, watchList[0]);
                break;
            }
        }

        assert !doesWatch(literal, clauseIndex);
    }

    /**
     * number of clauses in the database
     * @return the number of clauses in the database
     */
    public abstract int size();

    /**
     * prints the content of the database in a nice way, each line being
     * prefixed with
     * @param prefix prefix for printed line
     * @return a String representation of the database
     */
    public String toString(String prefix) {
        return prefix + toString();
    }

    /**
     * print the content of the Database in a nice way
     */
    @Override public final String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(getClass().getSimpleName()).append(" (with ");
        return sb.append(size()).append(')').toString();
    }

    public final void initialize(Core core) {
        this.core = core;
        this.trail = core.trail;
        this.pool = core.pool;
        this.dbStore = core.dbStore;

        // register this database
        dbStore.addDatabase(this);
    }

    /**
     * It creates a CNF description of the clauses stored in this database.
     * @param output it specifies the target to which the description will be written.
     */
    public abstract void toCNF(BufferedWriter output) throws java.io.IOException;

    /**
     * swaps the two literals at position i and j in the clause
     * @param clause  the clause
     * @param i      the position (index) of the first literal
     * @param j    the position of the second literal
     */
    protected final void swap(int[] clause, int i, int j) {
        //assert i >= 0 && j >= 0;
        if (i == j)
            return;

        int temp = clause[i];
        clause[i] = clause[j];
        clause[j] = temp;

    }



}
