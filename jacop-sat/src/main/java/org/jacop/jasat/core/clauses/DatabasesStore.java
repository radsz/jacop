/*
 * DatabasesStore.java
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
import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.SolverComponent;
import org.jacop.jasat.core.SolverState;

/**
 * This provides a unique interface to several databases. It also translates clauses ids to get them
 * unique across the whole system. Databases have access to it, so that they can translate unique
 * clauses ids in both way.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.10
 */
public final class DatabasesStore implements SolverComponent, ClauseDatabaseInterface {

  // the databases
  public AbstractClausesDatabase[] databases;
  // the index of the first databases[] empty slot
  public int currentIndex;
  // solver instance
  public Core core;
  // how many clausesDatabases can we have ? must be a power of 2
  private int maxNumberOfDatabases = 8;
  // the mask to get the database index part
  private int databasesMask;
  // the mask to get the clause index part
  private int indexMask;
  // the number of bits to shift right a DATABASE_MASK to get a normal int
  private int indexMaskNumBits;
  // log_2 of the number of databases
  private int logOfNumDatabases;

  // compute values and check things
  private void initializeMasks() {
    int i = maxNumberOfDatabases >>> 1;
    while (i > 0) {
      logOfNumDatabases++;
      i = i >>> 1; // divide by 2
    }
    // check  2^{logOfNumDatabases} == maxNumberOfDatabases
    assert 1 << logOfNumDatabases == maxNumberOfDatabases
        : "number" + " of databases must be a power of 2";

    indexMask = Integer.MAX_VALUE >>> logOfNumDatabases;
    databasesMask = Integer.MAX_VALUE ^ indexMask;
    indexMaskNumBits = Integer.bitCount(indexMask);
    assert Integer.bitCount(indexMask) == Integer.SIZE - logOfNumDatabases - 1;
    assert Integer.bitCount(databasesMask ^ indexMask) == Integer.SIZE - 1;
  }

  public int addClause(int[] clause, boolean isModelClause) {

    assert currentIndex > 0 : "must be at least one DB";

    /*
     *  we do not simplify clauses by removing duplicates
     */

    // find which database gives the highest rate for this clause
    int winnerDatabaseIndex = 0;
    int maxRate = databases[0].rateThisClause(clause);
    for (int i = 1; i < currentIndex; i++) {
      int currentRate = databases[i].rateThisClause(clause);
      if (currentRate > maxRate) {
        winnerDatabaseIndex = i;
        maxRate = currentRate;
      }
    }

    // add the clause to winner DB
    AbstractClausesDatabase db = databases[winnerDatabaseIndex];

    return db.addClause(clause, isModelClause);
  }

  public boolean canRemove(int clauseId) {
    int dbIndex = uniqueIdToDb(clauseId);
    int clauseIndex = uniqueIdToIndex(clauseId);
    return databases[dbIndex].canRemove(clauseIndex);
  }

  /**
   * Removes this clause from the database it belongs to.
   *
   * @param clauseId the id of the clause to be deleted
   */
  public void removeClause(int clauseId) {
    if (canRemove(clauseId)) {
      // we can remove this clause
      int dbIndex = uniqueIdToDb(clauseId);
      int clauseIndex = uniqueIdToIndex(clauseId);
      databases[dbIndex].removeClause(clauseIndex);

    } else {
      core.logc(3, "tried to remove a clause (%d) from a DB that cannot", clauseId);
    }
  }

  public MapClause resolutionWith(int clauseId, MapClause clause) {

    // find the right DB, the index, and delegate
    int dbIndex = uniqueIdToDb(clauseId);
    int clauseIndex = uniqueIdToIndex(clauseId);
    return databases[dbIndex].resolutionWith(clauseIndex, clause);
  }

  /**
   * Adds a ClausesDatabase to the Store.
   *
   * @param database the database to add
   */
  public void addDatabase(AbstractClausesDatabase database) {
    assert currentIndex < maxNumberOfDatabases;

    databases[currentIndex] = database;
    database.setDatabaseIndex(currentIndex);
    database.dbStore = this;
    currentIndex++;
  }

  /** The number of clauses in all databases. */
  public int size() {
    int sum = 0;
    for (int i = 0; i < currentIndex; i++) {
      sum += databases[i].size();
    }

    return sum;
  }

  /**
   * Tells all databases to backjump at this level.
   *
   * @param level the level to backjump to
   */
  public void backjump(int level) {
    for (int i = 0; i < currentIndex; i++) {
      AbstractClausesDatabase db = databases[i];
      db.backjump(level);
    }
  }

  /**
   * Tells all databases that the literal is set, for unit propagation. Stops when all databases are
   * informed, or the solver has reached a stop-state
   *
   * @param literal the literal
   */
  public void assertLiteral(int literal) {
    // assert in all databases
    for (int i = 0; i < currentIndex; i++) {
      databases[i].assertLiteral(literal);

      if (core.currentState != SolverState.UNKNOWN) {
        return;
      }
    }
  }

  /**
   * Returns the ClausesDatabase associated with this clauseId.
   *
   * @param clauseId a unique clause Id
   * @return the index of the ClausesDatabase that contains the clause
   */
  public int uniqueIdToDb(int clauseId) {
    // is this >>> or >> ?
    int dbIndex = (clauseId & databasesMask) >>> indexMaskNumBits;
    assert dbIndex >= 0;
    assert dbIndex < currentIndex;
    int clauseIndex = uniqueIdToIndex(clauseId);
    assert indexesToUniqueId(clauseIndex, dbIndex) == clauseId;

    return dbIndex;
  }

  /**
   * Removes the database index of the clause, to get a real clause index. The normal way to use it
   * is together with getClausesDatabase(), so that we have both the good database and the real id
   * of the clause
   *
   * @param clauseId the unique clauseId
   * @return the clause index in the database
   */
  public int uniqueIdToIndex(int clauseId) {
    int index = clauseId & indexMask;
    assert index >= 0;

    return index;
  }

  /**
   * It gets a unique id from a clause index, relative to a database, and a database index.
   *
   * @param clauseIndex clause index
   * @param databaseIndex database index
   * @return unique id from a clause index
   */
  public int indexesToUniqueId(int clauseIndex, int databaseIndex) {
    assert databaseIndex < currentIndex;
    assert clauseIndex >= 0;
    assert databaseIndex >= 0;

    int clauseId = (databaseIndex << indexMaskNumBits) | clauseIndex;
    assert ((clauseId & databasesMask) >>> indexMaskNumBits) == databaseIndex;
    assert uniqueIdToIndex(clauseId) == clauseIndex;

    return clauseId;
  }

  @Override
  public String toString() {
    return "DatabaseStore (with " + currentIndex + " databases)";
  }

  public void initialize(Core core) {
    // interconnect components
    this.core = core;
    core.dbStore = this;

    maxNumberOfDatabases = core.config.maxNumberOfDatabases;
    databases = new AbstractClausesDatabase[maxNumberOfDatabases];
    currentIndex = 0;

    // computes bits sets and so on
    initializeMasks();
  }

  public void toCnf(BufferedWriter output) throws IOException {

    int noOfVariables = core.getMaxVariable();
    int noOfClauses = 0;

    for (AbstractClausesDatabase abstractClausesDatabase : databases) {
      if (abstractClausesDatabase != null) {
        noOfClauses += abstractClausesDatabase.size();
      }
    }

    output.write("p cnf ");
    output.write(Integer.toString(noOfVariables));
    output.write(" ");
    output.write(Integer.toString(noOfClauses));
    output.write("\n");

    for (AbstractClausesDatabase database : databases) {
      if (database != null) {
        database.toCnf(output);
      }
    }
  }
}
