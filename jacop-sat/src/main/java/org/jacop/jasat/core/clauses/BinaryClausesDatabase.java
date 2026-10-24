/*
 * BinaryClausesDatabase.java
 * <p>
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.io.BufferedWriter;
import java.io.IOException;
import org.jacop.jasat.utils.Utils;

/**
 * A database for binary clauses. It only accepts those.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class BinaryClausesDatabase extends AbstractClausesDatabase {

  private static final int INITIAL_SIZE = 100;

  // the clauses
  private int[] clauses = new int[INITIAL_SIZE];

  // current clause index
  private int currentIndex;

  // number of removed clauses
  private int numRemoved;

  /**
   * Adds a binary clause to the database.
   *
   * @param clause the clause to add (must be of length 2)
   * @param isModel true if this is a model clause
   * @return the unique ID of the added clause
   */
  public int addClause(int[] clause, boolean isModel) {

    if (ASSERTS_ENABLED && clause.length != 2) {
      throw new IllegalStateException("Assertion failed");
    }

    int newIndex = currentIndex++;

    int offset = newIndex << 1;

    // resize if needed
    if (offset + 1 >= clauses.length) {
      int newSize = (offset + 1) * 2;
      clauses = Utils.resize(clauses, newSize, clauses.length, pool);
    }

    // set clause
    clauses[offset] = clause[0];
    clauses[offset + 1] = clause[1];

    // remember those vars watch this clause
    addWatch(clause[0], newIndex);
    addWatch(clause[1], newIndex);

    // is clause unit, satisfied, satisfiable or conflict ?
    notifyClause(newIndex);

    return indexToUniqueId(newIndex);
  }

  /**
   * Notifies the database that a literal has been asserted for unit propagation.
   *
   * @param literal the literal that has been asserted
   */
  public void assertLiteral(int literal) {

    int varIdx = literal > 0 ? literal : -literal; // Math.abs(literal);

    if (watchLists.length <= varIdx || watchLists[varIdx] == null) {
      return;
    }

    // notify all clauses
    int[] watchedClauses = watchLists[varIdx];
    for (int i = watchedClauses[0] - 1; i > 0; i--) {

      // notify this clause

      // conflict, abort
      if (notifyClause(watchedClauses[i]) == ClauseState.UNSATISFIABLE_CLAUSE) {
        return;
      }
    }
  }

  /**
   * Removes a clause from the database.
   *
   * @param clauseId the unique ID of the clause to remove
   */
  public void removeClause(int clauseId) {

    int clauseIndex = dbStore.uniqueIdToIndex(clauseId);
    numRemoved++;

    // remove this clause from watched clauses
    int offset = clauseIndex << 1;
    removeWatch(clauses[offset], clauseIndex);
    removeWatch(clauses[offset + 1], clauseIndex);

    clauses[offset] = 0;
    clauses[offset + 1] = 0;
  }

  @Override
  public boolean canRemove(int clauseId) {
    return true;
  }

  /**
   * Performs resolution with the specified clause.
   *
   * @param clauseId the unique ID of the clause in the database
   * @param clause the clause to resolve with
   * @return the resulting clause after resolution
   */
  public MapClause resolutionWith(int clauseId, MapClause clause) {

    int clauseIndex = dbStore.uniqueIdToIndex(clauseId);
    if (ASSERTS_ENABLED && clauseIndex >= currentIndex) {
      throw new IllegalStateException("Assertion failed");
    }

    int offset = clauseIndex << 1;

    clause.partialResolveWith(clauses[offset]);
    clause.partialResolveWith(clauses[offset + 1]);

    return clause;
  }

  /**
   * Handles backjumping to a specified decision level.
   *
   * @param level the level to backjump to
   */
  public void backjump(int level) {
    // nothing to do
  }

  @Override
  public int rateThisClause(int[] clause) {

    if (clause.length == 2) {
      return CLAUSE_RATE_I_WANT_THIS_CLAUSE;
    } else {
      return CLAUSE_RATE_UNSUPPORTED;
    }
  }

  /**
   * When something changed, find the status of the clause.
   *
   * @param clauseIndex index of the clause
   * @return the state of the clause
   */
  private int notifyClause(int clauseIndex) {

    int offset = clauseIndex << 1;

    // get literals, values, and check for satisfied clause
    int literal0 = clauses[offset];
    int value0 = core.trail.values[literal0 < 0 ? -literal0 : literal0];
    if (value0 == literal0) {
      return ClauseState.SATISFIED_CLAUSE;
    }

    int literal1 = clauses[offset + 1];
    int value1 = core.trail.values[literal1 < 0 ? -literal1 : literal1];
    if (value1 == literal1) {
      return ClauseState.SATISFIED_CLAUSE;
    }

    if (value0 == 0 && value1 == 0) {
      return ClauseState.UNKNOWN_CLAUSE;
    }

    int clauseId = indexToUniqueId(clauseIndex);

    if (value0 == 0) {
      // propagate
      core.triggerPropagateEvent(literal0, clauseId);
      return ClauseState.SATISFIED_CLAUSE;
    } else if (value1 == 0) {
      // propagate
      core.triggerPropagateEvent(literal1, clauseId);
      return ClauseState.SATISFIED_CLAUSE;
    } else {
      // conflict
      if (ASSERTS_ENABLED && (value0 != -literal0 || value1 != -literal1)) {
        throw new IllegalStateException("Assertion failed");
      }

      MapClause conflictClause = core.explanationClause;
      conflictClause.clear();
      conflictClause.addLiteral(clauses[offset]);
      conflictClause.addLiteral(clauses[offset + 1]);

      core.triggerConflictEvent(conflictClause);

      return ClauseState.UNSATISFIABLE_CLAUSE;
    }
  }

  @Override
  public int size() {
    return currentIndex - numRemoved;
  }

  @Override
  public void toCnf(BufferedWriter output) throws IOException {
    writeClausesToCnf(output, clauses, currentIndex, 2);
  }
}
