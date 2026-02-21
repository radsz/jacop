/*
 * UnaryClausesDatabase.java
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

import java.io.BufferedWriter;
import java.io.IOException;
import org.jacop.jasat.utils.Utils;

/**
 * A database for unit clauses (length 1). It only accepts those.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class UnaryClausesDatabase extends AbstractClausesDatabase {

  private static final int INITIAL_SIZE = 100;

  // the clauses
  private int[] clauses = new int[INITIAL_SIZE];

  // current max index
  private int currentIndex;

  // number of removed clauses
  private int numRemoved;

  /**
   * Adds a unary clause to the database.
   *
   * @param clause the clause to add (must be of length 1)
   * @param isModel true if this is a model clause
   * @return the unique ID of the added clause
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
    int varIdx = literal < 0 ? -literal : literal;
    int value = trail.values[varIdx];
    if (value == 0) {
      core.triggerPropagateEvent(literal, newId);
    } else if (value == -literal) {
      MapClause conflictClause = core.explanationClause;
      conflictClause.clear();
      conflictClause.addLiteral(literal);
      core.triggerConflictEvent(conflictClause);
    } else {
      assert value == literal;
    }

    return newId;
  }

  /**
   * Removes a clause from the database.
   *
   * @param clauseId the unique ID of the clause to remove
   */
  public void removeClause(int clauseId) {
    assert clauseId < currentIndex;
    numRemoved++;
    clauses[clauseId] = 0;
    // nothing to do (not worthy to remember empty slots)
  }

  /**
   * Checks if a clause can be removed from the database.
   *
   * @param clauseId the unique ID of the clause
   * @return true if the clause can be removed
   */
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
    assert clauseIndex < currentIndex;

    int literal = clauses[clauseIndex];
    clause.partialResolveWith(literal);

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

  /**
   * Notifies the database that a literal has been asserted for unit propagation.
   *
   * @param literal the literal that has been asserted
   */
  public void assertLiteral(int literal) {
    // nothing to do

  }

  @Override
  public int rateThisClause(int[] clause) {
    if (clause.length == 1) {
      return CLAUSE_RATE_I_WANT_THIS_CLAUSE;
    } else {
      return CLAUSE_RATE_UNSUPPORTED;
    }
  }

  @Override
  public String toString(String prefix) {
    StringBuilder sb = new StringBuilder().append("unary clause database\n");
    for (int i = 0; i < currentIndex; i++) {
      sb.append("[").append(clauses[i]).append("]\n");
    }
    return sb.toString();
  }

  @Override
  public int size() {
    return currentIndex - numRemoved;
  }

  @Override
  public void toCnf(BufferedWriter output) throws IOException {

    for (int i = 0; i < currentIndex; i++) {
      if (clauses[i] != 0) {
        output.write(Integer.toString(clauses[i]));
        output.write(" 0\n");
      }
    }
  }
}
