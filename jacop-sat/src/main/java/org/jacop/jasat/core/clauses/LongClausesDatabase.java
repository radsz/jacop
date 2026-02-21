/*
 * LongClausesDatabase.java
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
import org.jacop.core.Store;
import org.jacop.jasat.utils.Utils;

/**
 * A pool of long clauses, implemented with two watched an blocking literals to minimize cache
 * misses.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LongClausesDatabase extends AbstractClausesDatabase {

  private static final int DEFAULT_INITIAL_NUMBER_OF_CLAUSES = 100;

  private static final int SIZE_OF_CLAUSE_CACHE = 8;

  // the index of the current empty slot.
  private int currentIndex;
  // the pool of clauses
  private int[][] clauses = new int[DEFAULT_INITIAL_NUMBER_OF_CLAUSES][];
  // the small pool of literals of clauses that can be used for watching.
  private int[][] literalsCache = new int[DEFAULT_INITIAL_NUMBER_OF_CLAUSES][];

  /**
   * Adds a long clause to the database.
   *
   * @param clause the clause to add
   * @param isModel true if this is a model clause
   * @return the unique ID of the added clause
   */
  public int addClause(int[] clause, boolean isModel) {
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
    return indexToUniqueId(newIndex);
  }

  /**
   * Notifies the database that a literal has been asserted for unit propagation.
   *
   * @param literal the literal that has been asserted
   */
  public void assertLiteral(int literal) {

    assert literal != 0;
    int varIdx = literal < 0 ? -literal : literal;

    if (watchLists.length <= varIdx || watchLists[varIdx] == null) {
      return;
    }

    int[] varClauses = watchLists[varIdx];
    int[] positionRef = new int[] {varClauses[0]};

    for (int i = 1; i < positionRef[0]; i++) {
      int clauseIndex = varClauses[i];
      int[] cache = literalsCache[clauseIndex];
      int myWatchPos = (cache[0] < 0 ? -cache[0] : cache[0]) == varIdx ? 0 : 1;
      int otherWatch = cache[1 - myWatchPos];
      int myWatch = cache[myWatchPos];

      assert Math.abs(myWatch) == varIdx;
      assert otherWatch * myWatch != 0;

      if (cache[myWatchPos] == literal) {
        continue;
      }
      if (isSatisfied(otherWatch)) {
        continue;
      }

      if (tryReplaceWatchFromCache(
          varClauses, positionRef, i, cache, myWatchPos, myWatch, clauseIndex)) {
        continue;
      }

      int[] clause = clauses[clauseIndex];
      int right = scanClauseForWatches(clause, cache);

      if (right == cache.length - 1) {
        MapClause conflictClause = core.explanationClause;
        conflictClause.clear();
        conflictClause.addAll(clauses[clauseIndex]);
        core.triggerConflictEvent(conflictClause);
        break;
      }

      if (right == cache.length - 2 && isActive(cache[cache.length - 1])) {
        int clauseId = indexToUniqueId(clauseIndex);
        core.triggerPropagateEvent(cache[cache.length - 1], clauseId);
        continue;
      }

      if (tryReplaceWatchFromCache(
          varClauses, positionRef, i, cache, myWatchPos, myWatch, clauseIndex)) {
        continue;
      }

      throw new AssertionError("should not happen, bad int");
    }

    if (positionRef[0] == 1) {
      pool.storeOld(watchLists[varIdx]);
      watchLists[varIdx] = null;
    }
  }

  /** Tries to replace watch from cache. Updates positionRef[0] and varClauses if replaced. */
  private boolean tryReplaceWatchFromCache(
      int[] varClauses,
      int[] positionRef,
      int i,
      int[] cache,
      int myWatchPos,
      int myWatch,
      int clauseIndex) {
    for (int no = 2; no < SIZE_OF_CLAUSE_CACHE; no++) {
      if (isActiveOrSatisfied(cache[no])) {
        positionRef[0]--;
        varClauses[i] = varClauses[positionRef[0]];
        varClauses[0] = positionRef[0];
        addWatch(cache[no], clauseIndex);
        cache[myWatchPos] = cache[no];
        cache[no] = myWatch;
        return true;
      }
    }
    return false;
  }

  /** Scans clause for active/satisfied literals into cache. Returns right index after fill. */
  private int scanClauseForWatches(int[] clause, int[] cache) {
    int startingPosition = Store.getRandom().nextInt(clause.length - 1);
    int right = cache.length - 1;
    int currentPosition = startingPosition + 1;
    while (currentPosition < clause.length) {
      if (right == 2) {
        break;
      }
      if (isActiveOrSatisfied(clause[currentPosition])) {
        cache[right--] = clause[currentPosition];
      }
      currentPosition++;
    }
    currentPosition = 0;
    while (currentPosition <= startingPosition) {
      if (right == 2) {
        break;
      }
      if (isActiveOrSatisfied(clause[currentPosition])) {
        cache[right--] = clause[currentPosition];
      }
      currentPosition++;
    }
    return right;
  }

  /**
   * Removes a clause from the database.
   *
   * @param clauseId the unique ID of the clause to remove
   */
  public void removeClause(int clauseId) {}

  /**
   * Checks if a clause can be removed from the database.
   *
   * @param clauseId the unique ID of the clause
   * @return true if the clause can be removed
   */
  public boolean canRemove(int clauseId) {
    return false;
  }

  /**
   * Performs resolution with the specified clause.
   *
   * @param clauseIndex the index of the clause in the database
   * @param clause the clause to resolve with
   * @return the resulting clause after resolution
   */
  public MapClause resolutionWith(int clauseIndex, MapClause clause) {
    return null;
  }

  /**
   * Handles backjumping to a specified decision level.
   *
   * @param level the level to backjump to
   */
  public void backjump(int level) {}

  /**
   * Rates how well this database can handle the given clause.
   *
   * @param clause the clause to rate
   * @return the rating value indicating database suitability
   */
  public int rateThisClause(int[] clause) {

    if (clause.length > (SIZE_OF_CLAUSE_CACHE << 2)) {
      return CLAUSE_RATE_I_WANT_THIS_CLAUSE;
    } else {
      return CLAUSE_RATE_UNSUPPORTED;
    }
  }

  /**
   * Returns the number of clauses in the database.
   *
   * @return the number of clauses
   */
  public int size() {
    return 0;
  }

  /**
   * Be sure that the database can contain numberOfClauses clauses.
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
   * Checks if the literal is satisfied in the current trail.
   *
   * @param literal the literal to check
   * @return true if satisfied
   */
  private boolean isSatisfied(int literal) {
    return trail.values[literal < 0 ? -literal : literal] == literal;
  }

  /**
   * Checks if the literal is satisfied or active.
   *
   * @param literal the literal to check
   * @return true if satisfied or active
   */
  private boolean isActiveOrSatisfied(int literal) {

    int value = trail.values[literal < 0 ? -literal : literal];
    return value == 0 || value == literal;
  }

  /**
   * Checks if the literal is active.
   *
   * @param literal the literal to check
   * @return true if active
   */
  private boolean isActive(int literal) {

    return trail.values[literal < 0 ? -literal : literal] == 0;
  }

  @Override
  public void toCnf(BufferedWriter output) {
    throw new UnsupportedOperationException("Not supported yet.");
  }
}
