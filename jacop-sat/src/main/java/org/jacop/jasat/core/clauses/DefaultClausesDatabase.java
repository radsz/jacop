/*
 * DefaultClausesDatabase.java
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

/*
 * Radek:
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
 * A standard database of clauses, implemented in an efficient way such that insertion or removal of
 * clauses works fast.
 *
 * <p>Two-watched literals are used for fast unit propagation. The two first literals of each
 * clauses are the watches.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class DefaultClausesDatabase extends AbstractClausesDatabase {

  /**
   * It accepts binary or longer clauses. Should we assume that clauses are at least length 4? Does
   * it make the code quicker?
   */
  private static final int DEFAULT_INITIAL_NUMBER_OF_CLAUSES = 100;

  // the array of clauses
  private int[][] clauses = new int[DEFAULT_INITIAL_NUMBER_OF_CLAUSES][];
  // the index of the current empty slot.
  private int currentIndex;
  // number of removed clauses
  private int numRemoved;

  /**
   * Notify the watches that this literal is set, updating the watched clauses and propagating
   * literals if pertinent. If a conflict occurs, the solver conflict Event will be triggered. This
   * is the main part of unit propagation for the solver.
   *
   * <p>It always creates a list of new watched list (newWatchedList).
   *
   * @param literal the literal that is being set
   */
  public void assertLiteral(int literal) {

    if (ASSERTS_ENABLED && !(trail.getLevel(Math.abs(literal)) == core.currentLevel)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (ASSERTS_ENABLED && !(checkWatches4var(Math.abs(literal)) == null)) {
      throw new IllegalStateException("Assertion failed");
    }

    /* get the watched clauses for this literal;
     * for each such clause, find its state, and if needed, propagate,
     * find a new watch or trigger conflict
     */

    // get the current watched clauses for the variable
    int varIdx = literal < 0 ? -literal : literal;
    if (watchLists.length <= varIdx || watchLists[varIdx] == null) {
      return;
    }

    // watched clauses for this literal
    int[] watchList = watchLists[varIdx];
    // value of the literal in the trail
    int myValue = trail.values[varIdx];
    if (ASSERTS_ENABLED && !(myValue != 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    // new watched clauses[], to replace the current one after propagation
    int newSize = Math.max(watchList[0], MINIMUM_VAR_WATCH_SIZE);
    int[] newWatchList = pool.getNew(newSize);
    int newWatchNum = 1;

    // iterate on watched clauses
    IterateOnWatchedClauses:
    for (int i = 1, n = watchList[0]; i < n; i++) {

      int clauseIndex = watchList[i];
      int[] clause = clauses[clauseIndex];
      int myWatchPos = clause[0] == varIdx || -clause[0] == varIdx ? 0 : 1;
      int myWatch = clause[myWatchPos];

      if (myWatch == myValue) {
        newWatchList[newWatchNum++] = clauseIndex;
        continue;
      }

      int otherWatch = clause[1 - myWatchPos];
      int otherValue = trail.values[otherWatch < 0 ? -otherWatch : otherWatch];

      if (ASSERTS_ENABLED && !(Math.abs(myWatch) == varIdx)) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && !(otherWatch * myWatch != 0)) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && !(doesWatch(myWatch, clauseIndex))) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && !(doesWatch(otherWatch, clauseIndex))) {
        throw new IllegalStateException("Assertion failed");
      }

      if (otherValue == otherWatch) {
        newWatchList[newWatchNum++] = clauseIndex;
        continue;
      }

      if (myValue == -myWatch && otherValue == -otherWatch) {
        int[] newWatchNumRef = new int[] {newWatchNum};
        boolean conflict =
            processBothWatchesWrong(
                clause,
                clauseIndex,
                myWatchPos,
                otherWatch,
                watchList,
                i,
                newWatchList,
                newWatchNumRef);
        newWatchNum = newWatchNumRef[0];
        if (conflict) {
          break IterateOnWatchedClauses;
        }
        continue;
      }

      if (ASSERTS_ENABLED && !(otherValue == 0)) {
        throw new IllegalStateException("Assertion failed");
      }
      int[] newWatchNumRef = new int[] {newWatchNum};
      tryFindNewWatchOrUnitPropagate(
          clause, clauseIndex, myWatchPos, otherWatch, newWatchList, newWatchNumRef);
      newWatchNum = newWatchNumRef[0];
    }

    /*
     * cleanup: put the new array of watched clauses in place of the old one
     */
    // remember which clauses we watch from now
    if (newWatchNum == 1) { // no clauses
      watchLists[varIdx] = null;
      pool.storeOld(newWatchList); // useless because empty
    } else {
      if (ASSERTS_ENABLED && !(newWatchNum > 1)) {
        throw new IllegalStateException("Assertion failed");
      }
      // save the length of the array, and the array itself
      newWatchList[0] = newWatchNum;
      watchLists[varIdx] = newWatchList;
    }

    // recycle old watch list
    pool.storeOld(watchList);

    if (ASSERTS_ENABLED && !(checkWatches4var(Math.abs(literal)) == null)) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  /**
   * Handles case b) both watches wrong: find two other watches or conflict/unit/two-watches.
   *
   * @return true if conflict (caller must break), false otherwise
   */
  private boolean processBothWatchesWrong(
      int[] clause,
      int clauseIndex,
      int myWatchPos,
      int otherWatch,
      int[] watchList,
      int currentIdx,
      int[] newWatchList,
      int[] newWatchNumRef) {
    int watch1pos = -1;
    int watch2pos = -1;
    int countWatches = 0;
    for (int j = 2; j < clause.length && countWatches < 2; j++) {
      int lit = clause[j];
      int value = trail.values[lit < 0 ? -lit : lit];
      if (value == 0) {
        if (countWatches == 0) {
          watch1pos = j;
        } else {
          watch2pos = j;
        }
        countWatches++;
      } else if (value == lit) {
        newWatchList[newWatchNumRef[0]++] = clauseIndex;
        return false;
      }
    }
    if (ASSERTS_ENABLED && !(countWatches <= 2)) {
      throw new IllegalStateException("Assertion failed");
    }
    switch (countWatches) {
      case 0:
        newWatchList[newWatchNumRef[0]++] = clauseIndex;
        MapClause conflictClause = core.explanationClause;
        conflictClause.clear();
        conflictClause.addAll(clause);
        if (ASSERTS_ENABLED && !(conflictClause.isUnsatisfiableIn(trail))) {
          throw new IllegalStateException("Assertion failed");
        }
        core.triggerConflictEvent(conflictClause);
        for (int j = currentIdx + 1; j < watchList[0]; j++) {
          newWatchList[newWatchNumRef[0]++] = watchList[j];
        }
        return true;
      case 1:
        if (ASSERTS_ENABLED && !(watch1pos != myWatchPos)) {
          throw new IllegalStateException("Assertion failed");
        }
        if (ASSERTS_ENABLED && !(watch1pos >= 2)) {
          throw new IllegalStateException("Assertion failed");
        }
        if (ASSERTS_ENABLED && !(trail.values[Math.abs(clause[watch1pos])] == 0)) {
          throw new IllegalStateException("Assertion failed");
        }
        newWatchList[newWatchNumRef[0]++] = clauseIndex;
        int uniqueClauseId1 = indexToUniqueId(clauseIndex);
        if (ASSERTS_ENABLED && !(new MapClause(clause).isUnitIn(trail))) {
          throw new IllegalStateException("Assertion failed");
        }
        if (ASSERTS_ENABLED && !(new MapClause(clause).isUnitIn(clause[watch1pos], trail))) {
          throw new IllegalStateException("Assertion failed");
        }
        core.triggerPropagateEvent(clause[watch1pos], uniqueClauseId1);
        return false;
      case 2:
        swap(clause, 0, watch1pos);
        swap(clause, 1, watch2pos);
        removeWatch(otherWatch, clauseIndex);
        addWatch(clause[0], clauseIndex);
        addWatch(clause[1], clauseIndex);
        if (ASSERTS_ENABLED && !(trail.values[Math.abs(clause[0])] == 0)) {
          throw new IllegalStateException("Assertion failed");
        }
        if (ASSERTS_ENABLED && !(trail.values[Math.abs(clause[1])] == 0)) {
          throw new IllegalStateException("Assertion failed");
        }
        return false;
      default:
        throw new AssertionError("wrong case!");
    }
  }

  /**
   * Case c) Other watch unset: find another watch or unit propagate. Updates newWatchNumRef when
   * adding clause to newWatchList (unit case).
   */
  private void tryFindNewWatchOrUnitPropagate(
      int[] clause,
      int clauseIndex,
      int myWatchPos,
      int otherWatch,
      int[] newWatchList,
      int[] newWatchNumRef) {
    for (int j = 2; j < clause.length; j++) {
      int lit = clause[j];
      int value = trail.values[lit < 0 ? -lit : lit];
      if (value == 0 || value == lit) {
        swap(clause, myWatchPos, j);
        addWatch(lit, clauseIndex);
        return;
      }
    }
    newWatchList[newWatchNumRef[0]++] = clauseIndex;
    int uniqueClauseId = indexToUniqueId(clauseIndex);
    if (ASSERTS_ENABLED && !(new MapClause(clause).isUnitIn(trail))) {
      throw new IllegalStateException("Assertion failed");
    }
    core.triggerPropagateEvent(otherWatch, uniqueClauseId);
  }

  /**
   * Adds a clause to the database.
   *
   * @param clause the clause to add (must be of length at least 2)
   * @param isModel true if this is a model clause
   * @return the unique ID of the added clause
   */
  public int addClause(int[] clause, boolean isModel) {

    if (ASSERTS_ENABLED && !(clause.length >= 2)) {
      throw new IllegalStateException("Assertion failed");
    }

    int clauseIndex = currentIndex++;
    int clauseId = indexToUniqueId(clauseIndex);

    ensureSize(currentIndex);
    clauses[clauseIndex] = clause;

    WatchSearchResult search = findWatchPositions(clause);

    applyAddClauseWatches(clause, clauseIndex, clauseId, search);

    addWatch(clause[0], clauseIndex);
    addWatch(clause[1], clauseIndex);

    if (ASSERTS_ENABLED && !((checkWatches4Clause(clauseIndex) == null))) {
      throw new IllegalStateException("Assertion failed");
    }

    return clauseId;
  }

  private static final class WatchSearchResult {
    final int watch1pos;
    final int watch2pos;
    final int highestPos;
    final int secondHighestPos;
    final int numFoundWatch;

    WatchSearchResult(
        int watch1pos, int watch2pos, int highestPos, int secondHighestPos, int numFoundWatch) {
      this.watch1pos = watch1pos;
      this.watch2pos = watch2pos;
      this.highestPos = highestPos;
      this.secondHighestPos = secondHighestPos;
      this.numFoundWatch = numFoundWatch;
    }
  }

  private WatchSearchResult findWatchPositions(int[] clause) {
    int watch1pos = -1;
    int watch2pos = -1;
    int highestPos = -1;
    int highestLevel = -1;
    int secondHighestPos = -1;
    int secondHighestLevel = -1;
    int numFoundWatch = 0;
    for (int i = 0; i < clause.length && numFoundWatch < 2; i++) {
      int literal = clause[i];
      int varIdx = literal < 0 ? -literal : literal;
      int value = trail.values[varIdx];
      if (value == 0 || value == literal) {
        if (numFoundWatch == 1) {
          watch2pos = i;
        } else {
          watch1pos = i;
        }
        numFoundWatch++;
      } else {
        if (ASSERTS_ENABLED && !(value == -literal)) {
          throw new IllegalStateException("Assertion failed");
        }
        if (ASSERTS_ENABLED && !(highestLevel >= secondHighestLevel)) {
          throw new IllegalStateException("Assertion failed");
        }
        int level = trail.getLevel(varIdx);
        if (level >= highestLevel) {
          secondHighestLevel = highestLevel;
          secondHighestPos = highestPos;
          highestLevel = level;
          highestPos = i;
        } else if (level > secondHighestLevel) {
          secondHighestLevel = level;
          secondHighestPos = i;
        }
      }
    }
    return new WatchSearchResult(watch1pos, watch2pos, highestPos, secondHighestPos, numFoundWatch);
  }

  private void applyAddClauseWatches(
      int[] clause, int clauseIndex, int clauseId, WatchSearchResult search) {
    switch (search.numFoundWatch) {
      case 2:
        if (ASSERTS_ENABLED && !(search.watch1pos != search.watch2pos)) {
          throw new IllegalStateException("Assertion failed");
        }
        putAt0And1(clause, search.watch1pos, search.watch2pos);
        break;
      case 1:
        if (ASSERTS_ENABLED && !(search.watch2pos == -1)) {
          throw new IllegalStateException("Assertion failed");
        }
        putAt0And1(clause, search.watch1pos, search.highestPos);
        core.triggerPropagateEvent(clause[0], clauseId);
        break;
      case 0:
        if (ASSERTS_ENABLED && !(search.highestPos != search.secondHighestPos)) {
          throw new IllegalStateException("Assertion failed");
        }
        putAt0And1(clause, search.highestPos, search.secondHighestPos);
        MapClause conflictClause = core.explanationClause;
        conflictClause.clear();
        conflictClause.addAll(clause);
        if (ASSERTS_ENABLED && !(conflictClause.isUnsatisfiableIn(trail))) {
          throw new IllegalStateException("Assertion failed");
        }
        core.triggerConflictEvent(conflictClause);
        break;
      default:
        throw new AssertionError("wrong number of found watches");
    }
  }

  /**
   * Removes a clause from the database.
   *
   * @param clauseIndex the index of the clause to remove
   */
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
   * @param explanation the clause to resolve with
   * @return the resulting clause after resolution
   */
  public MapClause resolutionWith(int clauseId, MapClause explanation) {

    int[] clause = clauses[uniqueIdToIndex(clauseId)];

    for (int literal : clause) {
      // resolution !
      explanation.partialResolveWith(literal);
    }
    return explanation;
  }

  @Override
  public int rateThisClause(int[] clause) {

    if (clause.length <= 1) {
      return CLAUSE_RATE_UNSUPPORTED;
    }

    // give an average rate, this database is versatile
    return CLAUSE_RATE_AVERAGE;
  }

  @Override
  public int size() {
    return currentIndex - numRemoved;
  }

  /** Returns to the given level. */
  public void backjump(int level) {
    // nothing to do
  }

  /**
   * (used for debug) checks if the 2 first literals of the clauses are exactly the set of literals
   * that watch this clause.
   *
   * @param clauseIndex the index of the clause
   */
  @SuppressWarnings("unused")
  private String checkWatches4Clause(int clauseIndex) {
    int[] clause = clauses[clauseIndex];
    if (ASSERTS_ENABLED && !(doesWatch(clause[0], clauseIndex))) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(doesWatch(clause[1], clauseIndex))) {
      throw new IllegalStateException("Assertion failed");
    }
    for (int j = 2; j < clause.length; j++) {
      if (ASSERTS_ENABLED && !(!doesWatch(clause[j], clauseIndex))) {
        throw new IllegalStateException("Assertion failed");
      }
    }
    return null;
  }

  /**
   * (used for debug) checks if the 2 first literals of the clauses are exactly the set of literals
   * that watch this clause.
   */
  @SuppressWarnings("unused")
  private String checkWatches4var(int varIdx) {

    if (watchLists.length <= varIdx) {
      return null;
    }

    int[] watchList = watchLists[varIdx];

    if (watchList == null) {
      return null;
    }

    for (int i = 1, n = watchList[0]; i < n; i++) {

      // the clause and its index
      int clauseIndex = watchList[i];
      int[] clause = clauses[clauseIndex];
      if (ASSERTS_ENABLED && !(doesWatch(clause[0], clauseIndex))) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && !(doesWatch(clause[1], clauseIndex))) {
        throw new IllegalStateException("Assertion failed");
      }
      for (int j = 2; j < clause.length; j++) {
        if (ASSERTS_ENABLED && !(!doesWatch(clause[j], clauseIndex))) {
          throw new IllegalStateException(
              String.valueOf(
                  "Too many watches on variable "
                      + varIdx
                      + " watches also on "
                      + j
                      + " "
                      + new MapClause(clause)));
        }
      }
    }

    return null;
  }

  /**
   * Assuming i != j, this modifies clause so that the elements that were at position i and j will
   * now be at position 0 and 1 (i.e. clause[i] becomes clause[0] and clause[j] becomes clause[1])
   *
   * @param clause the clause to modify
   * @param i the first index
   * @param j the second index
   */
  private void putAt0And1(int[] clause, int i, int j) {
    if (ASSERTS_ENABLED && !(i >= 0 && i < clause.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(j >= 0 && j < clause.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(i != j)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (i == 0 && j == 1) {
      return;
    }
    if (i == 1 && j == 0) {
      swap(clause, 0, 1);
      return;
    }
    if (i == 0) {
      swap(clause, 1, j);
      return;
    }
    if (i == 1) {
      swap(clause, 0, 1);
      swap(clause, 1, j);
      return;
    }
    if (j == 0) {
      swap(clause, 0, i);
      swap(clause, 1, i);
      return;
    }
    if (j == 1) {
      swap(clause, 0, i);
      return;
    }
    swap(clause, 0, i);
    swap(clause, 1, j);
  }

  /**
   * Be sure that the database can contain @param size clauses.
   *
   * @param size the number of clauses
   */
  public void ensureSize(int size) {
    if (ASSERTS_ENABLED && !(currentIndex <= clauses.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(size >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (size >= clauses.length) {
      int newSize = 2 * size; // take some safety margin
      clauses = Utils.resize(clauses, newSize, currentIndex);
    }
  }

  @Override
  public void toCnf(BufferedWriter output) throws IOException {

    for (int i = 0; i < currentIndex; i++) {

      int[] clause = clauses[i];

      if (clause != null) {

        for (int k : clause) {
          output.write(Integer.toString(k));
          output.write(" ");
        }
        output.write("0\n");
      }
    }
  }
}
