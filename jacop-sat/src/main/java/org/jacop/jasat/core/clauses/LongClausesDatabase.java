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
import java.util.Random;
import org.jacop.core.Store;
import org.jacop.jasat.utils.Utils;

/*
 * TODO : code bcp, and maybe reuse watch node lists in some other databases
 */

/**
 * A pool of long clauses, implemented with two watched an blocking literals to minimize cache
 * misses.
 *
 * @author Radoslaw Szymanek
 * @version 4.10
 */
public final class LongClausesDatabase extends AbstractClausesDatabase {

  private static final int DEFAULT_INITIAL_NUMBER_OF_CLAUSES = 100;

  private static final int SIZE_OF_CLAUSE_CACHE = 8;

  /**
   * Put it one place so there is only one Random generator for the whole SAT solver. TODO: Radek.
   */
  final Random generator = Store.seedPresent() ? new Random(Store.getSeed()) : new Random();

  // the index of the current empty slot.
  private int currentIndex;
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
    return indexToUniqueId(newIndex);
  }

  public void assertLiteral(int literal) {

    /* get the watched clauses for this literal;
     * for each such clause, find its state, and if needed, propagate,
     * find a new watch or trigger conflict
     */

    // get the current watched clauses for the variable
    assert literal != 0;
    int var = literal < 0 ? -literal : literal;

    // The variable associated with the literal is not watching any clauses.
    if (watchLists.length <= var || watchLists[var] == null) {
      return;
    }

    assert watchLists[var] != null;
    int[] varClauses = watchLists[var];

    int positionOfFirstAvailablePlace = varClauses[0];

    // watched clauses
    for (int i = 1; i < positionOfFirstAvailablePlace; i++) {

      int clauseIndex = varClauses[i];
      int[] cache = literalsCache[clauseIndex];
      int[] clause = clauses[clauseIndex];

      // is the literal the first or second watch ?
      int myWatchPos = (cache[0] < 0 ? -cache[0] : cache[0]) == var ? 0 : 1;

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
      if (cache[myWatchPos] == literal) {
        continue;
      }
      // clause is satisfied, because of the other watch for this clause.
      if (isSatisfied(cache[otherWatch])) {
        continue;
      }

      // maybe watch replacement can be found in cache.
      for (int no = 2; no < SIZE_OF_CLAUSE_CACHE; no++) {
        if (isActiveOrSatisfied(cache[no])) {
          varClauses[i] = varClauses[--positionOfFirstAvailablePlace];
          varClauses[0] = positionOfFirstAvailablePlace;
          addWatch(cache[no], clauseIndex);
          cache[myWatchPos] = cache[no];
          cache[no] = myWatch;
        }
      }

      // maybe watch replacement can be find in main clause array.
      // replace cache with new potential watches later on.
      int startingPosition = generator.nextInt(clause.length - 1);
      int currentPosition = startingPosition + 1;
      int right = cache.length - 1;

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

          /*
           * TODO: Radek, can we trigger propagation right away or should we wait until all watches
           * are checked.
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

    if (clause.length > (SIZE_OF_CLAUSE_CACHE << 2)) {
      return CLAUSE_RATE_I_WANT_THIS_CLAUSE;
    } else {
      return CLAUSE_RATE_UNSUPPORTED;
    }
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

  /** is the literal at position @param literalPos satisfied in current trail ? */
  private boolean isSatisfied(int literal) {
    return trail.values[literal < 0 ? -literal : literal] == literal;
  }

  /** is the literal at position @param literalPos satisfied or active ? */
  private boolean isActiveOrSatisfied(int literal) {

    int value = trail.values[literal < 0 ? -literal : literal];
    return value == 0 || value == literal;
  }

  /** is the literal at position @param literalPos satisfied or active ? */
  private boolean isActive(int literal) {

    return trail.values[literal < 0 ? -literal : literal] == 0;
  }

  @Override
  public void toCNF(BufferedWriter output) {
    throw new UnsupportedOperationException("Not supported yet.");
  }
}
