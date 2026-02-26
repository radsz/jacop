/*
 * ConflictLearning.java
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

package org.jacop.jasat.core;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import org.jacop.jasat.core.clauses.DatabasesStore;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.utils.structures.IntStack;

/**
 * A solver component for conflict learning. (first UIP algorithm)
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class ConflictLearning implements SolverComponent {

  private Core core;

  // faster access to some objects
  private DatabasesStore dbStore;
  private Trail trail;

  /**
   * It computes to which level we should backjump to solve the conflict explained by @param
   * explanationClause.
   *
   * @param explanationClause used for backjumping computation
   * @return a level
   */
  public int getLevelToBackjump(MapClause explanationClause) {

    // this is a conflict, I hope
    if (ASSERTS_ENABLED && !(core.currentState == SolverState.CONFLICT)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(core.currentLevel > 0)) {
      throw new IllegalStateException(String.valueOf("cannot backjump from level 0"));
    }
    // did we met the highest literal in the clause ?
    boolean firstOne = true;

    IntStack assertionStack = trail.assertionStack;
    // find the first asserted literal before the one in explainClause
    for (int i = assertionStack.size() - 1; i >= 0; i--) {
      int varIdx = assertionStack.array[i];

      // this literal is in the clause
      if (explanationClause.containsVariable(varIdx)) {
        if (firstOne) {
          // ok, we met the first, the next one is the good one
          explanationClause.assertedLiteral = -trail.values[varIdx];
          firstOne = false;
        } else {
          return trail.getLevel(varIdx);
        }
      }
    }

    // default case
    return 0;
  }

  /**
   * It builds the explanation clause made of all literals that were involved in a conflict (ie
   * which are in the clause and were asserted, or were asserted and triggered, in another clause,
   * the propagation of a literal present in the current clause).
   *
   * @param explanationClause the SetClause we use, which must be initialized to the conflict clause
   */
  public void applyExplainUip(MapClause explanationClause) {

    if (ASSERTS_ENABLED && !(!explanationClause.isEmpty())) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(explanationClause.isUnsatisfiableIn(trail))) {
      throw new IllegalStateException("Assertion failed");
    }

    // count how many literals from current level the clause contains
    int curLevel = core.currentLevel;
    int startingPosition = trail.size() - 1;

    IntStack assertionStack = trail.assertionStack;

    while (true) {

      // find the literal to resolve
      int lastLiteralPosition =
          findPositionTopLiteral(explanationClause, curLevel, startingPosition);
      // if none, abort
      if (lastLiteralPosition == -1) {
        explanationClause.backjumpLevel = getLevelToBackjump(explanationClause);
        return;
      }

      // resolve with its explanation
      applyExplain(explanationClause, assertionStack.array[lastLiteralPosition]);

      startingPosition = lastLiteralPosition - 1;
    }
  }

  /**
   * It gets the position of last set literal of the clause.
   *
   * @param explanationClause the clause
   * @param level the level of selectable literals
   * @return the last set literal of the clause, at current level, or 0 if none has been found
   */
  private int findPositionTopLiteral(MapClause explanationClause, int level, int startingPosition) {

    for (int i = startingPosition; i >= 0; i--) {
      int varIdx = trail.assertionStack.array[i];
      if (ASSERTS_ENABLED && !(varIdx > 0)) {
        throw new IllegalStateException("Assertion failed");
      }

      if (ASSERTS_ENABLED && !(trail.isSet(varIdx))) {
        throw new IllegalStateException("Assertion failed");
      }

      // we reached the asserted literal -- the first set in its level
      if (trail.isAsserted(varIdx)) {
        return -1;
      }
      // we passed under the level
      if (trail.getLevel(varIdx) < level) {
        return -1;
      }

      // suitable literal, it is in the clause
      if (explanationClause.containsVariable(varIdx)) {
        return i;
      }
    }

    // none has been found
    return -1;
  }

  /**
   * Performs one step of resolution for conflict explanation on given explanation clause.
   *
   * @param explanationClause the explanation clause
   * @param literal the literal that must be resolved
   */
  private void applyExplain(MapClause explanationClause, int literal) {
    if (ASSERTS_ENABLED && !(explanationClause.containsVariable(literal))) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(trail.isSet(Math.abs(literal)))) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(!trail.isAsserted(Math.abs(literal)))) {
      throw new IllegalStateException("Assertion failed");
    }

    // perform resolution
    int clauseId = trail.getExplanation(Math.abs(literal));
    dbStore.resolutionWith(clauseId, explanationClause);
  }

  /**
   * Initializes the conflict learning component with the solver core.
   *
   * @param core the solver core
   */
  public void initialize(Core core) {
    this.core = core;
    core.conflictLearning = this;
    this.dbStore = core.dbStore;
    this.trail = core.trail;
  }
}
