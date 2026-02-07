/*
 * ActivityModule.java
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

package org.jacop.jasat.modules;

import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;
import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.ClauseListener;
import org.jacop.jasat.modules.interfaces.ConflictListener;

/*
 * TODO : polarity caching
 * TODO : some nice data structure to have a real Priority queue
 */

/**
 * Counts the activity of literals.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.10
 */
public final class ActivityModule implements ClauseListener, BackjumpListener, ConflictListener {

  // number of conflicts needed to increase bump rate (ie, it is increased
  // every 20 learnt clauses)
  private static final int LEARNT_COUNT_TO_INCREASE = 20;
  // how often do we sort again the priority queue
  private static final int CONFLICT_COUNT_TO_SORT = 100;
  // number by which activity bump rate is multiplied
  private static final int BUMP_INCREASE_FACTOR = 2;
  // set of literals that are in priorities
  private final BitSet prioritizedVars = new BitSet();
  // solver instance
  public Core core;
  // the rates, for each variable and polarity.
  private int[] posActivities;
  private int[] negActivities;

  /**
   * Compares literals according to their activity. This stands for i > j and not i < j, because we
   * want activities to be sorted in decreasing order
   *
   * @author simon
   */
  private final Comparator<Integer> comparator =
      (i, j) -> {
        assert Math.abs(i) <= posActivities.length + 1;
        assert Math.abs(j) <= posActivities.length + 1;
        assert posActivities.length == negActivities.length;

        int activity_i = getLiteralActivity(Math.abs(i), i > 0);
        int activity_j = getLiteralActivity(Math.abs(j), j > 0);

        return activity_j - activity_i;
      };

  private int activitiesIndex;
  // the bump rate
  private int currentBumpRate;
  // above which value do we rebase values ?
  private int rebaseThreshold;
  // the number of learnt clauses since last bump rate increase
  private int learntCount;
  // hand-managed priority queue for literals (always sorted by activity)
  private Integer[] priorities = new Integer[50];
  private int prioritiesIndex;
  // used to update sorting of priorities sometimes
  private int conflictCount;

  /**
   * Called when the solver performs a backjump operation.
   *
   * @param oldLevel the decision level before the backjump
   * @param newLevel the decision level after the backjump
   */
  public void onBackjump(int oldLevel, int newLevel) {}

  /**
   * Called when the solver restarts from a given decision level.
   *
   * @param oldLevel the decision level from which the restart occurs
   */
  public void onRestart(int oldLevel) {
    // get the priorities sorted again
    sortArray();
  }

  /**
   * Called when a conflict is detected during solving.
   *
   * @param conflictClause the clause that caused the conflict
   * @param level the decision level at which the conflict occurred
   */
  public void onConflict(MapClause conflictClause, int level) {
    conflictCount++;

    // sometimes, update sorting of literals
    if (conflictCount >= CONFLICT_COUNT_TO_SORT) {
      sortArray();
      conflictCount = 0;
    }
  }

  /** Sort the priorities array (useful after adding a lot of clauses). */
  public void sortArray() {
    Arrays.sort(priorities, 0, prioritiesIndex, comparator);
  }

  /**
   * Called when a new clause is added to the solver.
   *
   * @param clause the clause being added as an array of literals
   * @param clauseId the unique identifier assigned to the clause
   * @param isModelClause true if the clause is from the original model, false if it is a learnt
   *     clause
   */
  public void onClauseAdd(int[] clause, int clauseId, boolean isModelClause) {

    // if needed, increase bump rate
    if (!isModelClause) {
      learntCount++;
    }

    if (learntCount >= LEARNT_COUNT_TO_INCREASE) {
      increaseBumpRate();
      learntCount = 0;
    }

    // bump all literals in the explanation clause
    for (int literal : clause) {
      // bump the variable
      bumpVar(literal);

      // get it in the priority queue
      int var = Math.abs(literal);
      if (!prioritizedVars.get(var)) {
        if (prioritiesIndex + 2 >= priorities.length) {
          int newLength = 2 * priorities.length;
          priorities = Arrays.copyOf(priorities, newLength);
        }

        priorities[prioritiesIndex++] = var;
        priorities[prioritiesIndex++] = -var;
        prioritizedVars.set(var);
      }
    }
  }

  /**
   * Called when a clause is removed from the solver.
   *
   * @param clauseId the identifier of the clause being removed
   */
  public void onClauseRemoval(int clauseId) {
    // nothing to do
  }

  /**
   * Returns the non-set literal with highest activity, if any.
   *
   * @return a non set literal, or 0 if all known literals are set
   */
  public int getLiteralToAssert() {

    // by decreasing activity order
    for (int i = 0; i < prioritiesIndex; i++) {
      int literal = priorities[i];
      int var = Math.abs(literal);

      // var with highest activity
      if (!core.trail.isSet(var)) {
        return literal;
      }
    }

    // no free literal
    return 0;
  }

  /**
   * Gives activity of a (signed) literal.
   *
   * @return the activity of this (variable, polarity)
   */
  private int getLiteralActivity(int var, boolean polarity) {
    assert var > 0;

    if (polarity) {
      return posActivities[var];
    } else {
      return negActivities[var];
    }
  }

  /**
   * Code that really performs variable and polarity activity bumping.
   *
   * @return the new activity of the variable
   */
  private int bumpVar(int literal) {
    int var = Math.abs(literal);
    ensureVarSize(var);
    int curValue = literal > 0 ? posActivities[var] : negActivities[var];

    // keep rates under some threshold
    if (curValue >= rebaseThreshold) {
      rebase(curValue);
    }

    // increase rate
    if (literal > 0) {
      return posActivities[var] = curValue + currentBumpRate;
    } else {
      return negActivities[var] = curValue + currentBumpRate;
    }
  }

  // be sure the variable bump can be accessed safely
  private void ensureVarSize(int var) {
    assert var > 0;
    assert posActivities.length == negActivities.length;

    if (var > activitiesIndex) {
      if (var >= posActivities.length) {
        // resize the arrays
        int newSize = 2 * var;
        posActivities = Arrays.copyOf(posActivities, newSize);
        negActivities = Arrays.copyOf(negActivities, newSize);
      }

      // set rate = 0 for elements between maxVar+1 and var
      Arrays.fill(posActivities, activitiesIndex + 1, var, 0);
      Arrays.fill(negActivities, activitiesIndex + 1, var, 0);

      activitiesIndex = var;
    }
  }

  /** Increases the bump rate, so that recent activity is more important than old activity. */
  private void increaseBumpRate() {
    currentBumpRate = currentBumpRate * BUMP_INCREASE_FACTOR;
  }

  /**
   * Rebases all values.
   *
   * @param value the value that just overflowed
   */
  private void rebase(int value) {

    // RS: Rebasing should use shift operations instead of *
    // e.g. >> 20 (?)
    // TODO: kind of integer log
    int rebaseFactor = 100 / value;
    for (int curVar = 1; curVar <= activitiesIndex; curVar++) {
      posActivities[curVar] = posActivities[curVar] * rebaseFactor;
      negActivities[curVar] = negActivities[curVar] * rebaseFactor;
    }
  }

  @Override
  public String toString() {
    return "ActivityModule";
  }

  /**
   * Initializes the activity module and registers it with the solver core for relevant events.
   *
   * @param core the solver core instance
   */
  public void initialize(Core core) {

    this.core = core;

    // register
    core.clauseModules[core.numClauseModules++] = this;
    core.conflictModules[core.numConflictModules++] = this;
    core.restartModules[core.numRestartModules++] = this;

    // FIXME: what if maxVariable() increases ? (with wrapper, for instance)
    activitiesIndex = Math.max(core.getMaxVariable(), 100);
    posActivities = new int[activitiesIndex + 1];
    negActivities = new int[activitiesIndex + 1];

    currentBumpRate = core.config.bump_rate;
    rebaseThreshold = core.config.rebase_threshold;
  }
}
