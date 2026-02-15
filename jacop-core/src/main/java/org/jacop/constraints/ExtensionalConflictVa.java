/*
 * ExtensionalConflictVa.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Extensional constraint assures that none of the tuples explicitly given is enforced in the
 * relation.
 *
 * <p>This implementation tries to balance the usage of memory versus time efficiency.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class ExtensionalConflictVa extends AbstractExtensionalVa {

  static final boolean DEBUG_ALL = false;
  static boolean debugAllLocal = DEBUG_ALL;

  static final boolean DEBUG_PRUNING = false;
  static boolean debugPruning = DEBUG_PRUNING;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final LinkedHashSet<Var> variableQueue = new LinkedHashSet<>();
  final int[] tuple;

  int numberTuples;
  Store store;

  int[][][] lastofsequence;
  int[][][] supports;
  private boolean satisfiedAlreadyAtImposition;

  /**
   * Constructor stores reference to tuples until imposition, any changes to tuples parameter will
   * be reflected in the constraint behavior. Changes to tuples should not performed under any
   * circumstances. The tuples array is not copied to save memory and time.
   *
   * @param list list of variables for the conflict constraint
   * @param tuples list of forbidden tuples
   */
  public ExtensionalConflictVa(IntVar[] list, int[][] tuples) {

    super(idNumber, list, tuples);
    supports = new int[list.length][][];
    tuple = new int[list.length];
  }

  /**
   * The constructor does not create local copy of tuples array. Any changes to this array will
   * reflect on constraint behavior. Most probably incorrect as other data structures will not
   * change accordingly.
   *
   * @param variables the scope of the extensional conflict constraint.
   * @param tuples the conflict (forbidden) tuples for that constraint.
   */
  public ExtensionalConflictVa(List<? extends IntVar> variables, int[][] tuples) {
    this(variables.toArray(new IntVar[0]), tuples);
  }

  /**
   * It seeks support tuple for a given variable and its value.
   *
   * @param varPosition variable for which the support is seeked.
   * @param value value of the variable for which support is seeked.
   * @return support tuple supporting varPosition-value pair.
   */
  @Override
  public int[] seekSupportVa(int varPosition, int value) {

    if (DEBUG_ALL) {
      log.debug("Seeking support for {} and value {}", list[varPosition], value);
    }

    int[] t = getInitialSupportTuple(varPosition, value);
    assert t != null : " First valid tuple can not be null ";

    int pos = findPosition(value, values[varPosition]);
    int[][] tuplesVarValue = tuples[varPosition][pos];
    int[] lastofsequenceVarValue = lastofsequence[varPosition][pos];

    while (true) {
      int position = isDisallowed(varPosition, value, t);
      if (position == -1) {
        recordSupport(varPosition, value, t);
        return t;
      }
      if (lastofsequenceVarValue[position] != position) {
        System.arraycopy(tuplesVarValue[lastofsequenceVarValue[position]], 0, t, 0, list.length);
      }
      int invalidPosition = seekInvalidPosition(t);
      boolean advanced =
          invalidPosition == -1
              ? advanceTupleFromEnd(t, varPosition)
              : advanceTupleFromInvalidPosition(t, varPosition, invalidPosition);
      if (!advanced) {
        return null;
      }
    }
  }

  private int[] getInitialSupportTuple(int varPosition, int value) {
    int[] t = tuple;
    int pos = findPosition(value, values[varPosition]);
    if (pos == -1) {
      return setFirstValid(varPosition, value);
    }
    try {
      if (supports[varPosition][pos] != null) {
        System.arraycopy(supports[varPosition][pos], 0, t, 0, list.length);
      } else {
        t = setFirstValid(varPosition, value);
      }
    } catch (Exception _) {
      t = setFirstValid(varPosition, value);
    }
    return t;
  }

  /** Advances t to the next candidate from the end. Returns false if no more tuples. */
  private boolean advanceTupleFromEnd(int[] t, int varPosition) {
    int i = list.length - 1;
    for (; i >= 0; i--) {
      if (i != varPosition) {
        if (t[i] == list[i].max()) {
          t[i] = list[i].min();
        } else {
          t[i] = list[i].domain.nextValue(t[i]);
          return true;
        }
      }
    }
    return false;
  }

  /** Advances t from invalidPosition. Returns false if no more tuples. */
  private boolean advanceTupleFromInvalidPosition(int[] t, int varPosition, int invalidPosition) {
    for (int i = invalidPosition + 1; i < list.length; i++) {
      if (i != varPosition) {
        t[i] = list[i].min();
      }
    }
    for (int i = invalidPosition; i >= 0; i--) {
      if (i != varPosition) {
        if (t[i] >= list[i].max()) {
          t[i] = list[i].min();
        } else {
          t[i] = list[i].domain.nextValue(t[i]);
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Records a support tuple for a given variable-value pair to optimize future support searches.
   *
   * @param varPosition the position of the variable
   * @param value the value for which support is recorded
   * @param t the support tuple to record
   */
  private void recordSupport(int varPosition, int value, int[] t) {

    int pos = findPosition(value, values[varPosition]);

    int[][] supports4variable = supports[varPosition];

    if (supports4variable == null) {
      supports4variable = new int[values[varPosition].length][];
      supports4variable[pos] = new int[list.length];
      System.arraycopy(t, 0, supports4variable[pos], 0, list.length);
    } else {
      if (supports4variable[pos] == null) {
        supports4variable[pos] = new int[list.length];
      }
      System.arraycopy(t, 0, supports4variable[pos], 0, list.length);
    }
  }

  /**
   * It computes the first valid tuple given restriction that a variable will be equal to a given
   * value.
   *
   * @param varPosition the position of the variable.
   * @param value the value of the variable.
   * @return the smallest valid tuple supporting varPosition-value pair.
   */
  public int[] setFirstValid(int varPosition, int value) {

    int[] t = tuple;

    int noVars = list.length;
    for (int i = 0; i < noVars; i++) {
      t[i] = list[i].min();
    }

    t[varPosition] = value;

    return t;
  }

  /**
   * It returns the position of disallowed tuple in the array of tuples for a given variable-value
   * pair.
   *
   * @param varPosition variable for which we search for the forbidden tuple.
   * @param value value for which we search for the forbidden tuple.
   * @param t tuple which we check for forbidness.
   * @return position of the forbidden tuple, -1 if it is not forbidden.
   */
  public int isDisallowed(int varPosition, int value, int[] t) {

    if (DEBUG_ALL) {
      log.debug("variable {} position {} value {}", list[varPosition], varPosition, value);
    }

    int[][] tuplesForGivenVariableValuePair =
        tuples[varPosition][findPosition(value, values[varPosition])];

    int left = 0;
    int right = tuplesForGivenVariableValuePair.length - 1;

    int position = (left + right) >> 1;

    while (left + 1 < right) {

      if (smaller(t, tuplesForGivenVariableValuePair[position])) {
        right = position;
      } else {
        left = position;
      }

      position = (left + right) >> 1;
    }

    if (left != right) {
      if (arraysEqual(t, tuplesForGivenVariableValuePair[left])) {
        return left;
      }

      if (arraysEqual(t, tuplesForGivenVariableValuePair[right])) {
        return right;
      }
    } else {

      if (arraysEqual(t, tuplesForGivenVariableValuePair[left])) {
        return left;
      }
    }

    return -1;
  }

  /**
   * It puts back tuples which have lost their support status at the level which is being removed.
   */
  @Override
  public void removeLevel(int level) {

    // backtracking has occurred (removeLevel) therefore
    // restart tuples can not be reused.
    supports = new int[list.length][][];
    variableQueue.clear();
  }

  @Override
  public void consistency(Store store) {

    if (DEBUG_ALL) {
      log.debug("Begin {}", this);
    }

    if (satisfiedAlreadyAtImposition) {
      return;
    }

    pruneUnsupported(store);

    if (DEBUG_ALL) {
      log.debug("End {}", this);
    }
  }

  @Override
  public void impose(Store store) {

    super.impose(store);
    this.store = store;

    filterAndIndexTuples(store);

    lastofsequence = new int[list.length][][];

    for (int i = 0; i < list.length; i++) {
      lastofsequence[i] = new int[tuples[i].length][];

      for (int j = 0; j < tuples[i].length; j++) {
        lastofsequence[i][j] = new int[tuples[i][j].length];
        for (int l = 0; l < tuples[i][j].length; l++) {
          lastofsequence[i][j][l] = computeLastOfSequence(tuples[i][j], i, l);
        }
      }
    }

    numberTuples = tuplesFromConstructor != null ? tuplesFromConstructor.length : 0;

    if (numberTuples == 0) {
      satisfiedAlreadyAtImposition = true;
    }

    tuplesFromConstructor = null;

    store.raiseLevelBeforeConsistency = true;
  }

  /**
   * Computes the last tuple in a sequence of consecutive forbidden tuples. This optimization allows
   * skipping over sequences of forbidden tuples during support search.
   *
   * @param is the array of forbidden tuples
   * @param posVar the position of the variable being considered
   * @param l the starting position in the tuple array
   * @return the index of the last tuple in the consecutive sequence
   */
  private int computeLastOfSequence(int[][] is, int posVar, int l) {

    int[] t = tuple;

    System.arraycopy(is[l], 0, t, 0, list.length);

    while (l + 1 < is.length) {

      for (int i = list.length - 1; i >= 0; i--) {
        if (i != posVar) {
          if (t[i] >= list[i].max()) {
            t[i] = list[i].min();
          } else {
            t[i] = list[i].domain.nextValue(t[i]);
            break;
          }
        }
      }

      if (!arraysEqual(is[l + 1], t)) {
        return l;
      } else {

        System.arraycopy(is[++l], 0, t, 0, list.length);
      }
    }

    return l;
  }

  @Override
  public void queueVariable(int level, Var v) {

    if (DEBUG_ALL) {
      log.debug("Var {} {}", v, ((IntVar) v).recentDomainPruning());
    }

    variableQueue.add(v);
  }
}
