/*
 * ExtensionalSupportVa.java
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Extensional constraint assures that one of the tuples is enforced in the relation.
 *
 * <p>This implementation tries to balance the usage of memory versus time efficiency.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class ExtensionalSupportVa extends AbstractExtensionalVa {

  static final boolean DEBUG_PRUNING = false;

  /** It specifies the id of the constraint. */
  static final AtomicInteger idNumber = new AtomicInteger(0);

  boolean firstConsistencyCheck = true;
  int levelOfFirstConsistencyCheck;

  LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<>();

  /**
   * Partial constructor which stores variables involved in a constraint but does not get
   * information about tuples yet. The tuples must set separately.
   *
   * @param list list of variables for the constraint
   */
  public ExtensionalSupportVa(IntVar[] list) {
    super(idNumber, list);
  }

  /**
   * The constructor does not create local copy of tuples array. Any changes to this array will
   * reflect on constraint behavior. Most probably incorrect as other data structures will not
   * change accordingly.
   *
   * @param variables the constraint scope.
   * @param tuples the tuples which are supports for the constraint.
   */
  public ExtensionalSupportVa(List<? extends IntVar> variables, int[][] tuples) {
    this(variables.toArray(new IntVar[0]), tuples);
  }

  /**
   * Constructor stores reference to tuples until imposition, any changes to tuples parameter will
   * be reflected in the constraint behavior. Changes to tuples should not performed under any
   * circumstances. The tuples array is not copied to save memory and time.
   *
   * @param list the constraint scope.
   * @param tuples the tuples which are supports for the constraint.
   */
  public ExtensionalSupportVa(IntVar[] list, int[][] tuples) {
    super(idNumber, list, tuples);
  }

  /**
   * It puts back tuples which have lost their support status at the level which is being removed.
   */
  @Override
  public void removeLevel(int level) {
    variableQueue = new LinkedHashSet<>();

    if (level == levelOfFirstConsistencyCheck) {
      firstConsistencyCheck = true;
    }
  }

  @Override
  public void consistency(Store store) {

    if (DEBUG_ALL) {
      log.debug("Begin {}", this);
    }

    if (firstConsistencyCheck) {

      int i = 0;

      for (IntVar v : list) {

        if (values[i].length == 0) {
          throw Store.failException;
        }

        IntervalDomain update = new IntervalDomain(values[i][0], values[i][0]);
        for (int j = 1; j < values[i].length; j++) {
          update.unionAdapt(values[i][j], values[i][j]);
        }
        v.domain.in(store.level, v, update);

        i++;
      }

      firstConsistencyCheck = false;
      levelOfFirstConsistencyCheck = store.level;
    }

    pruneUnsupported(store);

    if (DEBUG_ALL) {
      log.debug("End {}", this);
    }
  }

  @Override
  public void impose(Store store) {

    super.impose(store);
    filterAndIndexTuples(store);
    tuplesFromConstructor = null;
    firstConsistencyCheck = true;
    store.raiseLevelBeforeConsistency = true;
  }

  @Override
  public void queueVariable(int level, Var v) {

    if (DEBUG_ALL) {
      log.debug("Var {} {}", v, ((IntVar) v).recentDomainPruning());
    }

    variableQueue.add((IntVar) v);
  }

  /**
   * It seeks support for a given variable-value pair.
   *
   * @param varPosition position of the variable for which the support is seek.
   * @param value value for which the support is seek.
   * @return support tuple.
   */
  @Override
  public int[] seekSupportVa(int varPosition, int value) {
    if (DEBUG_ALL) {
      log.debug("Seeking support for {} and value {}", list[varPosition], value);
    }
    int[] t = setFirstValid(varPosition, value);
    while (true) {
      t = findFirstAllowed(varPosition, value, t);
      if (t == null) {
        return null;
      }
      int invalidPosition = seekInvalidPosition(t);
      if (invalidPosition == -1) {
        return t;
      }
      t = advanceToNextTuple(t, invalidPosition, varPosition);
      if (t == null) {
        return null;
      }
    }
  }

  /**
   * Advances tuple t to the next candidate by resetting positions after invalidPosition and
   * incrementing at or before invalidPosition. Returns null if no next candidate exists.
   */
  private int[] advanceToNextTuple(int[] t, int invalidPosition, int varPosition) {
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
          return t;
        }
      }
    }
    return null;
  }

  /**
   * It computes the first valid tuple for a given variable-value pair.
   *
   * @param varPosition position of the variable.
   * @param value value for which the fist valid tuple is seek.
   * @return first valid tuple.
   */
  public int[] setFirstValid(int varPosition, int value) {

    int[] t = new int[list.length];

    int noVars = list.length;
    for (int i = 0; i < noVars; i++) {
      t[i] = list[i].min();
    }

    t[varPosition] = value;

    return t;
  }

  /**
   * It finds the first allowed tuple from the given tuple.
   *
   * @param varPosition position of the variable.
   * @param value value for which first allowed tuple is seek.
   * @param t tuple from which the search commences.
   * @return first allowed tuple for a given variable-value pair.
   */
  public int[] findFirstAllowed(int varPosition, int value, int[] t) {

    if (DEBUG_ALL) {
      log.debug("variable {} position {} value {}", list[varPosition], varPosition, value);
    }

    int[][] tuplesForGivenVariableValuePair =
        tuples[varPosition][findPosition(value, values[varPosition])];

    int index = binarySearchAllowedTuple(t, tuplesForGivenVariableValuePair);
    if (index < 0) {
      return null;
    }
    System.arraycopy(tuplesForGivenVariableValuePair[index], 0, t, 0, list.length);
    return t;
  }

  private int binarySearchAllowedTuple(int[] t, int[][] tuplesForGivenVariableValuePair) {
    int left = 0;
    int right = tuplesForGivenVariableValuePair.length - 1;

    if (!(smaller(t, tuplesForGivenVariableValuePair[right])
        || arraysEqual(t, tuplesForGivenVariableValuePair[right]))) {
      return -1;
    }

    int position = (left + right) >> 1;

    while (left + 1 < right) {
      if (smaller(t, tuplesForGivenVariableValuePair[position])) {
        right = position;
      } else {
        left = position;
      }
      position = (left + right) >> 1;
    }

    if (smaller(t, tuplesForGivenVariableValuePair[left])
        || arraysEqual(t, tuplesForGivenVariableValuePair[left])) {
      return left;
    }
    return right;
  }
}
