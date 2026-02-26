/*
 * SimpleSelect.java
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

package org.jacop.search;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.Arrays;
import org.jacop.core.Var;

/**
 * It is simple and customizable selector of decisions (constraints) which will be enforced by
 * search.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class SimpleSelect<T extends Var> extends AbstractSelect<T> {

  public final ComparatorVariable<T> variableOrdering;

  /** It chooses if input order tie breaking is used. */
  public boolean inputOrderTieBreaking = true;

  public ComparatorVariable<T> tieBreakingComparator;

  /**
   * The constructor to create a simple choice select mechanism.
   *
   * @param variables variables upon which the choice points are created.
   * @param varSelect the variable comparator to choose the variable.
   * @param indomain the value heuristic to choose a value for a given variable.
   */
  public SimpleSelect(T[] variables, ComparatorVariable<T> varSelect, Indomain<T> indomain) {

    super(variables, indomain);
    variableOrdering = varSelect;
  }

  /**
   * It constructs a simple selection mechanism for choice points.
   *
   * @param variables variables used as basis of the choice point.
   * @param varSelect the main variable comparator.
   * @param tieBreakerVarSelect secondary variable comparator employed if the first one gives the
   *     same metric.
   * @param indomain the heuristic to choose value assigned to a chosen variable.
   */
  public SimpleSelect(
      T[] variables,
      ComparatorVariable<T> varSelect,
      ComparatorVariable<T> tieBreakerVarSelect,
      Indomain<T> indomain) {

    super(variables, indomain);
    variableOrdering = varSelect;
    tieBreakingComparator = tieBreakerVarSelect;

    if (tieBreakingComparator != null) {
      inputOrderTieBreaking = false;
    }
  }

  /**
   * It returns the variable which is the base on the next choice point. Only if choice is of an X =
   * C type. This function returns null if all variables have a value assigned or a choice point
   * based on other type of constraint is being selected. The parameter index is the last value
   * which have been return by this SelectChoicePoint object which has not been backtracked upon
   * yet.
   */
  public T getChoiceVariable(int index) {

    if (ASSERTS_ENABLED && !(index < searchVariables.length)) {
      throw new IllegalStateException("Assertion failed");
    }

    int finalIndex = searchVariables.length;
    T currentVariable;

    do {
      currentVariable = searchVariables[index];
    } while (currentVariable.singleton() && ++index < finalIndex);

    if (index == finalIndex) {
      return null;
    }

    if (variableOrdering == null || index + 1 == finalIndex) {
      currentIndex = index;
      return searchVariables[currentIndex];
    }

    double optimalMetric = variableOrdering.metric(currentVariable);
    int optimalPosition = index;

    for (int currentPosition = index + 1; currentPosition < finalIndex; currentPosition++) {
      T v = searchVariables[currentPosition];

      if (v.singleton()) {
        int[] next = handleSingletonAtPosition(index, currentPosition, optimalPosition);
        index = next[0];
        optimalPosition = next[1];
        continue;
      }

      int comparison = variableOrdering.compare(optimalMetric, v);
      if (comparison < 0) {
        optimalPosition = currentPosition;
        optimalMetric = variableOrdering.metric(v);
      } else if (comparison == 0) {
        optimalPosition =
            applyTieBreak(optimalPosition, currentPosition, v) ? currentPosition : optimalPosition;
      }
    }

    if (index != optimalPosition) {
      placeSearchVariable(index, optimalPosition);
    }

    this.currentIndex = index;
    return searchVariables[index];
  }

  /**
   * Handles a singleton variable at currentPosition: moves it and advances index. Returns new int[]
   * { index, optimalPosition }.
   */
  private int[] handleSingletonAtPosition(int index, int currentPosition, int optimalPosition) {
    if (index == optimalPosition) {
      placeSearchVariable(index, currentPosition);
      return new int[] {index + 1, currentPosition};
    }
    while (index < currentPosition && searchVariables[index].singleton()) {
      index++;
    }
    if (index != currentPosition) {
      placeSearchVariable(index, currentPosition);
      if (index == optimalPosition) {
        optimalPosition = currentPosition;
      }
      index++;
    }
    return new int[] {index, optimalPosition};
  }

  /**
   * Applies tie-breaking between variables at optimalPosition and currentPosition. Returns true if
   * currentPosition should become the new optimal.
   */
  private boolean applyTieBreak(int optimalPosition, int currentPosition, T v) {
    if (tieBreakingComparator != null) {
      int comp = tieBreakingComparator.compare(searchVariables[optimalPosition], v);
      if (comp < 0) {
        return true;
      }
      if (comp == 0 && inputOrderTieBreaking) {
        return position.get(searchVariables[currentPosition])
            < position.get(searchVariables[optimalPosition]);
      }
      return false;
    }
    if (inputOrderTieBreaking) {
      return position.get(searchVariables[currentPosition])
          < position.get(searchVariables[optimalPosition]);
    }
    return false;
  }

  /**
   * It returns the string representation of the choice point selector.
   *
   * @return string describing the variables, ordering, and value selection heuristic.
   */
  public String toString() {
    return Arrays.asList(searchVariables)
        + ", SimpleSelect("
        + variableOrdering
        + ", "
        + tieBreakingComparator
        + ", "
        + valueOrdering
        + ")";
  }
}
