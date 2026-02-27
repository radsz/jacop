/*
 * SimpleMatrixSelect.java
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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * SimpleMatrixSelect selects first a row in the matrix based on metric of the variable at
 * pivotPosition. As soon as a row is choosen, variables starting from the beginning of the row
 * which are not assigned yet are selected. The row selection is done with the help of variable
 * comparators. Two comparators can be employed main and tiebreaking one. If two are not sufficient
 * to differentiate two rows than the lexigraphical ordering is used.
 *
 * <p>Default values: pivotPosition = 0, mainComparator = InputOrder, tieBreakingComparator =
 * InputOrder.
 *
 * @param <T> type of variable being used in the Search.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class SimpleMatrixSelect<T extends Var> implements SelectChoicePoint<T> {

  static final boolean DEBUG_ALL = false;

  /** It stores the original positions of variables to be used for input order tie-breaking. */
  public final Map<T, Integer> position = Var.createEmptyPositioning();

  /** It stores variables which need to be labelled. */
  public final List<List<T>> searchVariables = new ArrayList<>();

  /**
   * It decides if input order tiebreaking is used. If input tiebreaking is not used than the
   * current arrangement of row, variables within rows decides on the priority. The arrangement of
   * the rows, variables within rows depends on the search history. Setting it to false makes the
   * final tiebreaking a mixture of input-order/search history influenced tie breaking. It is faster
   * to compute tiebreaking and it may give interesting search history based tiebreaking.
   */
  public boolean inputOrderTieBreaking = true;

  /** It specifies the pivot position (first element has index 0). */
  public int pivotPosition;

  ComparatorVariable<T> mainComparator;
  ComparatorVariable<T> tieBreakingComparator;
  int primaryIndex;
  int secondaryIndex;
  Indomain<T> valueOrdering;

  /**
   * This constructor uses default values for all parameters. The size of the sublist is equal to
   * two. The pivot position points to the first element. The tiebreaking delete used is
   * DeleteMostConstrainedStatic.
   *
   * @param vars variables to choose from.
   * @param indomain value ordering heuristic used to choose a value for a given variable.
   */
  public SimpleMatrixSelect(T[][] vars, Indomain<T> indomain) {
    this(vars, null, null, indomain, 0);
  }

  /**
   * It constructs a MatrixSelection variable ordering.
   *
   * @param vars matrix of variables to be selected from.
   * @param mainComparator the variable comparator to choose the proper vector.
   * @param indomain variable ordering value to be used to determine value for a given variable.
   */
  public SimpleMatrixSelect(
      T[][] vars, ComparatorVariable<T> mainComparator, Indomain<T> indomain) {
    this(vars, mainComparator, null, indomain, 0);
  }

  /**
   * It constructs a MatrixSelection variable ordering.
   *
   * @param vars matrix of variables to be selected from.
   * @param mainComparator the variable comparator to choose the proper vector.
   * @param tieBreakingComparator the variable comparator used if the main comparator can not
   *     distinguish between vectors.
   * @param indomain variable ordering value to be used to determine value for a given variable.
   */
  public SimpleMatrixSelect(
      T[][] vars,
      ComparatorVariable<T> mainComparator,
      ComparatorVariable<T> tieBreakingComparator,
      Indomain<T> indomain) {
    this(vars, mainComparator, tieBreakingComparator, indomain, 0);
  }

  /**
   * This constructor allows to specify all parameters for the selection mechanism. Specifying
   * mainComparator or tieBreaking to value null do not use that functionality of the selection
   * mechanims.
   *
   * @param vars variables from which the base of the choice point is choosen.
   * @param mainComparator the main variable comparator used to compare variables.
   * @param tieBreakingComparator the secondary variable comparator used to break ties.
   * @param indomain the value ordering heuristic used to assign value to a chosen variable.
   * @param pivotPosition the position of the variable which is used to rank the rows.
   */
  public SimpleMatrixSelect(
      T[][] vars,
      ComparatorVariable<T> mainComparator,
      ComparatorVariable<T> tieBreakingComparator,
      Indomain<T> indomain,
      int pivotPosition) {

    if (ASSERTS_ENABLED && pivotPosition < 0) {
      throw new IllegalStateException(String.valueOf("Pivot position must be equal or greater 0"));
    }

    this.mainComparator = mainComparator;
    this.tieBreakingComparator = tieBreakingComparator;
    this.pivotPosition = pivotPosition;
    valueOrdering = indomain;

    int no = 0;

    for (T[] var : vars) {

      List<T> current = new ArrayList<>();

      if (ASSERTS_ENABLED && var.length <= pivotPosition) {
        throw new IllegalStateException("Assertion failed");
      }

      for (T t : var) {
        current.add(t);
        if (!position.containsKey(t)) {
          position.put(t, no++);
        }
      }

      searchVariables.add(current);
    }
  }

  /**
   * It returns the variable which is the base on the next choice point. Only if choice is of an X =
   * C type. This function returns null if all variables have a value assigned or a choice point
   * based on other type of constraint is being selected. The parameter index is the last value
   * which have been return by this SelectChoicePoint object which has not been backtracked upon
   * yet.
   */
  public T getChoiceVariable(int firstVariable) {

    if (ASSERTS_ENABLED && searchVariables.size() <= firstVariable) {
      throw new IllegalStateException(
          String.valueOf(
              "The position of the first entity to check is larger than the array size"));
    }

    int finalIndex = searchVariables.size();

    if (mainComparator == null) {
      return getChoiceVariableNoComparator(firstVariable, finalIndex);
    }

    T currentVariable = searchVariables.get(firstVariable).get(pivotPosition);

    if (currentVariable.singleton()) {
      int[] next = skipToFirstNonSingletonRow(firstVariable, finalIndex);
      firstVariable = next[0];
      if (firstVariable < 0) {
        return null;
      }
      currentVariable = searchVariables.get(firstVariable).get(pivotPosition);
    }

    double optimalMetric = mainComparator.metric(currentVariable);
    int optimalPosition = firstVariable;

    for (int currentPosition = firstVariable + 1; currentPosition < finalIndex; currentPosition++) {
      T v = searchVariables.get(currentPosition).get(pivotPosition);

      if (v.singleton()) {
        if (trySwapGroundedRow(firstVariable, currentPosition, optimalPosition)) {
          if (optimalPosition == firstVariable) {
            optimalPosition = currentPosition;
          }
          firstVariable++;
          continue;
        }
      }

      int comparison = mainComparator.compare(optimalMetric, v);
      if (comparison < 0) {
        optimalPosition = currentPosition;
        optimalMetric = mainComparator.metric(v);
      } else if (comparison == 0 && applyMatrixTieBreak(optimalPosition, currentPosition, v)) {
        optimalPosition = currentPosition;
      }
    }

    if (optimalPosition != firstVariable) {
      List<T> row = searchVariables.get(optimalPosition);
      // switch rows.
      searchVariables.set(optimalPosition, searchVariables.get(firstVariable));
      searchVariables.set(firstVariable, row);
      optimalPosition = firstVariable;
    }

    primaryIndex = optimalPosition;
    List<T> row = searchVariables.get(primaryIndex);
    for (int i = 0; i < row.size(); i++) {
      if (!row.get(i).singleton()) {
        secondaryIndex = i;
        break;
      }
    }

    return searchVariables.get(primaryIndex).get(secondaryIndex);
  }

  private T getChoiceVariableNoComparator(int firstVariable, int finalIndex) {
    while (firstVariable < finalIndex) {
      List<T> row = searchVariables.get(firstVariable);
      for (int i = 0; i < row.size(); i++) {
        if (!row.get(i).singleton()) {
          primaryIndex = firstVariable;
          secondaryIndex = i;
          return row.get(i);
        }
      }
      firstVariable++;
    }
    return null;
  }

  /** Returns true if row was all grounded and was swapped with firstVariable row. */
  private boolean trySwapGroundedRow(int firstVariable, int currentPosition, int optimalPosition) {
    List<T> row = searchVariables.get(currentPosition);
    if (!isRowAllGrounded(row)) {
      return false;
    }
    searchVariables.set(currentPosition, searchVariables.get(firstVariable));
    searchVariables.set(firstVariable, row);
    return true;
  }

  /**
   * Skips rows that are all singletons. Returns int[1] with new firstVariable, or -1 if no row
   * found (caller should return null).
   */
  private int[] skipToFirstNonSingletonRow(int firstVariable, int finalIndex) {
    while (firstVariable < finalIndex) {
      List<T> row = searchVariables.get(firstVariable);
      if (!isRowAllGrounded(row)) {
        return new int[] {firstVariable};
      }
      firstVariable++;
      if (firstVariable == finalIndex) {
        return new int[] {-1};
      }
      T currentVariable = searchVariables.get(firstVariable).get(pivotPosition);
      if (!currentVariable.singleton()) {
        return new int[] {firstVariable};
      }
    }
    return new int[] {-1};
  }

  private boolean isRowAllGrounded(List<T> row) {
    for (int i = row.size() - 1; i >= 0; i--) {
      if (!row.get(i).singleton()) {
        return false;
      }
    }
    return true;
  }

  private boolean applyMatrixTieBreak(int optimalPosition, int currentPosition, T v) {
    if (tieBreakingComparator != null) {
      int comp =
          tieBreakingComparator.compare(searchVariables.get(optimalPosition).get(pivotPosition), v);
      if (comp < 0) {
        return true;
      }
      if (comp == 0 && inputOrderTieBreaking) {
        return position.get(searchVariables.get(currentPosition).get(pivotPosition))
            < position.get(searchVariables.get(optimalPosition).get(pivotPosition));
      }
      return false;
    }
    if (inputOrderTieBreaking) {
      return position.get(searchVariables.get(currentPosition).get(pivotPosition))
          < position.get(searchVariables.get(optimalPosition).get(pivotPosition));
    }
    return false;
  }

  /**
   * It returns a value which is the base of the next choice point. Only if choice is of an X = C
   * type.
   */
  public int getChoiceValue() {

    if (ASSERTS_ENABLED && primaryIndex < 0) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && primaryIndex >= searchVariables.size()) {
      throw new IllegalStateException("Assertion failed");
    }

    return valueOrdering.indomain(searchVariables.get(primaryIndex).get(secondaryIndex));
  }

  /** It always returns null as choice point is obtained by getChoiceVariable and getChoiceValue. */
  public PrimitiveConstraint getChoiceConstraint(int index) {

    return null;
  }

  /** It returns the variables for which assignment in the solution is given. */
  public Map<T, Integer> getVariablesMapping() {

    return position;
  }

  /**
   * It returns the current index. Supplying this value in the next invocation of select will make
   * search for next variable faster without comprimising efficiency.
   */
  public int getIndex() {
    return primaryIndex;
  }

  /**
   * It returns the position of the pivot variable.
   *
   * @return the position of the pivot variable.
   */
  public int getPivotPosition() {
    return pivotPosition;
  }

  /**
   * It uses cheap method of breaking the ties. It is based on input order influenced by the search
   * history.
   */
  public void setDynamicLexTieBreaking() {
    inputOrderTieBreaking = false;
  }

  /**
   * It chooses input order tiebreaking if the supplied comparators can not distinguish between
   * matrix rows.
   */
  public void setInputOrderTieBreaking() {
    inputOrderTieBreaking = true;
  }

  /**
   * It returns the string representation of the choice point selector.
   *
   * @return string describing the search variables matrix.
   */
  public String toString() {
    return searchVariables + "\n";
  }
}
