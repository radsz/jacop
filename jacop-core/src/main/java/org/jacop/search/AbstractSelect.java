/*
 * AbstractSelect.java
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

import java.util.Map;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * Abstract base class for variable selection heuristics that share common initialization and
 * accessor logic.
 *
 * @param <T> the type of variable being selected
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@SuppressWarnings("unchecked")
public abstract class AbstractSelect<T extends Var> implements SelectChoicePoint<T> {

  static final boolean DEBUG_ALL = false;

  /** The search variables managed by this selector. */
  public final T[] searchVariables;

  /** It stores the original positions of variables to be used for input order tie-breaking. */
  public final Map<T, Integer> position;

  /** The value ordering heuristic. */
  final Indomain<T> valueOrdering;

  /** Index of the currently selected variable. */
  int currentIndex;

  /**
   * Initializes common fields: deduplicates variables, builds searchVariables array and position
   * mapping.
   *
   * @param variables the variables upon which choice points are created
   * @param indomain the value heuristic to choose a value for a given variable
   */
  protected AbstractSelect(T[] variables, Indomain<T> indomain) {

    position = Var.createEmptyPositioning();

    int unique = 0;
    for (T variable : variables) {
      if (position.get(variable) == null) {
        position.put(variable, unique++);
      }
    }

    this.searchVariables = (T[]) new Var[position.size()];

    for (Map.Entry<T, Integer> e : position.entrySet()) {
      searchVariables[e.getValue()] = e.getKey();
    }

    valueOrdering = indomain;
  }

  /**
   * It returns a value which is the base of the next choice point. Only if choice is of an X = C
   * type.
   */
  @Override
  public int getChoiceValue() {

    assert currentIndex >= 0;
    assert currentIndex < searchVariables.length;
    assert searchVariables[currentIndex].dom() != null;

    return valueOrdering.indomain(searchVariables[currentIndex]);
  }

  /** It always returns null as choice point is obtained by getChoiceVariable and getChoiceValue. */
  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return null;
  }

  /** It returns the variables for which assignment in the solution is given. */
  @Override
  public Map<T, Integer> getVariablesMapping() {
    return position;
  }

  /**
   * It returns the current index. Supplying this value in the next invocation of select will make
   * search for next variable faster without compromising efficiency.
   */
  @Override
  public int getIndex() {
    return currentIndex;
  }

  /**
   * It gets as input the index of the variable which is chosen by search to be instantiated at this
   * stage. The variable is positioned at search position.
   *
   * @param searchPosition position at which search stores the currently chosen variable.
   * @param variablePosition current position of the variable chosen by search.
   * @return variable chosen to be a base of the choice point.
   */
  public T placeSearchVariable(int searchPosition, int variablePosition) {

    if (searchPosition != variablePosition) {

      T temp = searchVariables[searchPosition];

      searchVariables[searchPosition] = searchVariables[variablePosition];

      searchVariables[variablePosition] = temp;
    }

    return searchVariables[searchPosition];
  }
}
