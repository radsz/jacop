/*
 * RandomSelect.java
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

import java.util.Arrays;
import java.util.Random;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * It is simple and customizable selector of decisions (constraints) which will be enforced by
 * search.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class RandomSelect<T extends Var> extends AbstractSelect<T> {

  final Random random = Store.seedPresent() ? new Random(Store.getSeed()) : new Random();

  /**
   * The constructor to create a simple choice select mechanism.
   *
   * @param variables variables upon which the choice points are created.
   * @param indomain the value heuristic to choose a value for a given variable.
   */
  public RandomSelect(T[] variables, Indomain<T> indomain) {
    super(variables, indomain);
  }

  /**
   * It returns the variable which is the base on the next choice point. Only if choice is of an X =
   * C type. This function returns null if all variables have a value assigned or a choice point
   * based on other type of constraint is being selected. The parameter index is the last value
   * which have been return by this SelectChoicePoint object which has not been backtracked upon
   * yet.
   */
  public T getChoiceVariable(int index) {

    assert index < searchVariables.length;

    if (debugAll) {
      log.debug("index = {}", index);

      StringBuilder vars = new StringBuilder();
      for (T searchVariable : searchVariables) {
        vars.append(searchVariable).append(" ");
      }
      log.debug("{}", vars);
    }

    int finalIndex = searchVariables.length;
    T currentVariable;

    do {

      int size = finalIndex - index;

      int selectedIndex = index + random.nextInt(size);
      currentVariable = placeSearchVariable(index, selectedIndex);

    } while (currentVariable.singleton() && ++index < finalIndex);

    if (index == finalIndex) {
      return null;
    } else {
      currentIndex = index;

      if (debugAll) {
        log.debug("selected {}", currentVariable);
      }

      return currentVariable;
    }
  }

  /**
   * It returns the string representation of the choice point selector.
   *
   * @return string describing the search variables.
   */
  public String toString() {
    return "" + Arrays.asList(searchVariables);
  }
}
