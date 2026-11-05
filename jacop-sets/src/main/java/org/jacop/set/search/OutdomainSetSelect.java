/*
 * OutdomainSetSelect.java
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

package org.jacop.set.search;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.search.ComparatorVariable;
import org.jacop.search.Indomain;
import org.jacop.search.SimpleSelect;
import org.jacop.set.core.SetVar;

/**
 * Selects set variables as {@link SimpleSelect} does and decides the element its indomain picks,
 * but leaves the element out of the set in the left branch and puts it in only in the right one:
 * the outdomain_min and outdomain_max value choices of MiniZinc's set_search.
 *
 * @param <T> the type of the set variables
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class OutdomainSetSelect<T extends SetVar> extends SimpleSelect<T> {

  /**
   * Creates the selection.
   *
   * @param variables the variables to decide
   * @param varSelect the variable ordering, or null for input order
   * @param indomain the element to decide in the chosen variable
   */
  public OutdomainSetSelect(T[] variables, ComparatorVariable<T> varSelect, Indomain<T> indomain) {
    super(variables, varSelect, indomain);
  }

  /**
   * Creates the selection with a tie breaking variable ordering.
   *
   * @param variables the variables to decide
   * @param varSelect the variable ordering
   * @param tieBreakerVarSelect the ordering among variables equal under varSelect
   * @param indomain the element to decide in the chosen variable
   */
  public OutdomainSetSelect(
      T[] variables,
      ComparatorVariable<T> varSelect,
      ComparatorVariable<T> tieBreakerVarSelect,
      Indomain<T> indomain) {
    super(variables, varSelect, tieBreakerVarSelect, indomain);
  }

  @Override
  public T getChoiceVariable(int index) {
    return null;
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    T var = super.getChoiceVariable(index);
    if (var == null) {
      return null;
    }
    return new SetElementChoice(getChoiceValue(), var);
  }
}
