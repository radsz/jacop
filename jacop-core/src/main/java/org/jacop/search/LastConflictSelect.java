/*
 * LastConflictSelect.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * Last-conflict reasoning, lc(1) (Lecoutre et al. 2009), for a {@link DepthFirstSearch}: when the
 * left branch of a decision fails, its variable is branched on again first, as long as it is not
 * fixed; otherwise the wrapped selection decides. The search keeps coming back to a variable that
 * no value fits, so a search over variables the model defines only loosely, such as the labels of
 * the cycles of a graph whose successors an earlier search fixed, backtracks to the decision that
 * caused the failure instead of trying every combination of the variables between them.
 *
 * <p>The conflict variable is kept when the search fails and is called again as a sub-search of a
 * master search, as Choco's {@code Search.lastConflict} does for the complementary search of a
 * FlatZinc model.
 *
 * @param <T> type of the variables.
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LastConflictSelect<T extends IntVar> implements SelectChoicePoint<T> {

  private final SelectChoicePoint<T> select;
  private final Indomain<T> indomain;

  private T conflict;
  private T selected;
  private int index;

  /**
   * Wraps a selection with last-conflict reasoning. With a {@link SplitSelect} a conflict variable
   * is split as the selection splits its own variables; otherwise it gets the value of indomain.
   *
   * @param select the selection used when the conflict variable is fixed.
   * @param indomain the value heuristic for the conflict variable, unless select is a SplitSelect.
   */
  public LastConflictSelect(SelectChoicePoint<T> select, Indomain<T> indomain) {
    this.select = select;
    this.indomain = indomain;
  }

  /**
   * Records the variable of a decision whose left branch failed, if it is one of the variables of
   * this selection. {@link DepthFirstSearch} calls it.
   *
   * @param var the variable of the failed decision.
   */
  @SuppressWarnings("unchecked")
  public void failedDecision(Var var) {
    if (var != null && select.getVariablesMapping().containsKey(var)) {
      conflict = (T) var;
    }
  }

  private boolean conflictOpen() {
    return conflict != null && !conflict.singleton();
  }

  @Override
  public T getChoiceVariable(int index) {
    this.index = index;
    if (conflictOpen()) {
      selected = conflict;
      return select instanceof SplitSelect ? null : conflict;
    }
    selected = null;
    return select.getChoiceVariable(index);
  }

  @Override
  public int getChoiceValue() {
    return selected != null ? indomain.indomain(selected) : select.getChoiceValue();
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    if (selected != null && select instanceof SplitSelect<T> split) {
      return split.getChoiceConstraint(selected);
    }
    return select.getChoiceConstraint(index);
  }

  @Override
  public Map<T, Integer> getVariablesMapping() {
    return select.getVariablesMapping();
  }

  @Override
  public int getIndex() {
    // a conflict variable is chosen out of order, so the variables before it are still to be done
    return selected != null ? index : select.getIndex();
  }

  @Override
  public String toString() {
    return "LastConflictSelect(" + select + ")";
  }
}
