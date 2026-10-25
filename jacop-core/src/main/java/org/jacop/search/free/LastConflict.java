/*
 * LastConflict.java
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
package org.jacop.search.free;

import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.search.Indomain;
import org.jacop.search.SelectChoicePoint;

/**
 * Last-conflict reasoning, lc(k) (Lecoutre et al. 2009; Gay et al. 2015): the variables of the last
 * k decisions that led to a failure are branched on first, most recent first, while they are
 * unfixed; otherwise the wrapped selection decides.
 *
 * <p>It is a {@link SearchMonitor}: add it to the {@link FreeSearch} it branches for.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LastConflict implements SelectChoicePoint<IntVar>, SearchMonitor {

  private final SelectChoicePoint<IntVar> select;
  private final Indomain<IntVar> indomain;
  private final Map<IntVar, Integer> variables;
  private final IntVar[] conflicts;
  private int size;

  private IntVar selected;
  private boolean fromConflict;

  /**
   * Wraps a selection with last-conflict reasoning.
   *
   * @param select the selection used when no conflict variable is unfixed.
   * @param indomain the value heuristic for conflict variables.
   * @param k the number of conflict variables kept.
   */
  public LastConflict(SelectChoicePoint<IntVar> select, Indomain<IntVar> indomain, int k) {
    if (k < 1) {
      throw new IllegalArgumentException("k must be at least 1");
    }
    this.select = select;
    this.indomain = indomain;
    this.variables = select.getVariablesMapping();
    this.conflicts = new IntVar[k];
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    for (int i = 0; i < size; i++) {
      if (!conflicts[i].singleton()) {
        selected = conflicts[i];
        fromConflict = true;
        return selected;
      }
    }
    fromConflict = false;
    selected = select.getChoiceVariable(index);
    return selected;
  }

  @Override
  public int getChoiceValue() {
    return fromConflict ? indomain.indomain(selected) : select.getChoiceValue();
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return select.getChoiceConstraint(index);
  }

  @Override
  public Map<IntVar, Integer> getVariablesMapping() {
    return variables;
  }

  @Override
  public int getIndex() {
    return fromConflict ? 0 : select.getIndex();
  }

  @Override
  public void onFailure(Constraint failed, Var decision) {
    if (!(decision instanceof IntVar v) || !variables.containsKey(v)) {
      return;
    }
    // move v to the front, keeping the others in order
    int i = 0;
    while (i < size && conflicts[i] != v) {
      i++;
    }
    if (i == size) {
      if (size < conflicts.length) {
        size++;
      }
      i = size - 1;
    }
    System.arraycopy(conflicts, 0, conflicts, 1, i);
    conflicts[0] = v;
  }

  @Override
  public void onRestart(FreeSearch search) {
    size = 0;
  }

  @Override
  public String toString() {
    return "LastConflict(" + conflicts.length + ", " + select + ")";
  }
}
