/*
 * SequenceSelect.java
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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * Branches with several selections in sequence: the next selection is used only once all the
 * variables of the previous ones are fixed. It lets one search engine run what {@link
 * DepthFirstSearch} does with child searches, for example a {@code seq_search} annotation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SequenceSelect implements SelectChoicePoint<Var> {

  /** The index of a selection is kept in the bits above this shift, the selection's own below. */
  private static final int SHIFT = 24;

  private static final int LOCAL_MASK = (1 << SHIFT) - 1;

  private final SelectChoicePoint<? extends Var>[] selects;

  private int current;

  private PrimitiveConstraint pendingConstraint;

  /**
   * Creates a sequence of selections.
   *
   * @param selects the selections, in the order in which they are used.
   */
  @SuppressWarnings("unchecked")
  public SequenceSelect(List<? extends SelectChoicePoint<? extends Var>> selects) {
    if (selects.isEmpty() || selects.size() > (1 << (31 - SHIFT))) {
      throw new IllegalArgumentException("Between 1 and 128 selections are supported");
    }
    this.selects = selects.toArray(new SelectChoicePoint[0]);
  }

  @Override
  public Var getChoiceVariable(int index) {
    pendingConstraint = null;
    int first = index >>> SHIFT;
    for (int k = first; k < selects.length; k++) {
      int local = k == first ? index & LOCAL_MASK : 0;
      Var v = selects[k].getChoiceVariable(local);
      if (v != null) {
        current = k;
        return v;
      }
      PrimitiveConstraint c = selects[k].getChoiceConstraint(local);
      if (c != null) {
        current = k;
        pendingConstraint = c;
        return null;
      }
    }
    return null;
  }

  @Override
  public int getChoiceValue() {
    return selects[current].getChoiceValue();
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return pendingConstraint;
  }

  @Override
  public Map<Var, Integer> getVariablesMapping() {
    Map<Var, Integer> mapping = new HashMap<>();
    for (SelectChoicePoint<? extends Var> s : selects) {
      for (Map.Entry<? extends Var, Integer> e : s.getVariablesMapping().entrySet()) {
        mapping.putIfAbsent(e.getKey(), mapping.size());
      }
    }
    return mapping;
  }

  @Override
  public int getIndex() {
    return (current << SHIFT) | (selects[current].getIndex() & LOCAL_MASK);
  }

  @Override
  public String toString() {
    StringBuilder b = new StringBuilder("SequenceSelect[");
    for (int k = 0; k < selects.length; k++) {
      b.append(k > 0 ? ", " : "").append(selects[k]);
    }
    return b.append(']').toString();
  }
}
