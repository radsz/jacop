/*
 * Solve.java
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
package org.jacop.fz;

import java.util.Map;
import java.util.function.BooleanSupplier;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;
import org.jacop.search.SelectChoicePoint;

/**
 * A branching that follows one selection while a condition holds and another once it no longer
 * does, such as one branching until the first solution and another afterwards. The positions the
 * selections return are their own, so the scan starts again from the first position when the
 * selection in use changes.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SwitchingSelect implements SelectChoicePoint<IntVar> {

  private final SelectChoicePoint<IntVar> first;
  private final SelectChoicePoint<IntVar> then;
  private final BooleanSupplier useFirst;
  private SelectChoicePoint<IntVar> current;

  /**
   * Creates the branching.
   *
   * @param first the selection while the condition holds
   * @param then the selection once it does not
   * @param useFirst the condition
   */
  SwitchingSelect(
      SelectChoicePoint<IntVar> first, SelectChoicePoint<IntVar> then, BooleanSupplier useFirst) {
    this.first = first;
    this.then = then;
    this.useFirst = useFirst;
    this.current = first;
  }

  // the selection in use now, and the position to scan it from
  private int select(int index) {
    SelectChoicePoint<IntVar> s = useFirst.getAsBoolean() ? first : then;
    if (s != current) {
      current = s;
      return 0;
    }
    return index;
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    int from = select(index);
    return current.getChoiceVariable(from);
  }

  @Override
  public int getChoiceValue() {
    return current.getChoiceValue();
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    int from = select(index);
    return current.getChoiceConstraint(from);
  }

  @Override
  public Map<IntVar, Integer> getVariablesMapping() {
    return current.getVariablesMapping();
  }

  @Override
  public int getIndex() {
    return current.getIndex();
  }
}
