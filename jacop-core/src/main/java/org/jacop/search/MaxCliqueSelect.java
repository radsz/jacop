/*
 * MaxCliqueSelect.java
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

import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.constraints.MaxCliqueBound;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;

/**
 * The branching of maximum clique algorithms over the vertices of a {@link MaxCliqueBound}: the
 * vertex not yet fixed of the last color class first ({@link MaxCliqueBound#branchVertex()}), set
 * to 1, then to 0. E. Tomita and T. Seki, An efficient branch-and-bound algorithm for finding a
 * maximum clique, DMTCS 2003, LNCS 2731; E. Tomita, Y. Sutani, T. Higashi, S. Takahashi and M.
 * Wakatsuki, A simple and faster branch-and-bound algorithm for finding a maximum clique, WALCOM
 * 2010, LNCS 5942.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class MaxCliqueSelect implements SelectChoicePoint<IntVar> {

  private final MaxCliqueBound bound;

  private final Map<IntVar, Integer> positions = new IdentityHashMap<>();

  /**
   * It creates the branching.
   *
   * @param bound the bound whose vertices are branched on
   */
  public MaxCliqueSelect(MaxCliqueBound bound) {
    this.bound = bound;
    for (int i = 0; i < bound.x.length; i++) {
      positions.putIfAbsent(bound.x[i], i);
    }
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    int v = bound.branchVertex();
    return v < 0 ? null : bound.x[v];
  }

  @Override
  public int getChoiceValue() {
    return 1;
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return null;
  }

  @Override
  public Map<IntVar, Integer> getVariablesMapping() {
    return positions;
  }

  @Override
  public int getIndex() {
    return 0;
  }

  @Override
  public String toString() {
    return "MaxCliqueSelect(" + bound.x.length + " vertices)";
  }
}
