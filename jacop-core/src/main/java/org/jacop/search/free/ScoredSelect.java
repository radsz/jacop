/*
 * ScoredSelect.java
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

import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.TrailedInts;
import org.jacop.search.Indomain;
import org.jacop.search.SelectChoicePoint;

/**
 * A variable heuristic that selects the unfixed variable with the largest score divided by its
 * domain size; ties go to the smaller domain, then to the variable given first. The unfixed
 * variables are kept in a reversible sparse set, so a selection visits only them.
 *
 * <p>Subclasses learn their scores as {@link SearchMonitor}s: add them to the {@link FreeSearch}
 * they branch for.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
abstract class ScoredSelect implements SelectChoicePoint<IntVar>, SearchMonitor {

  final IntVar[] vars;
  private final Indomain<IntVar> indomain;
  final Map<IntVar, Integer> positions = new IdentityHashMap<>();

  /** The search positions: the unfixed ones first, then those seen fixed, removed.get(0) many. */
  private final int[] order;

  private TrailedInts removed;
  private IntVar selected;

  ScoredSelect(IntVar[] vars, Indomain<IntVar> indomain) {
    this.vars = vars.clone();
    this.indomain = indomain;
    order = new int[vars.length];
    for (int i = 0; i < vars.length; i++) {
      order[i] = i;
      positions.putIfAbsent(vars[i], i);
    }
  }

  /**
   * Returns the score of a search variable; larger is selected first.
   *
   * @param i the position of the variable
   * @return its score, at least 0
   */
  abstract double score(int i);

  @Override
  public IntVar getChoiceVariable(int index) {
    selected = null;
    if (vars.length == 0) {
      return null;
    }
    if (removed == null) {
      removed = new TrailedInts(vars[0].getStore(), 1);
    }
    double best = -1.0d;
    int bestSize = Integer.MAX_VALUE;
    int bestIndex = Integer.MAX_VALUE;
    int size = vars.length - removed.get(0);
    int p = 0;
    while (p < size) {
      int i = order[p];
      IntVar v = vars[i];
      if (v.singleton()) {
        size--;
        order[p] = order[size];
        order[size] = i;
        continue;
      }
      p++;
      int d = v.getSize();
      double s = score(i) / d;
      if (s > best || (s == best && (d < bestSize || (d == bestSize && i < bestIndex)))) {
        best = s;
        bestSize = d;
        bestIndex = i;
        selected = v;
      }
    }
    removed.set(0, vars.length - size);
    return selected;
  }

  @Override
  public int getChoiceValue() {
    return indomain.indomain(selected);
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return null;
  }

  @Override
  public Map<IntVar, Integer> getVariablesMapping() {
    return new IdentityHashMap<>(positions);
  }

  @Override
  public int getIndex() {
    return 0;
  }
}
