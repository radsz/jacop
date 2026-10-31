/*
 * LpGuidedSelect.java
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
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * Decisions from the last solution of the linear relaxation, as the LP search of CP-SAT's LP
 * workers: the unfixed 0/1 column whose value is the most fractional takes its rounded value, and
 * when no such column is fractional, an unfixed 0/1 column that the solution sets to 1 takes 1.
 * When the relaxation has no solution yet, or its solution fixes no unfixed 0/1 column, the
 * decision is the one of another selection.
 *
 * <p>The solution is the last one the simplex found, which can be from another branch: it guides,
 * and the propagation of the store decides.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LpGuidedSelect implements SelectChoicePoint<Var> {

  private static final double EPSILON = 1e-6;

  private final LinearRelaxation lp;
  private final SelectChoicePoint<? extends Var> fallback;

  // the last decision: from the relaxation, or of the other selection
  private boolean fromLp;
  private int value;

  /** Statistics: decisions taken from the relaxation. */
  public long lpDecisions;

  /**
   * Creates the selection.
   *
   * @param lp the linear relaxation
   * @param fallback the selection when the relaxation gives no decision, or null for none
   */
  public LpGuidedSelect(LinearRelaxation lp, SelectChoicePoint<? extends Var> fallback) {
    this.lp = lp;
    this.fallback = fallback;
  }

  @Override
  public Var getChoiceVariable(int index) {
    IntVar best = null;
    double bestScore = Double.POSITIVE_INFINITY;
    int bestValue = 0;
    IntVar one = null;
    IntVar objective = lp.objective();
    for (int j = 0; j < lp.solutionColumns(); j++) {
      IntVar x = lp.column(j);
      if (x == objective || x.singleton() || x.min() != 0 || x.max() != 1) {
        continue;
      }
      double v = lp.solutionValue(j);
      if (v > EPSILON && v < 1 - EPSILON) {
        double score = Math.abs(v - 0.5);
        if (score < bestScore) {
          bestScore = score;
          best = x;
          bestValue = v >= 0.5 ? 1 : 0;
        }
      } else if (one == null && v >= 1 - EPSILON) {
        one = x;
      }
    }
    if (best == null && one != null) {
      best = one;
      bestValue = 1;
    }
    if (best != null) {
      fromLp = true;
      value = bestValue;
      lpDecisions++;
      return best;
    }
    fromLp = false;
    return fallback == null ? null : fallback.getChoiceVariable(index);
  }

  @Override
  public int getChoiceValue() {
    return fromLp ? value : fallback.getChoiceValue();
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return fallback == null ? null : fallback.getChoiceConstraint(index);
  }

  @Override
  @SuppressWarnings("unchecked")
  public Map<Var, Integer> getVariablesMapping() {
    return fallback == null ? Map.of() : (Map<Var, Integer>) fallback.getVariablesMapping();
  }

  @Override
  public int getIndex() {
    return fromLp || fallback == null ? 0 : fallback.getIndex();
  }
}
