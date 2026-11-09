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

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.constraints.lp.LpColumn;
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

  /**
   * Following the root solution, the largest share of value columns it may set strictly between 0
   * and 1: a root solution that is fractional on more of them does not point at a solution.
   */
  static final double ROOT_FRACTIONAL = 0.1;

  private final LinearRelaxation lp;
  private final SelectChoicePoint<? extends Var> fallback;
  private final boolean root;

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
    this(lp, fallback, false);
  }

  /**
   * Creates the selection.
   *
   * @param lp the linear relaxation
   * @param fallback the selection when the relaxation gives no decision, or null for none
   * @param root true to follow the relaxation's solution at the root (see {@link
   *     LinearRelaxation#rootSolutionValue}) instead of its last solution; it then gives no
   *     decision unless it has open value columns (see {@link LpColumn}) and at most a tenth of
   *     them are fractional
   */
  public LpGuidedSelect(
      LinearRelaxation lp, SelectChoicePoint<? extends Var> fallback, boolean root) {
    this.lp = lp;
    this.fallback = fallback;
    this.root = root;
    lp.keepSolutions();
  }

  // for a large relaxation, whose last solution stays as it is in search: its candidate columns in
  // the order the scan below picks them, the fractional ones nearest to 0.5 first and then those
  // at 1, each by index, and the solution they were taken from
  private int[] order;
  private int orderVersion = -1;

  @Override
  public Var getChoiceVariable(int index) {
    if (!root && lp.large()) {
      return chooseInOrder(index);
    }
    IntVar best = null;
    double bestScore = Double.POSITIVE_INFINITY;
    int bestValue = 0;
    IntVar one = null;
    int oneValue = 1;
    IntVar objective = lp.objective();
    int n = root ? lp.rootSolutionColumns() : lp.solutionColumns();
    int columns = 0;
    int fractional = 0;
    for (int j = 0; j < n; j++) {
      IntVar x = lp.column(j);
      if (x == objective) {
        continue;
      }
      // a value column [y = w] of the relaxation decides y = w (or y != w when rounded down)
      IntVar decided = x;
      int at = 1;
      if (x instanceof LpColumn c) {
        if (c.isArc() || c.isFree()) {
          // an arc of a layered graph is one of the edges of its value: the value column decides;
          // a free column decides nothing
          continue;
        }
        decided = c.variable();
        at = c.value();
        if (decided.singleton() || !decided.domain.contains(at)) {
          continue;
        }
      } else if (x.singleton() || x.min() != 0 || x.max() != 1) {
        continue;
      }
      double v = root ? lp.rootSolutionValue(j) : lp.solutionValue(j);
      boolean isFractional = v > EPSILON && v < 1 - EPSILON;
      if (x instanceof LpColumn) {
        columns++;
        fractional += isFractional ? 1 : 0;
      }
      if (isFractional) {
        double score = Math.abs(v - 0.5);
        if (score < bestScore && (v >= 0.5 || decided == x)) {
          bestScore = score;
          best = decided;
          bestValue = v >= 0.5 ? at : 0;
        }
      } else if (one == null && v >= 1 - EPSILON) {
        one = decided;
        oneValue = at;
      }
    }
    if (root && (columns == 0 || fractional > ROOT_FRACTIONAL * columns)) {
      best = null;
      one = null;
    }
    if (best == null && one != null) {
      best = one;
      bestValue = oneValue;
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

  // the decision of the scan of getChoiceVariable over the columns in the order of their values,
  // computed once per solution: the first open one in that order is the one the scan picks (the
  // least score, ties by index; else the first column at 1). A scan of every column at each
  // decision took most of the search on rcpsp-wet-diverse j60_19_6 (140,186 columns)
  private Var chooseInOrder(int index) {
    if (orderVersion != lp.solutionVersion()) {
      orderVersion = lp.solutionVersion();
      order = candidates();
    }
    for (int j : order) {
      IntVar x = lp.column(j);
      IntVar decided = x;
      int at = 1;
      if (x instanceof LpColumn c) {
        decided = c.variable();
        at = c.value();
        if (decided.singleton() || !decided.domain.contains(at)) {
          continue;
        }
      } else if (x.singleton() || x.min() != 0 || x.max() != 1) {
        continue;
      }
      double v = lp.solutionValue(j);
      boolean isFractional = v > EPSILON && v < 1 - EPSILON;
      if (isFractional && v < 0.5 && decided != x) {
        continue;
      }
      fromLp = true;
      value = !isFractional || v >= 0.5 ? at : 0;
      lpDecisions++;
      return decided;
    }
    fromLp = false;
    return fallback == null ? null : fallback.getChoiceVariable(index);
  }

  // the columns that can give a decision, fractional ones by score and index, then those at 1
  private int[] candidates() {
    IntVar objective = lp.objective();
    int n = lp.solutionColumns();
    List<Integer> fractional = new ArrayList<>();
    List<Integer> ones = new ArrayList<>();
    for (int j = 0; j < n; j++) {
      IntVar x = lp.column(j);
      if (x == objective || x instanceof LpColumn c && (c.isArc() || c.isFree())) {
        continue;
      }
      double v = lp.solutionValue(j);
      if (v > EPSILON && v < 1 - EPSILON) {
        fractional.add(j);
      } else if (v >= 1 - EPSILON) {
        ones.add(j);
      }
    }
    fractional.sort(
        Comparator.comparingDouble((Integer j) -> Math.abs(lp.solutionValue(j) - 0.5))
            .thenComparingInt(j -> j));
    int[] r = new int[fractional.size() + ones.size()];
    int k = 0;
    for (int j : fractional) {
      r[k++] = j;
    }
    for (int j : ones) {
      r[k++] = j;
    }
    return r;
  }

  @Override
  public int getChoiceValue() {
    return fromLp || fallback == null ? value : fallback.getChoiceValue();
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
