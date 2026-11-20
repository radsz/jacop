/*
 * FrbaDom.java
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

import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.search.Indomain;

/**
 * The frba/dom variable heuristic, failure rate based search (Li, Yin and Li, "Failure based
 * variable ordering heuristics for solving CSPs", CP 2021, as defined in Audemard, Lecoutre and
 * Prud'homme, "Guiding backtrack search by tracking variables during constraint propagation", CP
 * 2023): each variable counts its assignments (left branches) and the assignments whose propagation
 * failed, and the selected variable has the largest (fr(x) + a(x)) / |dom(x)|, where fr(x) is the
 * failure rate and a(x) = 1 / (conflicts - conflict(x) + 1) rewards a recent failure. Only left
 * branches count, as in the original definition. Ties go to the smaller domain, so the heuristic
 * starts as dom.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class FrbaDom extends ScoredSelect {

  private final long[] assigns;
  private final long[] failures;
  private final long[] lastConflict;
  private long conflicts;

  /** The position of the variable of the last decision when it was a left branch, else -1. */
  private int lastAssigned = -1;

  /**
   * Creates the heuristic for the given variables.
   *
   * @param vars the variables to branch on.
   * @param indomain the value heuristic.
   */
  public FrbaDom(IntVar[] vars, Indomain<IntVar> indomain) {
    super(vars, indomain);
    assigns = new long[vars.length];
    failures = new long[vars.length];
    lastConflict = new long[vars.length];
  }

  @Override
  double score(int i) {
    if (assigns[i] == 0) {
      return 0.0d;
    }
    double age = failures[i] == 0 ? 0.0d : 1.0d / (conflicts - lastConflict[i] + 1);
    return (double) failures[i] / assigns[i] + age;
  }

  @Override
  public void onDecision(Var aVar, int value, boolean left) {
    lastAssigned = -1;
    if (left && aVar instanceof IntVar v) {
      Integer i = positions.get(v);
      if (i != null) {
        assigns[i]++;
        lastAssigned = i;
      }
    }
  }

  @Override
  public void onFailure(Constraint failed, Var decision) {
    conflicts++;
    if (lastAssigned >= 0 && decision == vars[lastAssigned]) {
      failures[lastAssigned]++;
      lastConflict[lastAssigned] = conflicts;
    }
    lastAssigned = -1;
  }

  @Override
  public void onRestart(FreeSearch search) {
    lastAssigned = -1;
  }

  @Override
  public String toString() {
    return "FrbaDom(" + vars.length + " variables)";
  }
}
