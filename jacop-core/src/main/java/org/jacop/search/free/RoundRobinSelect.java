/*
 * RoundRobinSelect.java
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

import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.search.SelectChoicePoint;

/**
 * Rotates several variable heuristics over the runs of a restarting search: the first heuristic
 * branches in the first runs, the next one in the following runs, and so on in a round robin, as
 * ACE-rr and ACE-mix did in the XCSP3 competitions of 2024 and 2025 (wdeg^ca.cd, pick/dom and
 * frba/dom; Lecoutre, ACE solver description, XCSP3 competition proceedings, arXiv 2412.00117 and
 * 2511.06918). Every heuristic sees every event, so each keeps learning from the runs of the
 * others.
 *
 * <p>It is a {@link SearchMonitor}: add it, and not its heuristics, to the {@link FreeSearch} it
 * branches for.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class RoundRobinSelect implements SelectChoicePoint<IntVar>, SearchMonitor {

  private final List<SelectChoicePoint<IntVar>> selects;
  private final List<SearchMonitor> monitors;
  private final int runsEach;
  private final long[] runs;
  private long restarts;
  private int active;

  /**
   * Creates the rotation.
   *
   * @param selects the heuristics, each also a {@link SearchMonitor} or not, in the order of the
   *     rotation; all over the same variables.
   * @param runsEach the number of consecutive runs each heuristic branches in.
   */
  public RoundRobinSelect(List<SelectChoicePoint<IntVar>> selects, int runsEach) {
    if (selects.isEmpty() || runsEach < 1) {
      throw new IllegalArgumentException("at least one heuristic and one run each");
    }
    this.selects = List.copyOf(selects);
    this.monitors =
        selects.stream()
            .filter(SearchMonitor.class::isInstance)
            .map(SearchMonitor.class::cast)
            .toList();
    this.runsEach = runsEach;
    this.runs = new long[selects.size()];
  }

  /**
   * Returns the heuristic that branches in the current run.
   *
   * @return its position in the rotation.
   */
  public int active() {
    return active;
  }

  /**
   * Returns the number of finished runs in which a heuristic branched.
   *
   * @param i the position of the heuristic in the rotation.
   * @return its runs so far.
   */
  public long runs(int i) {
    return runs[i];
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    return selects.get(active).getChoiceVariable(index);
  }

  @Override
  public int getChoiceValue() {
    return selects.get(active).getChoiceValue();
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return selects.get(active).getChoiceConstraint(index);
  }

  @Override
  public Map<IntVar, Integer> getVariablesMapping() {
    return selects.get(0).getVariablesMapping();
  }

  @Override
  public int getIndex() {
    return selects.get(active).getIndex();
  }

  @Override
  public void onStart(FreeSearch search) {
    for (SearchMonitor m : monitors) {
      m.onStart(search);
    }
  }

  @Override
  public void onDecision(Var aVar, int value, boolean left) {
    for (SearchMonitor m : monitors) {
      m.onDecision(aVar, value, left);
    }
  }

  @Override
  public void onDecision(PrimitiveConstraint choice, boolean left) {
    for (SearchMonitor m : monitors) {
      m.onDecision(choice, left);
    }
  }

  @Override
  public void onFailure(Constraint failed, Var decision) {
    for (SearchMonitor m : monitors) {
      m.onFailure(failed, decision);
    }
  }

  @Override
  public void onRestart(FreeSearch search) {
    for (SearchMonitor m : monitors) {
      m.onRestart(search);
    }
    runs[active]++;
    restarts++;
    active = (int) ((restarts / runsEach) % selects.size());
  }

  @Override
  public void onSolution(FreeSearch search) {
    for (SearchMonitor m : monitors) {
      m.onSolution(search);
    }
  }

  @Override
  public String toString() {
    StringBuilder b = new StringBuilder("RoundRobinSelect(");
    for (int i = 0; i < selects.size(); i++) {
      b.append(i == 0 ? "" : ", ")
          .append(selects.get(i))
          .append(": ")
          .append(runs[i])
          .append(" runs");
    }
    return b.append(')').toString();
  }
}
