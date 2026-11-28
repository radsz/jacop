/*
 * PickDom.java
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

import java.util.Arrays;
import org.jacop.constraints.Constraint;
import org.jacop.core.DomainChangeRecorder;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.Indomain;

/**
 * The pick/dom variable heuristic (Audemard, Lecoutre and Prud'homme, "Guiding backtrack search by
 * tracking variables during constraint propagation", CP 2023): when the propagation of a decision
 * fails, the variables that took part in it get points, and the selected variable has the largest
 * ratio of its points to its domain size. Ties go to the smaller domain, so it starts as dom.
 *
 * <p>The paper tracks the variables picked from a variable-oriented propagation queue, weighted by
 * the values their revisions removed. JaCoP propagates constraints, so here a variable takes part
 * when its own domain changed during the failed propagation (the decision variable included), and
 * its share is the number of its domain changes. The points follow mode 3 of the paper, its best:
 * 100 × (n - depth) / n points per failure, shared by the shares, so that failures near the root
 * count more; mode 0 gives each variable that took part one point.
 *
 * <p>The domain changes come from {@link Store#domainTracker}, which the heuristic takes when the
 * search starts and at each restart.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class PickDom extends ScoredSelect implements DomainChangeRecorder {

  private final double[] picks;
  private final boolean shared;

  /** The search position of each variable of the store, by its index, -1 if none. */
  private int[] byIndex = new int[0];

  private Store store;
  private FreeSearch search;

  /** The positions changed since the last decision, with their numbers of changes. */
  private final int[] changed;

  private int changedSize;
  private final int[] changes;

  /**
   * Creates the heuristic for the given variables, with the points of mode 3 of the paper.
   *
   * @param vars the variables to branch on.
   * @param indomain the value heuristic.
   */
  public PickDom(IntVar[] vars, Indomain<IntVar> indomain) {
    this(vars, indomain, 3);
  }

  /**
   * Creates the heuristic for the given variables.
   *
   * @param vars the variables to branch on.
   * @param indomain the value heuristic.
   * @param mode 3 to share 100 × (n - depth) / n points per failure by the numbers of changes, 0 to
   *     give one point to each variable that took part.
   */
  public PickDom(IntVar[] vars, Indomain<IntVar> indomain, int mode) {
    super(vars, indomain);
    if (mode != 0 && mode != 3) {
      throw new IllegalArgumentException("pick/dom mode must be 0 or 3, not " + mode);
    }
    shared = mode == 3;
    picks = new double[vars.length];
    changed = new int[vars.length];
    changes = new int[vars.length];
  }

  @Override
  double score(int i) {
    return picks[i];
  }

  /** Takes the domain tracker of the store, and maps the store indices of the variables. */
  private void install(FreeSearch s) {
    search = s;
    if (vars.length == 0) {
      return;
    }
    Store st = vars[0].getStore();
    if (st != store || byIndex.length != st.size()) {
      store = st;
      byIndex = new int[st.size()];
      Arrays.fill(byIndex, -1);
      for (int i = 0; i < vars.length; i++) {
        int si = vars[i].index();
        if (si >= 0 && si < byIndex.length && st.vars[si] == vars[i] && byIndex[si] < 0) {
          byIndex[si] = i;
        }
      }
    }
    st.domainTracker = this;
    clear();
  }

  private void clear() {
    for (int q = 0; q < changedSize; q++) {
      changes[changed[q]] = 0;
    }
    changedSize = 0;
  }

  private int position(IntVar x) {
    int si = x.index();
    if (si >= 0 && si < byIndex.length && store.vars[si] == x) {
      return byIndex[si];
    }
    Integer i = positions.get(x);
    return i == null ? -1 : i;
  }

  private void count(int i) {
    if (changes[i]++ == 0) {
      changed[changedSize++] = i;
    }
  }

  @Override
  public void domainChanged(IntVar x, int event) {
    int i = position(x);
    if (i >= 0) {
      count(i);
    }
  }

  @Override
  public void onStart(FreeSearch s) {
    install(s);
  }

  @Override
  public void onDecision(Var aVar, int value, boolean left) {
    clear();
    if (aVar instanceof IntVar v && store != null) {
      int i = position(v);
      if (i >= 0) {
        count(i);
      }
    }
  }

  @Override
  public void onFailure(Constraint failed, Var decision) {
    if (changedSize == 0) {
      return;
    }
    if (shared) {
      int n = vars.length;
      int depth = search == null ? 0 : Math.min(n, search.getDepth());
      long total = 0;
      for (int q = 0; q < changedSize; q++) {
        total += changes[changed[q]];
      }
      double points = 100.0d * (n - depth) / n / total;
      for (int q = 0; q < changedSize; q++) {
        int i = changed[q];
        picks[i] += points * changes[i];
      }
    } else {
      for (int q = 0; q < changedSize; q++) {
        picks[changed[q]] += 1.0d;
      }
    }
    clear();
  }

  @Override
  public void onRestart(FreeSearch s) {
    if (store == null || store.domainTracker != this) {
      install(s);
    } else {
      search = s;
      clear();
    }
  }

  @Override
  public String toString() {
    return "PickDom(" + vars.length + " variables, mode " + (shared ? 3 : 0) + ")";
  }
}
