/*
 * DomWdeg.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.search.Indomain;
import org.jacop.search.SelectChoicePoint;

/**
 * The dom/wdeg variable heuristic (Boussemart et al. 2004): every constraint has a weight, one more
 * each time its propagation fails, and the selected variable has the smallest ratio of its domain
 * size to the sum of the weights of its constraints that have at least one other unfixed variable.
 * Weights are kept across restarts.
 *
 * <p>It is a {@link SearchMonitor}: add it to the {@link FreeSearch} it branches for, so that it
 * sees the failures. Ties go to the variable given first.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class DomWdeg implements SelectChoicePoint<IntVar>, SearchMonitor {

  private final IntVar[] vars;
  private final Indomain<IntVar> indomain;

  private final Map<Constraint, Integer> constraintIndex = new IdentityHashMap<>();
  private final Var[][] scopes;
  private final double[] weights;
  private final int[][] varConstraints;

  /** Whether a constraint has two unfixed variables, computed once per selection. */
  private final boolean[] future;

  private final long[] futureStamp;
  private long stamp;

  private IntVar selected;

  /**
   * Creates the heuristic for the given variables. The constraints are those attached to the
   * variables when it is created.
   *
   * @param vars the variables to branch on.
   * @param indomain the value heuristic.
   */
  public DomWdeg(IntVar[] vars, Indomain<IntVar> indomain) {
    this.vars = vars.clone();
    this.indomain = indomain;
    List<Var[]> scopeList = new ArrayList<>();
    varConstraints = new int[vars.length][];
    for (int i = 0; i < vars.length; i++) {
      List<Constraint> cs = vars[i].dom().constraints();
      int[] indices = new int[cs.size()];
      int n = 0;
      for (Constraint c : cs) {
        Integer k = constraintIndex.get(c);
        if (k == null) {
          k = scopeList.size();
          constraintIndex.put(c, k);
          scopeList.add(c.arguments().toArray(new Var[0]));
        }
        if (!contains(indices, n, k)) {
          indices[n++] = k;
        }
      }
      varConstraints[i] = Arrays.copyOf(indices, n);
    }
    scopes = scopeList.toArray(new Var[0][]);
    weights = new double[scopes.length];
    Arrays.fill(weights, 1.0d);
    future = new boolean[scopes.length];
    futureStamp = new long[scopes.length];
  }

  private static boolean contains(int[] a, int n, int k) {
    for (int i = 0; i < n; i++) {
      if (a[i] == k) {
        return true;
      }
    }
    return false;
  }

  private boolean hasTwoUnfixed(int k) {
    if (futureStamp[k] != stamp) {
      futureStamp[k] = stamp;
      int unfixed = 0;
      for (Var v : scopes[k]) {
        if (!v.singleton() && ++unfixed == 2) {
          break;
        }
      }
      future[k] = unfixed >= 2;
    }
    return future[k];
  }

  /**
   * Returns the weighted degree of a variable: the sum of the weights of its constraints with at
   * least one other unfixed variable.
   *
   * @param i the position of the variable.
   * @return the weighted degree.
   */
  double weightedDegree(int i) {
    double w = 0.0d;
    for (int k : varConstraints[i]) {
      if (hasTwoUnfixed(k)) {
        w += weights[k];
      }
    }
    return w;
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    stamp++;
    selected = null;
    double best = Double.MAX_VALUE;
    for (int i = 0; i < vars.length; i++) {
      IntVar v = vars[i];
      if (v.singleton()) {
        continue;
      }
      double w = weightedDegree(i);
      // a variable without constraints left comes last, smaller domains first
      double score = w > 0.0d ? v.getSize() / w : Double.MAX_VALUE / 2 + v.getSize();
      if (selected == null || score < best) {
        best = score;
        selected = v;
      }
    }
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
    Map<IntVar, Integer> mapping = new IdentityHashMap<>();
    for (int i = 0; i < vars.length; i++) {
      mapping.putIfAbsent(vars[i], i);
    }
    return mapping;
  }

  @Override
  public int getIndex() {
    return 0;
  }

  @Override
  public void onFailure(Constraint failed, Var decision) {
    if (failed != null) {
      Integer k = constraintIndex.get(failed);
      if (k != null) {
        weights[k] += 1.0d;
      }
    }
  }

  @Override
  public String toString() {
    return "DomWdeg(" + vars.length + " variables, " + indomain + ")";
  }
}
