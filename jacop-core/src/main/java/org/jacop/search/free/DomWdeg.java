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
 * <p>Two refinements of the weights are available through {@link Weighting}: wdeg^ca.cd (Wattez et
 * al. 2019), with a weight per constraint and variable, and CHS, conflict history search (Habet and
 * Terrioux 2021), where the weight of a constraint rewards recent failures and decays.
 *
 * <p>It is a {@link SearchMonitor}: add it to the {@link FreeSearch} it branches for, so that it
 * sees the failures. Ties go to the variable given first.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class DomWdeg implements SelectChoicePoint<IntVar>, SearchMonitor {

  /** How the weights are updated when a constraint fails. */
  public enum Weighting {
    /** The weight of the failed constraint grows by one (Boussemart et al. 2004). */
    WDEG,
    /**
     * Each unfixed variable of the failed constraint gets its own weight for that constraint, which
     * grows by one divided by the number of unfixed variables of the constraint and by the domain
     * size of the variable (wdeg^ca.cd, Wattez et al. 2019).
     */
    CACD,
    /**
     * The weight of the failed constraint moves towards a reward that is larger when the constraint
     * failed recently; weights decay between restarts (conflict history search, Habet and Terrioux
     * 2021).
     */
    CHS
  }

  private static final double CHS_ALPHA = 0.1d;
  private static final double CHS_ALPHA_MIN = 0.06d;
  private static final double CHS_ALPHA_STEP = 1e-6d;
  private static final double CHS_DECAY = 0.995d;
  private static final double CHS_DELTA = 1e-4d;

  private final IntVar[] vars;
  private final Indomain<IntVar> indomain;
  private final Weighting weighting;

  private final Map<Constraint, Integer> constraintIndex = new IdentityHashMap<>();
  private final Var[][] scopes;
  private final double[] weights;
  private final int[][] varConstraints;

  /**
   * For wdeg^ca.cd, the weight of each constraint of a variable, in the order of varConstraints.
   */
  private final double[][] varWeights;

  /** For wdeg^ca.cd, the positions i and j in varWeights of the variables of each constraint. */
  private final int[][] scopePositions;

  /**
   * For CHS, the number of failures so far and the failure count when each constraint last failed.
   */
  private long conflicts;

  private final long[] lastConflict;
  private double alpha = CHS_ALPHA;

  /** Added to the weight of every constraint; for CHS, so that the degree breaks ties at first. */
  private final double offset;

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
    this(vars, indomain, Weighting.WDEG);
  }

  /**
   * Creates the heuristic for the given variables with the given weighting. The constraints are
   * those attached to the variables when it is created.
   *
   * @param vars the variables to branch on.
   * @param indomain the value heuristic.
   * @param weighting how the weights are updated on failures.
   */
  public DomWdeg(IntVar[] vars, Indomain<IntVar> indomain, Weighting weighting) {
    this.vars = vars.clone();
    this.indomain = indomain;
    this.weighting = weighting;
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
    Arrays.fill(weights, weighting == Weighting.CHS ? 0.0d : 1.0d);
    offset = weighting == Weighting.CHS ? CHS_DELTA : 0.0d;
    future = new boolean[scopes.length];
    futureStamp = new long[scopes.length];
    lastConflict = new long[scopes.length];
    if (weighting == Weighting.CACD) {
      varWeights = new double[vars.length][];
      int[] counts = new int[scopes.length];
      for (int i = 0; i < vars.length; i++) {
        varWeights[i] = new double[varConstraints[i].length];
        Arrays.fill(varWeights[i], 1.0d);
        for (int k : varConstraints[i]) {
          counts[k]++;
        }
      }
      scopePositions = new int[scopes.length][];
      for (int k = 0; k < scopes.length; k++) {
        scopePositions[k] = new int[2 * counts[k]];
        counts[k] = 0;
      }
      for (int i = 0; i < vars.length; i++) {
        for (int j = 0; j < varConstraints[i].length; j++) {
          int k = varConstraints[i][j];
          scopePositions[k][counts[k]++] = i;
          scopePositions[k][counts[k]++] = j;
        }
      }
    } else {
      varWeights = null;
      scopePositions = null;
    }
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
    int[] constraints = varConstraints[i];
    for (int j = 0; j < constraints.length; j++) {
      int k = constraints[j];
      if (hasTwoUnfixed(k)) {
        w += varWeights == null ? weights[k] + offset : varWeights[i][j];
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
    Integer k = failed == null ? null : constraintIndex.get(failed);
    if (k != null) {
      switch (weighting) {
        case WDEG -> weights[k] += 1.0d;
        case CACD -> increaseVariableWeights(k);
        case CHS -> {
          double reward = 1.0d / (conflicts - lastConflict[k] + 1);
          weights[k] = (1.0d - alpha) * weights[k] + alpha * reward;
          lastConflict[k] = conflicts;
        }
      }
    }
    conflicts++;
    if (alpha > CHS_ALPHA_MIN) {
      alpha -= CHS_ALPHA_STEP;
    }
  }

  private void increaseVariableWeights(int k) {
    int[] positions = scopePositions[k];
    int unfixed = 0;
    for (int p = 0; p < positions.length; p += 2) {
      if (!vars[positions[p]].singleton()) {
        unfixed++;
      }
    }
    for (int p = 0; p < positions.length; p += 2) {
      IntVar v = vars[positions[p]];
      if (!v.singleton()) {
        // the domain may be empty in the failed state
        varWeights[positions[p]][positions[p + 1]] +=
            1.0d / ((double) unfixed * Math.max(1, v.getSize()));
      }
    }
  }

  @Override
  public void onRestart(FreeSearch search) {
    if (weighting == Weighting.CHS) {
      alpha = CHS_ALPHA;
      for (int k = 0; k < weights.length; k++) {
        weights[k] *= Math.pow(CHS_DECAY, (double) conflicts - lastConflict[k]);
      }
    }
  }

  @Override
  public String toString() {
    return "DomWdeg(" + vars.length + " variables, " + weighting + ", " + indomain + ")";
  }
}
