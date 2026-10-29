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
import org.jacop.core.TrailedInts;
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
 * <p>The selection is incremental: the unfixed search variables and the unfixed variables of the
 * constraints are kept in reversible sparse sets, and each constraint counts its unfixed variables,
 * so a selection visits only the unfixed variables and not the scopes of their constraints.
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
  private final double[] weights;
  private final int[][] varConstraints;

  /** The distinct variables of the constraints' scopes. */
  private final Var[] scopeVars;

  /** For each scope variable, the constraint of each of its occurrences in a scope. */
  private final int[][] occurrences;

  /** For each constraint, the number of occurrences of unfixed variables in its scope. */
  private final int[] unfixed;

  /**
   * Sparse sets of the search variables and of the scope variables: the elements not seen fixed
   * come first, and those seen fixed last, as many as counted in {@link #removed}.
   */
  private final int[] searchOrder;

  private final int[] scopeOrder;

  /**
   * The number of elements seen fixed in each sparse set, restored on backtracking; created at the
   * first selection. Zero, the initial value, holds at every level.
   */
  private TrailedInts removed;

  /** The size of the scope variable set that {@link #unfixed} counts. */
  private int countedScopeSize;

  /**
   * For wdeg^ca.cd, the weight of each constraint of a variable, in the order of varConstraints.
   */
  private final double[][] varWeights;

  /**
   * For wdeg and wdeg^ca.cd, the positions i of the search variables of each constraint, each
   * followed by the position j of the constraint in varConstraints[i].
   */
  private final int[][] scopePositions;

  /**
   * For wdeg, the weighted degree of each search variable, kept up to date as constraints get fewer
   * than two unfixed variables and as weights grow. The weights are whole numbers, so the sums are
   * exact and equal to those of {@link #weightedDegree(int)}.
   */
  private final double[] degrees;

  /**
   * For CHS, the number of failures so far and the failure count when each constraint last failed.
   */
  private long conflicts;

  private final long[] lastConflict;
  private double alpha = CHS_ALPHA;

  /** Added to the weight of every constraint; for CHS, so that the degree breaks ties at first. */
  private final double offset;

  private IntVar selected;

  private int flushEvery;
  private long restarts;

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
    int constraints = scopeList.size();
    weights = new double[constraints];
    Arrays.fill(weights, weighting == Weighting.CHS ? 0.0d : 1.0d);
    offset = weighting == Weighting.CHS ? CHS_DELTA : 0.0d;
    lastConflict = new long[constraints];
    unfixed = new int[constraints];
    Map<Var, Integer> scopeIndex = new IdentityHashMap<>();
    List<Var> scopeVarList = new ArrayList<>();
    int[] occurrenceCounts = new int[0];
    for (Var[] scope : scopeList) {
      for (Var v : scope) {
        Integer x = scopeIndex.get(v);
        if (x == null) {
          x = scopeVarList.size();
          scopeIndex.put(v, x);
          scopeVarList.add(v);
          if (x == occurrenceCounts.length) {
            occurrenceCounts = Arrays.copyOf(occurrenceCounts, 2 * x + 8);
          }
        }
        occurrenceCounts[x]++;
      }
    }
    scopeVars = scopeVarList.toArray(new Var[0]);
    occurrences = new int[scopeVars.length][];
    for (int x = 0; x < scopeVars.length; x++) {
      occurrences[x] = new int[occurrenceCounts[x]];
      occurrenceCounts[x] = 0;
    }
    for (int k = 0; k < constraints; k++) {
      Var[] scope = scopeList.get(k);
      unfixed[k] = scope.length;
      for (Var v : scope) {
        int x = scopeIndex.get(v);
        occurrences[x][occurrenceCounts[x]++] = k;
      }
    }
    countedScopeSize = scopeVars.length;
    scopeOrder = identity(scopeVars.length);
    searchOrder = identity(vars.length);
    if (weighting == Weighting.CACD) {
      varWeights = new double[vars.length][];
      for (int i = 0; i < vars.length; i++) {
        varWeights[i] = new double[varConstraints[i].length];
        Arrays.fill(varWeights[i], 1.0d);
      }
    } else {
      varWeights = null;
    }
    if (weighting != Weighting.CHS) {
      int[] counts = new int[constraints];
      for (int i = 0; i < vars.length; i++) {
        for (int k : varConstraints[i]) {
          counts[k]++;
        }
      }
      scopePositions = new int[constraints][];
      for (int k = 0; k < constraints; k++) {
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
      scopePositions = null;
    }
    degrees = weighting == Weighting.WDEG ? new double[vars.length] : null;
    computeDegrees();
  }

  /** Computes the cached weighted degrees from the weights and the unfixed counts. */
  private void computeDegrees() {
    if (degrees != null) {
      for (int i = 0; i < vars.length; i++) {
        degrees[i] = weightedDegree(i);
      }
    }
  }

  /** Adds a change of the weight of a constraint to the cached degrees of its search variables. */
  private void addToDegrees(int k, double delta) {
    int[] positions = scopePositions[k];
    for (int p = 0; p < positions.length; p += 2) {
      degrees[positions[p]] += delta;
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

  private static int[] identity(int n) {
    int[] a = new int[n];
    for (int i = 0; i < n; i++) {
      a[i] = i;
    }
    return a;
  }

  /**
   * Brings the unfixed counts of the constraints up to date: the scope variables put back in the
   * set by backtracking count again, then the variables now fixed leave the set.
   */
  private void updateUnfixed() {
    int size = scopeVars.length - removed.get(1);
    for (int p = countedScopeSize; p < size; p++) {
      for (int k : occurrences[scopeOrder[p]]) {
        if (++unfixed[k] == 2 && degrees != null) {
          addToDegrees(k, weights[k]);
        }
      }
    }
    int p = 0;
    while (p < size) {
      int x = scopeOrder[p];
      if (scopeVars[x].singleton()) {
        size--;
        scopeOrder[p] = scopeOrder[size];
        scopeOrder[size] = x;
        for (int k : occurrences[x]) {
          if (--unfixed[k] == 1 && degrees != null) {
            addToDegrees(k, -weights[k]);
          }
        }
      } else {
        p++;
      }
    }
    countedScopeSize = size;
    removed.set(1, scopeVars.length - size);
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
      if (unfixed[k] >= 2) {
        w += varWeights == null ? weights[k] + offset : varWeights[i][j];
      }
    }
    return w;
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    selected = null;
    if (vars.length == 0) {
      return null;
    }
    if (removed == null) {
      removed = new TrailedInts(vars[0].getStore(), 2);
    }
    updateUnfixed();
    double best = Double.MAX_VALUE;
    int bestIndex = -1;
    int size = vars.length - removed.get(0);
    int p = 0;
    while (p < size) {
      int i = searchOrder[p];
      IntVar v = vars[i];
      if (v.singleton()) {
        size--;
        searchOrder[p] = searchOrder[size];
        searchOrder[size] = i;
        continue;
      }
      p++;
      double w = degrees != null ? degrees[i] : weightedDegree(i);
      // a variable without constraints left comes last, smaller domains first
      double score = w > 0.0d ? v.getSize() / w : Double.MAX_VALUE / 2 + v.getSize();
      // the set is not in the order of the variables, so ties go to the smaller position
      if (selected == null || score < best || (score == best && i < bestIndex)) {
        best = score;
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
        case WDEG -> {
          weights[k] += 1.0d;
          if (unfixed[k] >= 2) {
            addToDegrees(k, 1.0d);
          }
        }
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

  /**
   * Forgets the weights every given number of restarts, as Choco does (every 32 restarts by default
   * there), so the heuristic follows the part of the search the recent runs are in.
   *
   * @param restarts the number of restarts between two flushes; 0 (the default) never flushes.
   * @return this heuristic.
   */
  public DomWdeg flushEvery(int restarts) {
    this.flushEvery = restarts;
    return this;
  }

  @Override
  public void onRestart(FreeSearch search) {
    restarts++;
    if (flushEvery > 0 && restarts % flushEvery == 0) {
      Arrays.fill(weights, weighting == Weighting.CHS ? 0.0d : 1.0d);
      if (varWeights != null) {
        for (double[] w : varWeights) {
          Arrays.fill(w, 1.0d);
        }
      }
      computeDegrees();
      return;
    }
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
