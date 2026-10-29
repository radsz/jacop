/*
 * ReliabilityPseudoCost.java
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
import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.Indomain;
import org.jacop.search.SelectChoicePoint;

/**
 * Reliability pseudo-cost branching for optimisation (Achterberg, Koch and Martin 2005, SCIP's
 * {@code relpscost}), with the objective bound that propagation gives in place of the LP bound.
 *
 * <p>Each search variable has a pseudo-cost per branch: the mean increase of the lower bound of the
 * cost variable (minimised) after the left branch {@code x = v} and after the right branch {@code x
 * != v} propagated. The search updates them at every decision. A variable is reliable once both of
 * its pseudo-costs average at least a given number of observations; until then, the most promising
 * unreliable variables by dom/wdeg are probed at a node (strong branching): both branches are
 * propagated one level up and the bound increases are recorded, and a branch that fails makes its
 * variable the choice. The variable selected has the largest score, the product of its two gains
 * (unreliable variables not probed take the mean gains of all variables), plus a small multiple of
 * its dom/wdeg score as a tie-breaker; both parts are divided by their mean over the candidates.
 *
 * <p>The values come from the given value heuristic. It is a {@link SearchMonitor}: add it, and the
 * {@link DomWdeg} it is built on, to the {@link FreeSearch} it branches for.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ReliabilityPseudoCost implements SelectChoicePoint<IntVar>, SearchMonitor {

  /** The default number of observations of each branch after which pseudo-costs are trusted. */
  public static final int DEFAULT_RELIABILITY = 4;

  /** The default number of unreliable variables probed at a node. */
  public static final int DEFAULT_CANDIDATES = 8;

  /** The default weight of the dom/wdeg score next to the pseudo-cost score. */
  public static final double DEFAULT_WDEG_WEIGHT = 0.01d;

  // a gain counts at least this much in the product, so that one zero gain does not hide the other
  private static final double EPSILON = 1e-6d;

  private final Store store;
  private final IntVar[] vars;
  private final IntVar cost;
  private final DomWdeg domWdeg;
  private final Indomain<IntVar> indomain;
  private final Map<IntVar, Integer> index = new IdentityHashMap<>();

  private final int reliability;
  private final int candidates;
  private final double wdegWeight;

  // pseudo-costs: sum of gains and number of observations, per variable, [0] left and [1] right
  private final double[][] gainSum = new double[2][];
  private final int[][] count = new int[2][];
  private final double[] totalGain = new double[2];
  private final long[] totalCount = new long[2];

  // the decision whose bound change is not recorded yet: variable, branch and bound before it
  private int pending = -1;
  private int pendingBranch;
  private int pendingBound;

  private IntVar selected;
  private long probes;
  private long gaining;

  // scratch arrays of the selection
  private final int[] unfixed;
  private final double[] gains;
  private final double[] wdeg;
  private final Integer[] order;

  /**
   * Creates the heuristic with the default settings.
   *
   * @param store the store.
   * @param domWdeg the dom/wdeg selection over the variables to branch on; it orders the variables
   *     to probe and breaks ties.
   * @param indomain the value heuristic.
   * @param cost the cost variable, minimised.
   */
  public ReliabilityPseudoCost(
      Store store, DomWdeg domWdeg, Indomain<IntVar> indomain, IntVar cost) {
    this(
        store,
        domWdeg,
        indomain,
        cost,
        DEFAULT_RELIABILITY,
        DEFAULT_CANDIDATES,
        DEFAULT_WDEG_WEIGHT);
  }

  /**
   * Creates the heuristic.
   *
   * @param store the store.
   * @param domWdeg the dom/wdeg selection over the variables to branch on; it orders the variables
   *     to probe and breaks ties.
   * @param indomain the value heuristic.
   * @param cost the cost variable, minimised.
   * @param reliability the number of observations of each branch after which a variable is not
   *     probed any more; 0 never probes.
   * @param candidates the most unreliable variables probed at a node.
   * @param wdegWeight the weight of the dom/wdeg score next to the pseudo-cost score.
   */
  public ReliabilityPseudoCost(
      Store store,
      DomWdeg domWdeg,
      Indomain<IntVar> indomain,
      IntVar cost,
      int reliability,
      int candidates,
      double wdegWeight) {
    this.store = store;
    this.domWdeg = domWdeg;
    this.vars = domWdeg.variables();
    this.indomain = indomain;
    this.cost = cost;
    this.reliability = reliability;
    this.candidates = candidates;
    this.wdegWeight = wdegWeight;
    for (int i = 0; i < vars.length; i++) {
      index.putIfAbsent(vars[i], i);
    }
    for (int b = 0; b < 2; b++) {
      gainSum[b] = new double[vars.length];
      count[b] = new int[vars.length];
    }
    unfixed = new int[vars.length];
    gains = new double[vars.length];
    wdeg = new double[vars.length];
    order = new Integer[vars.length];
  }

  private void observe(int i, int branch, double gain) {
    gainSum[branch][i] += gain;
    count[branch][i]++;
    totalGain[branch] += gain;
    totalCount[branch]++;
    if (gain > 0) {
      gaining++;
    }
  }

  /** Records the bound change of the pending decision, with the store at its fixpoint. */
  private void resolvePending() {
    if (pending >= 0) {
      observe(pending, pendingBranch, Math.max(0, cost.min() - pendingBound));
      pending = -1;
    }
  }

  private double meanGain(int branch) {
    return totalCount[branch] == 0 ? 0.0d : totalGain[branch] / totalCount[branch];
  }

  private double gain(int i, int branch) {
    return count[branch][i] == 0 ? meanGain(branch) : gainSum[branch][i] / count[branch][i];
  }

  private boolean reliable(int i) {
    return Math.min(count[0][i], count[1][i]) >= reliability;
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    resolvePending();
    selected = domWdeg.getChoiceVariable(index);
    if (selected == null) {
      return null;
    }
    int n = 0;
    for (int i = 0; i < vars.length; i++) {
      if (!vars[i].singleton() && this.index.get(vars[i]) == i) {
        unfixed[n++] = i;
        wdeg[i] = domWdeg.score(i);
      }
    }
    if (n == 1) {
      return selected;
    }
    IntVar forced = strongBranching(n);
    if (forced != null) {
      selected = forced;
      return selected;
    }
    double gainTotal = 0.0d;
    double wdegTotal = 0.0d;
    for (int k = 0; k < n; k++) {
      int i = unfixed[k];
      gains[i] = Math.max(gain(i, 0), EPSILON) * Math.max(gain(i, 1), EPSILON);
      gainTotal += gains[i];
      // dom/wdeg prefers small scores
      wdegTotal += 1.0d / wdeg[i];
    }
    double gainMean = gainTotal / n;
    double wdegMean = wdegTotal / n;
    double best = Double.NEGATIVE_INFINITY;
    for (int k = 0; k < n; k++) {
      int i = unfixed[k];
      double score = gains[i] / gainMean + wdegWeight * (1.0d / wdeg[i]) / wdegMean;
      if (score > best) {
        best = score;
        selected = vars[i];
      }
    }
    return selected;
  }

  /**
   * Probes both branches of the most promising unreliable variables. Returns a variable one of
   * whose branches fails, or null.
   */
  private IntVar strongBranching(int n) {
    if (reliability == 0 || candidates == 0) {
      return null;
    }
    int m = 0;
    for (int k = 0; k < n; k++) {
      if (!reliable(unfixed[k])) {
        order[m++] = unfixed[k];
      }
    }
    if (m == 0) {
      return null;
    }
    Arrays.sort(order, 0, m, (a, b) -> Double.compare(wdeg[a], wdeg[b]));
    int level = store.level;
    int bound = cost.min();
    try {
      for (int k = 0; k < Math.min(m, candidates); k++) {
        int i = order[k];
        IntVar v = vars[i];
        int value = indomain.indomain(v);
        for (int branch = 0; branch < 2; branch++) {
          probes++;
          store.setLevel(level + 1);
          boolean consistent;
          try {
            if (branch == 0) {
              v.domain.inValue(store.level, v, value);
            } else {
              v.domain.inComplement(store.level, v, value);
            }
            consistent = store.consistency();
          } catch (FailException _) {
            consistent = false;
          }
          int after = cost.min();
          store.removeLevel(level + 1);
          store.setLevel(level);
          if (!consistent) {
            return v;
          }
          observe(i, branch, Math.max(0, after - bound));
        }
      }
    } finally {
      // the probes are not failures of the search
      store.recentlyFailedConstraint = null;
    }
    return null;
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
    return domWdeg.getVariablesMapping();
  }

  @Override
  public int getIndex() {
    return 0;
  }

  @Override
  public void onDecision(Var var, int value, boolean left) {
    // the decision is not propagated yet, so the bound is still that of the node it starts from
    resolvePending();
    Integer i = index.get(var);
    if (i != null && var != cost) {
      pending = i;
      pendingBranch = left ? 0 : 1;
      pendingBound = cost.min();
    }
  }

  @Override
  public void onFailure(Constraint failed, Var decision) {
    // a failed branch gives no bound
    pending = -1;
  }

  @Override
  public void onRestart(FreeSearch search) {
    pending = -1;
  }

  @Override
  public void onSolution(FreeSearch search) {
    resolvePending();
  }

  /**
   * Returns the number of branches propagated by strong branching so far.
   *
   * @return the number of probes.
   */
  public long getProbes() {
    return probes;
  }

  /**
   * Returns the number of bound changes recorded so far, by the search and by strong branching.
   *
   * @return the number of observations.
   */
  public long getObservations() {
    return totalCount[0] + totalCount[1];
  }

  /**
   * Returns the number of observations that raised the bound.
   *
   * @return the number of observations with a positive gain.
   */
  public long getGainingObservations() {
    return gaining;
  }

  @Override
  public String toString() {
    return "ReliabilityPseudoCost("
        + vars.length
        + " variables, reliability "
        + reliability
        + ", "
        + candidates
        + " candidates, "
        + indomain
        + ")";
  }
}
