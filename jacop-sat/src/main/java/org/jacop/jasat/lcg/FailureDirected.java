/*
 * FailureDirected.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with Section 7 of the GNU Affero General Public License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import org.jacop.core.IntVar;

/**
 * The ratings and choices of failure-directed search (P. Vilím, P. Laborie and P. Shaw,
 * <i>Failure-Directed Search for Constraint-Based Scheduling</i>, CPAIOR 2015, LNCS 9075, pp.
 * 437-453), the proof search of IBM ILOG CP Optimizer for scheduling, over the start variables of
 * the tasks of a model's resources.
 *
 * <p>Each decision is a binary split of a start's domain, {@code [s >= v]} or {@code [s < v]}. To
 * keep the ratings of a choice stable across the search, the split points are fixed in advance: a
 * grid of at most {@link #GRID} points over the start's root domain, the point nearest the middle
 * of the current domain taken; once the domain lies between two neighbouring points, the middle of
 * the current domain with one shared rating per polarity. Each choice keeps a rating, a moving
 * average of local ratings: 0 when the propagation of the choice fails, otherwise 1 plus the share
 * of the search space (the product of the starts' domain sizes) that is left after it, so the lower
 * a rating the more the choice prunes. As in the paper, a local rating is divided by the average
 * local rating at the same depth before it enters the average, so that choices taken deep in the
 * tree, where every choice prunes little, compare fairly with those near the root.
 *
 * <p>The search takes the start whose two choices have the least sum of ratings, the most likely to
 * fail together, and tries first the choice with the lower rating, the one more likely to fail.
 * Ties go to the smaller domain. Under lazy clause generation the restarts and the learnt clauses
 * of the SAT solver take the place of the paper's restarts with a geometric node limit and its
 * restart nogoods.
 *
 * <p>The rating formula follows the description of the paper as recalled, not a copy of its text
 * (the full text was not available when this was written): the constants {@link #ALPHA} and {@link
 * #GRID} are this implementation's own.
 */
final class FailureDirected {

  /** The weight of a new local rating in a choice's moving average. */
  static final double ALPHA = Double.parseDouble(System.getProperty("jacop.lcg.fdsAlpha", "0.1"));

  /** The most split points of a start's root domain. */
  static final int GRID = Integer.getInteger("jacop.lcg.fdsGrid", 32);

  // the starts by their variable id in LcgSolver
  private final int[] ids;
  // per start: the lower bound of its root domain and the distance between split points
  private final int[] lo;
  private final int[] step;
  private final int[] points;
  // per start: the ratings of its choices, 2 per split point (upper, lower), then 2 for the middle
  private final double[][] rating;
  // the average local rating per depth
  private double[] depthAverage = new double[64];

  // the pending choice: start, rating slot, its polarity, decision level, and log2 search space
  // before it; pendingStart < 0 when none
  private int pendingStart = -1;
  private int pendingSlot;
  private int pendingLevel;
  private double pendingLog;
  private int pendingLit;

  /** Statistics: decisions taken. */
  long decisions;

  /** Statistics: choices whose propagation failed. */
  long failures;

  /**
   * Prepares the ratings of the given starts.
   *
   * @param ids the starts' ids in the solver
   * @param root the root domains' bounds as {min, max} per start
   */
  FailureDirected(int[] ids, int[][] root) {
    this.ids = ids.clone();
    int n = ids.length;
    lo = new int[n];
    step = new int[n];
    points = new int[n];
    rating = new double[n][];
    for (int k = 0; k < n; k++) {
      long width = (long) root[k][1] - root[k][0];
      lo[k] = root[k][0];
      long s = Math.max(1, (width + GRID) / (GRID + 1));
      step[k] = (int) Math.min(Integer.MAX_VALUE, s);
      points[k] = (int) Math.min(GRID, width / s);
      rating[k] = new double[2 * points[k] + 2];
      java.util.Arrays.fill(rating[k], 1.0);
    }
    java.util.Arrays.fill(depthAverage, 1.0);
  }

  /** The number of starts. */
  int size() {
    return ids.length;
  }

  // log2 of the size of a domain of n values, near enough for ratios of search spaces
  private static double log2(int n) {
    return n <= 1 ? 0 : Math.log(n) * 1.4426950408889634;
  }

  private double logSpace(IntVar[] vars) {
    double s = 0;
    for (int id : ids) {
      s += log2(vars[id].getSize());
    }
    return s;
  }

  /**
   * Rates the pending choice from the state at the next decision: it failed when the search is
   * below its level or its literal does not hold, otherwise its local rating is 1 plus the share of
   * the search space left.
   *
   * @param vars the solver's variables
   * @param level the decision level now
   * @param holds whether the pending choice's literal holds now
   */
  void settle(IntVar[] vars, int level, boolean holds) {
    if (pendingStart < 0) {
      return;
    }
    double local;
    if (level < pendingLevel || !holds) {
      local = 0;
      failures++;
    } else {
      double left = logSpace(vars) - pendingLog;
      local = 1 + Math.pow(2, Math.min(0, left));
    }
    int d = Math.min(pendingLevel, 1 << 20);
    if (d >= depthAverage.length) {
      int old = depthAverage.length;
      depthAverage = java.util.Arrays.copyOf(depthAverage, Math.max(d + 1, 2 * old));
      java.util.Arrays.fill(depthAverage, old, depthAverage.length, 1.0);
    }
    double avg = depthAverage[d];
    double normal = avg > 1e-9 ? local / avg : local;
    depthAverage[d] = (1 - ALPHA) * avg + ALPHA * local;
    double[] r = rating[pendingStart];
    r[pendingSlot] = (1 - ALPHA) * r[pendingSlot] + ALPHA * normal;
    pendingStart = -1;
  }

  /** Forgets the pending choice, for a decision taken elsewhere. */
  void clearPending() {
    pendingStart = -1;
  }

  /** The literal of the pending choice, or 0. */
  int pendingLiteral() {
    return pendingStart < 0 ? 0 : pendingLit;
  }

  /** Callback that turns a choice into the solver's literal [x >= v]. */
  interface Literals {
    int geLit(int id, int v);
  }

  /**
   * Chooses the next decision: the unfixed start whose choices have the least sum of ratings, its
   * choice with the lower rating first.
   *
   * @param vars the solver's variables
   * @param level the decision level the choice will be taken at
   * @param literals makes the literal of a choice
   * @return the decision literal, or 0 when every start is fixed.
   */
  int choose(IntVar[] vars, int level, Literals literals) {
    int bestK = -1;
    int bestV = 0;
    int bestSlot = 0;
    double bestSum = Double.MAX_VALUE;
    int bestSize = Integer.MAX_VALUE;
    double space = 0;
    for (int k = 0; k < ids.length; k++) {
      IntVar x = vars[ids[k]];
      int size = x.getSize();
      if (size <= 1) {
        continue;
      }
      space += log2(size);
      int min = x.min();
      int max = x.max();
      int mid = min + (int) (((long) max - min + 1) / 2); // [x >= mid] splits [min, max] in two
      int slot;
      int v;
      long j = (mid - (long) lo[k] + step[k] / 2) / step[k]; // the nearest grid point
      j = Math.max(1, Math.min(points[k], j));
      long p = lo[k] + j * step[k];
      if (points[k] > 0 && p > min && p <= max) {
        slot = 2 * (int) (j - 1);
        v = (int) p;
      } else {
        slot = 2 * points[k];
        v = mid;
      }
      double[] r = rating[k];
      double sum = r[slot] + r[slot + 1];
      if (sum < bestSum || (sum == bestSum && size < bestSize)) {
        bestSum = sum;
        bestSize = size;
        bestK = k;
        bestV = v;
        bestSlot = slot;
      }
    }
    if (bestK < 0) {
      return 0;
    }
    double[] r = rating[bestK];
    // the upper half when its rating is strictly lower, else the lower half
    boolean upper = r[bestSlot] < r[bestSlot + 1];
    int ge = literals.geLit(ids[bestK], bestV);
    pendingStart = bestK;
    pendingSlot = upper ? bestSlot : bestSlot + 1;
    pendingLevel = level;
    pendingLog = space;
    pendingLit = upper ? ge : -ge;
    decisions++;
    return pendingLit;
  }
}
