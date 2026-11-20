/*
 * FloatDive.java
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

package org.jacop.floats.search;

import java.util.Random;
import org.jacop.core.FailException;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Sampling dives, a primal heuristic for float optimisation. A dive narrows the float search
 * variables one after the other, in their order, to a box as wide as the precision around a sampled
 * value, and propagates after each one; the variables that the earlier ones define (x8 = x2 / (x2 +
 * x4 + x6)) are narrow by then and take a value inside their domain. Under a bound on the cost a
 * dive that narrows every variable ends at a box holding a better solution, which a depth-first
 * search on a wide box may not reach: on ex6_1_3 (Ibex optim/hard) branch and bound crawls by ulps
 * along a flat valley of one-phase points at -0.32435, and interval bounds cannot refute the boxes
 * away from the optimum -0.3525 in its corners (1.4 million nodes with x2 fixed).
 *
 * <p>A dive samples each value either uniformly in the current domain or, around the point of the
 * last dive that improved the cost, from a normal distribution whose deviation is a fraction sigma
 * of the variable's initial width: a (1+1) evolution strategy, with sigma growing after a success
 * and shrinking after a failure, as the 1/5 success rule of Rechenberg (I. Rechenberg,
 * Evolutionsstrategie: Optimierung technischer Systeme nach Prinzipien der biologischen Evolution,
 * Frommann-Holzboog, 1973). Sampling points of the box for an upper bound of the cost is the upper
 * bounding of interval branch and bound solvers such as Ibex (I. Araya, G. Trombettoni, B. Neveu,
 * G. Chabert, Upper bounding in inner regions for global optimization under inequality constraints,
 * Journal of Global Optimization 60(2), 2014); diving with propagation after each fixing is the
 * diving heuristic of MIP solvers (T. Berthold, Primal heuristics for mixed integer programs,
 * Diploma thesis, TU Berlin, 2006).
 *
 * <p>A dive opens store levels above the current one; the caller removes them.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class FloatDive {

  // the tries of a variable before a dive gives up
  private static final int TRIES = 3;

  // a domain wider than this is sampled in [-LARGE, LARGE]
  private static final double LARGE = 1e3;

  private static final double INITIAL_SIGMA = 0.1;

  private final Store store;

  private final Var[] vars;

  private final FloatVar cost;

  private final Random random;

  // the width of each variable at the first dive
  private double[] width;

  // the point of the last dive that improved the cost, or null
  private double[] center;

  private double sigma = INITIAL_SIGMA;

  // the last dive sampled around center
  private boolean local;

  private double[] point;

  private long dives;

  private long steps;

  private long improvements;

  /**
   * Dives over the float variables among vars.
   *
   * @param store the store
   * @param vars the search variables, in their order; variables that are not float variables are
   *     left to the search
   * @param cost the cost, never sampled
   * @param seed the seed of the samples
   */
  public FloatDive(Store store, Var[] vars, FloatVar cost, long seed) {
    this.store = store;
    this.vars = vars.clone();
    this.cost = cost;
    this.random = new Random(seed);
  }

  /**
   * Narrows each float variable, in order, to a box of the precision around a sampled value, with
   * propagation after each one, at levels above the current level.
   *
   * @return true if every float variable is narrowed to the precision and the store is consistent
   */
  public boolean dive() {
    dives++;
    if (width == null) {
      width = new double[vars.length];
      for (int i = 0; i < vars.length; i++) {
        if (vars[i] instanceof FloatVar v) {
          width[i] = Math.min(v.max(), LARGE) - Math.max(v.min(), -LARGE);
        }
      }
    }
    local = center != null && random.nextBoolean();
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] instanceof FloatVar v && v != cost && !v.singleton() && !narrow(v, i)) {
        return false;
      }
    }
    point = new double[vars.length];
    for (int i = 0; i < vars.length; i++) {
      point[i] = vars[i] instanceof FloatVar v ? (v.min() + v.max()) / 2 : Double.NaN;
    }
    return true;
  }

  // narrows v to a box of the precision around a sample, at a new level, in up to TRIES tries
  private boolean narrow(FloatVar v, int i) {
    double h = FloatDomain.precision() / 2;
    for (int t = 0; t < TRIES; t++) {
      steps++;
      int level = store.level + 1;
      store.setLevel(level);
      boolean ok = false;
      try {
        double c = sample(v, i);
        v.domain.in(level, v, Math.max(v.min(), c - h), Math.min(v.max(), c + h));
        ok = store.consistency();
      } catch (FailException _) {
        store.clearChanged();
      }
      if (ok) {
        return true;
      }
      store.removeLevel(level);
      store.setLevel(level - 1);
    }
    return false;
  }

  private double sample(FloatVar v, int i) {
    if (local && !Double.isNaN(center[i])) {
      return Math.clamp(center[i] + sigma * width[i] * random.nextGaussian(), v.min(), v.max());
    }
    double lo = Math.max(v.min(), -LARGE);
    double hi = Math.min(v.max(), LARGE);
    if (lo > hi) {
      lo = v.min();
      hi = v.max();
    }
    return lo + random.nextDouble() * (hi - lo);
  }

  /** The last dive found a better solution: the next local dives sample around its point. */
  public void improved() {
    improvements++;
    center = point;
    if (local) {
      sigma = Math.min(0.5, sigma * 1.5);
    }
  }

  /** The last dive found no better solution. */
  public void failed() {
    if (local) {
      sigma *= 0.95;
      if (sigma < 1e-9) {
        sigma = INITIAL_SIGMA;
      }
    }
  }

  /**
   * @return the dives so far
   */
  public long dives() {
    return dives;
  }

  /**
   * @return the variables narrowed so far, counting each try
   */
  public long steps() {
    return steps;
  }

  /**
   * @return the dives that found a better solution
   */
  public long improvements() {
    return improvements;
  }
}
