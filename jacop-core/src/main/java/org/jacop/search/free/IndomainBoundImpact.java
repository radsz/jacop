/*
 * IndomainBoundImpact.java
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

import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.search.Indomain;

/**
 * Bound-impact value selection for optimisation (Fages and Prud'homme 2017): each value of the
 * variable is tried in turn, propagated, and the value that leaves the best bound on the objective
 * is chosen, the smallest one on ties. Values whose propagation fails are not chosen. Variables
 * with a domain larger than a limit, and the objective itself, use the wrapped heuristic, as do
 * variables none of whose values propagates.
 *
 * <p>Each probe raises the store level and removes it again, so the store is left as it was. It is
 * meant to find a good first solution; wrapped in {@link IndomainLastSolution} it is used only for
 * variables without a value from the last solution, and {@link #untilFirstSolution()} stops it
 * after the first solution.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class IndomainBoundImpact implements Indomain<IntVar>, SearchMonitor {

  /** The default largest domain whose values are all tried. */
  public static final int DEFAULT_MAX_DOMAIN = 64;

  private final Store store;
  private final IntVar objective;
  private final boolean maximize;
  private final int maxDomain;
  private final Indomain<IntVar> fallback;
  private long probes;
  private boolean untilFirstSolution;
  private boolean solved;

  /**
   * Creates the heuristic.
   *
   * @param store the store.
   * @param objective the objective variable.
   * @param maximize true if the objective is maximised, false if it is minimised.
   * @param maxDomain the largest domain whose values are all tried.
   * @param fallback the value heuristic for the other variables.
   */
  public IndomainBoundImpact(
      Store store, IntVar objective, boolean maximize, int maxDomain, Indomain<IntVar> fallback) {
    this.store = store;
    this.objective = objective;
    this.maximize = maximize;
    this.maxDomain = maxDomain;
    this.fallback = fallback;
  }

  @Override
  public int indomain(IntVar v) {
    if ((untilFirstSolution && solved)
        || v == objective
        || v.getSize() > maxDomain
        || v.singleton()) {
      return fallback.indomain(v);
    }
    int level = store.level;
    boolean found = false;
    int bestValue = 0;
    int bestBound = 0;
    for (ValueEnumeration e = v.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int value = e.nextElement();
      probes++;
      store.setLevel(level + 1);
      boolean consistent;
      try {
        v.domain.in(store.level, v, value, value);
        consistent = store.consistency();
      } catch (FailException _) {
        consistent = false;
      }
      int bound = maximize ? objective.max() : objective.min();
      store.removeLevel(level + 1);
      store.setLevel(level);
      if (consistent && (!found || (maximize ? bound > bestBound : bound < bestBound))) {
        found = true;
        bestValue = value;
        bestBound = bound;
      }
    }
    // the probes are not failures of the search
    store.recentlyFailedConstraint = null;
    return found ? bestValue : fallback.indomain(v);
  }

  /**
   * Uses the wrapped heuristic once a solution is found; the probes then only slow down the search
   * for a better one. Add the heuristic as a monitor of the search to see the solutions.
   *
   * @return this heuristic.
   */
  public IndomainBoundImpact untilFirstSolution() {
    this.untilFirstSolution = true;
    return this;
  }

  @Override
  public void onSolution(FreeSearch search) {
    solved = true;
  }

  /**
   * Returns the number of values propagated so far.
   *
   * @return the number of probes.
   */
  public long getProbes() {
    return probes;
  }

  @Override
  public String toString() {
    return "IndomainBoundImpact(" + maxDomain + ", " + fallback + ")";
  }
}
