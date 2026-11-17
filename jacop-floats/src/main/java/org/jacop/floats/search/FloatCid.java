/*
 * FloatCid.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.search;

import org.jacop.core.FailException;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.ConsistencyListener;

/**
 * 3BCID, shaving and constructive interval disjunction on float variables, run at every search node
 * after propagation.
 *
 * <p>For each variable the contractor first shaves its bounds (3B): a slice of width w/s3b at each
 * end is propagated on its own, and removed when it fails, until a slice survives. It then splits
 * the remaining interval in two halves (CID), propagates each one, and narrows every variable to
 * the hull of what is left of it in the two halves. Both steps only remove values without a
 * solution of the propagated subproblem, so they are sound, and they reach consistency that
 * propagation of each constraint alone cannot (several occurrences of a variable, cycles of
 * constraints).
 *
 * <ul>
 *   <li>O. Lhomme, "Consistency techniques for numeric CSPs", IJCAI 1993, pp. 232-238 (3B).
 *   <li>G. Trombettoni and G. Chabert, "Constructive Interval Disjunction", CP 2007, LNCS 4741, pp.
 *       635-650 (CID and 3BCID).
 *   <li>B. Neveu, G. Trombettoni and I. Araya, "Adaptive constructive interval disjunction:
 *       algorithms and experiments", Constraints 20(4), 2015, pp. 452-467 (ACID: how many variables
 *       to handle at a node).
 * </ul>
 *
 * <p>The number of variables handled at a node is a parameter (round robin over the variables);
 * ACID learns it, this class uses a fixed number.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class FloatCid implements ConsistencyListener {

  private final Store store;

  private final FloatVar[] vars;

  /** Number of slices of the 3B shaving, 0 for no shaving. */
  private final int s3b;

  /** Number of variables handled at each node. */
  private final int perNode;

  private int next;

  private ConsistencyListener[] children;

  /** Number of probes made. */
  public long probes;

  /** Number of variables narrowed by the contractor. */
  public long narrowed;

  /**
   * It creates a 3BCID contractor.
   *
   * @param store the store
   * @param vars the variables to shave and split
   * @param s3b the number of slices of the shaving step, 0 for CID only
   * @param perNode the number of variables handled at each node, at most vars.length
   */
  public FloatCid(Store store, FloatVar[] vars, int s3b, int perNode) {
    this.store = store;
    this.vars = vars.clone();
    this.s3b = s3b;
    this.perNode = Math.max(1, Math.min(perNode, vars.length));
  }

  @Override
  public boolean executeAfterConsistency(boolean consistent) {
    boolean result = consistent && contract();
    if (children != null) {
      for (ConsistencyListener child : children) {
        result = child.executeAfterConsistency(result);
      }
    }
    return result;
  }

  private boolean contract() {
    if (vars.length == 0) {
      return true;
    }
    for (int k = 0; k < perNode; k++) {
      FloatVar x = vars[next];
      next = (next + 1) % vars.length;
      if (x.singleton() || !Double.isFinite(x.max() - x.min())) {
        continue;
      }
      if (s3b > 0 && !shave(x)) {
        return false;
      }
      if (!x.singleton() && !cid(x)) {
        return false;
      }
    }
    return true;
  }

  /** Propagates x in [a, b] at a new level; returns whether it is consistent. */
  private boolean probe(FloatVar x, double a, double b, double[] lo, double[] hi) {
    int level = store.level;
    store.setLevel(level + 1);
    boolean ok;
    probes++;
    try {
      x.domain.in(store.level, x, a, b);
      ok = store.consistency();
    } catch (FailException e) {
      ok = false;
    }
    if (ok && lo != null) {
      for (int i = 0; i < vars.length; i++) {
        lo[i] = vars[i].min();
        hi[i] = vars[i].max();
      }
    }
    store.removeLevel(level + 1);
    store.setLevel(level);
    return ok;
  }

  /** Applies a narrowing at the current level and propagates it. */
  private boolean narrow(FloatVar v, double a, double b) {
    if (a <= v.min() && b >= v.max()) {
      return true;
    }
    try {
      v.domain.in(store.level, v, a, b);
    } catch (FailException e) {
      return false;
    }
    narrowed++;
    return true;
  }

  private boolean shave(FloatVar x) {
    double lo = x.min();
    double hi = x.max();
    double slice = (hi - lo) / s3b;
    if (slice <= FloatDomain.precision()) {
      return true;
    }
    double newLo = lo;
    int i = 0;
    while (i < s3b - 1 && !probe(x, newLo, newLo + slice, null, null)) {
      newLo += slice;
      i++;
    }
    if (i == s3b - 1) {
      // every slice but the last failed: the last one is what is left
      return narrow(x, newLo, hi) && store.consistency();
    }
    double newHi = hi;
    int j = 0;
    while (j < s3b - 1 - i && !probe(x, newHi - slice, newHi, null, null)) {
      newHi -= slice;
      j++;
    }
    if (newLo == lo && newHi == hi) {
      return true;
    }
    return narrow(x, newLo, newHi) && store.consistency();
  }

  private boolean cid(FloatVar x) {
    double lo = x.min();
    double hi = x.max();
    double mid = lo + (hi - lo) / 2;
    if (!(mid > lo && mid < hi)) {
      return true;
    }
    int n = vars.length;
    double[] lo1 = new double[n];
    double[] hi1 = new double[n];
    double[] lo2 = new double[n];
    double[] hi2 = new double[n];
    boolean left = probe(x, lo, mid, lo1, hi1);
    boolean right = probe(x, mid, hi, lo2, hi2);
    if (!left && !right) {
      return false;
    }
    if (!left) {
      return narrow(x, mid, hi) && store.consistency();
    }
    if (!right) {
      return narrow(x, lo, mid) && store.consistency();
    }
    boolean changed = false;
    for (int i = 0; i < n; i++) {
      double a = Math.min(lo1[i], lo2[i]);
      double b = Math.max(hi1[i], hi2[i]);
      if (a > vars[i].min() || b < vars[i].max()) {
        if (!narrow(vars[i], a, b)) {
          return false;
        }
        changed = true;
      }
    }
    return !changed || store.consistency();
  }

  /**
   * It sets the listeners called after this one.
   *
   * @param children the listeners
   */
  @Override
  public void setChildrenListeners(ConsistencyListener[] children) {
    this.children = children;
  }

  @Override
  public void setChildrenListeners(ConsistencyListener child) {
    this.children = new ConsistencyListener[] {child};
  }
}
