/*
 * LexChainExplanation.java
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

package org.jacop.lcg;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;

/**
 * Explanations of a chain of lexicographically ordered vectors x[0] &lt;= x[1] &lt;= ... (or &lt;)
 * ({@link org.jacop.constraints.LexChain}) that need only one side of the chain.
 *
 * <p>The smallest tuple of each vector above the one before it, starting from the smallest tuple of
 * x[0], is a lower bound of that vector in every solution, and it depends only on the domains of
 * the vectors up to it. A value of x[i] that no tuple of x[i] reaches above the bound of x[i - 1]
 * is pruned by the domains of x[0..i] alone; symmetrically with the largest tuples from the last
 * vector down. Such a pruning gets the atoms of those vectors as its reason, instead of the atoms
 * of every vector; a value that needs both sides is left to the generic reason. A failure is
 * explained by the vectors up to (or from) the first one with no tuple above (below) its bound.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LexChainExplanation {

  // domains larger than this are left to the generic reason
  private static final int MAX_VALUES = 10_000;

  private final AtomicTrail trail;
  private final IntVar[][] x;
  private final boolean strict;
  private final int m;
  private final int n;
  private final int position;
  private final IntDomain[][] domain;
  private final EntryList scratch = new EntryList();

  private LexChainExplanation(AtomicTrail trail, IntVar[][] x, boolean strict, int position) {
    this.trail = trail;
    this.x = x;
    this.strict = strict;
    this.m = x.length;
    this.n = m == 0 ? 0 : x[0].length;
    this.position = position;
    this.domain = new IntDomain[m][];
  }

  /**
   * Adds to {@code out} the reason of an atom the constraint propagated.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param x the vectors, with no variable twice
   * @param strict whether the order is strict
   * @param out where the reason entries are added
   * @return false when one side of the chain does not give the atom
   */
  public static boolean explain(
      AtomicTrail trail, int entry, IntVar[][] x, boolean strict, EntryList out) {
    IntVar v = trail.variable(entry);
    for (int i = 0; i < x.length; i++) {
      for (int j = 0; j < x[i].length; j++) {
        if (x[i][j] == v) {
          return new LexChainExplanation(trail, x, strict, entry)
              .explainValues(i, j, trail.removedMin(entry), trail.removedMax(entry), out);
        }
      }
    }
    return false;
  }

  /**
   * Adds to {@code out} the reason of a failure of the constraint now.
   *
   * @param trail the trail
   * @param x the vectors, with no variable twice
   * @param strict whether the order is strict
   * @param out where the reason entries are added
   * @return false when one side of the chain does not fail
   */
  public static boolean explainFailure(
      AtomicTrail trail, IntVar[][] x, boolean strict, EntryList out) {
    LexChainExplanation e = new LexChainExplanation(trail, x, strict, trail.size());
    int m = x.length;
    if (m < 2) {
      return false;
    }
    int[] bound = null;
    for (int i = 0; i < m; i++) {
      if (!e.read(i)) {
        return false;
      }
      bound = e.smallestAbove(i, bound);
      if (bound == null) {
        e.addRows(0, i, -1, -1, out);
        return true;
      }
    }
    bound = null;
    for (int i = m - 1; i >= 0; i--) {
      bound = e.largestBelow(i, bound);
      if (bound == null) {
        e.addRows(i, m - 1, -1, -1, out);
        return true;
      }
    }
    return false;
  }

  /** Explains that no value of x[i][j] in [lo, hi] is left, by one side of the chain. */
  private boolean explainValues(int i, int j, int lo, int hi, EntryList out) {
    IntDomain root = trail.rootDomain(x[i][j]);
    lo = Math.max(lo, root.min());
    hi = Math.min(hi, root.max());
    if (lo > hi) {
      return true;
    }
    if (root.getSize() > MAX_VALUES) {
      return false;
    }
    // the bounds of x[i] from the vectors before and after it
    int[] below = null;
    for (int k = 0; k < i; k++) {
      if (!read(k)) {
        return false;
      }
      below = smallestAbove(k, below);
      if (below == null) {
        return false;
      }
    }
    int[] above = null;
    for (int k = m - 1; k > i; k--) {
      if (!read(k)) {
        return false;
      }
      above = largestBelow(k, above);
      if (above == null) {
        return false;
      }
    }
    if (!read(i)) {
      return false;
    }
    boolean lower = below != null;
    boolean upper = above != null;
    int mark = out.size();
    for (int u = root.contains(lo) ? lo : root.nextValue(lo); u <= hi; u = root.nextValue(u)) {
      if (!trail.excludedBefore(x[i][j], u, position, out)) {
        lower &= !reachesAbove(i, j, u, below);
        upper &= !reachesBelow(i, j, u, above);
        if (!lower && !upper) {
          out.truncate(mark);
          return false;
        }
      }
      if (u >= root.max()) {
        break;
      }
    }
    if (lower) {
      addRows(0, i, i, j, out);
    } else if (upper) {
      addRows(i, m - 1, i, j, out);
    }
    return true;
  }

  /** Whether some tuple of x[i] with u at j is above (or equal to, unless strict) the bound. */
  private boolean reachesAbove(int i, int j, int u, int[] bound) {
    if (bound == null) {
      return true;
    }
    for (int k = 0; k < n; k++) {
      int t = k == j ? u : domain[i][k].max();
      if (t != bound[k]) {
        return t > bound[k];
      }
    }
    return !strict;
  }

  /** Whether some tuple of x[i] with u at j is below (or equal to, unless strict) the bound. */
  private boolean reachesBelow(int i, int j, int u, int[] bound) {
    if (bound == null) {
      return true;
    }
    for (int k = 0; k < n; k++) {
      int t = k == j ? u : domain[i][k].min();
      if (t != bound[k]) {
        return t < bound[k];
      }
    }
    return !strict;
  }

  /**
   * The smallest tuple of x[i] above the bound (or equal to it, unless strict), or the smallest
   * tuple of x[i] when the bound is null; null when there is none.
   */
  private int[] smallestAbove(int i, int[] bound) {
    IntDomain[] d = domain[i];
    int[] t = new int[n];
    if (bound == null) {
      for (int k = 0; k < n; k++) {
        t[k] = d[k].min();
      }
      return t;
    }
    int q = 0;
    while (q < n && d[q].contains(bound[q])) {
      q++;
    }
    if (q == n && !strict) {
      return bound.clone();
    }
    for (int p = Math.min(q, n - 1); p >= 0; p--) {
      if (d[p].max() > bound[p]) {
        System.arraycopy(bound, 0, t, 0, p);
        t[p] = bound[p] < d[p].min() ? d[p].min() : d[p].nextValue(bound[p]);
        for (int k = p + 1; k < n; k++) {
          t[k] = d[k].min();
        }
        return t;
      }
    }
    return null;
  }

  /** The largest tuple of x[i] below the bound, symmetric to {@link #smallestAbove}. */
  private int[] largestBelow(int i, int[] bound) {
    IntDomain[] d = domain[i];
    int[] t = new int[n];
    if (bound == null) {
      for (int k = 0; k < n; k++) {
        t[k] = d[k].max();
      }
      return t;
    }
    int q = 0;
    while (q < n && d[q].contains(bound[q])) {
      q++;
    }
    if (q == n && !strict) {
      return bound.clone();
    }
    for (int p = Math.min(q, n - 1); p >= 0; p--) {
      if (d[p].min() < bound[p]) {
        System.arraycopy(bound, 0, t, 0, p);
        t[p] = bound[p] > d[p].max() ? d[p].max() : d[p].previousValue(bound[p]);
        for (int k = p + 1; k < n; k++) {
          t[k] = d[k].max();
        }
        return t;
      }
    }
    return null;
  }

  /** Reads the domains of x[i] before the position; false when one is too large or empty. */
  private boolean read(int i) {
    if (domain[i] != null) {
      return true;
    }
    IntDomain[] d = new IntDomain[n];
    for (int k = 0; k < n; k++) {
      IntVar v = x[i][k];
      IntDomain root = trail.rootDomain(v);
      if (root.getSize() > MAX_VALUES) {
        return false;
      }
      int lo = trail.minBefore(v, position);
      int hi = trail.maxBefore(v, position);
      IntDomain r = new IntervalDomain();
      for (var e = root.valueEnumeration(); e.hasMoreElements(); ) {
        int u = e.nextElement();
        if (u >= lo && u <= hi) {
          int mark = scratch.size();
          if (!trail.excludedBefore(v, u, position, scratch)) {
            r.unionAdapt(u, u);
          }
          scratch.truncate(mark);
        }
      }
      if (r.isEmpty()) {
        return false;
      }
      d[k] = r;
    }
    domain[i] = d;
    return true;
  }

  /** Adds the atoms of the vectors from..to, except the variable x[skipRow][skipColumn]. */
  private void addRows(int from, int to, int skipRow, int skipColumn, EntryList out) {
    for (int i = from; i <= to; i++) {
      for (int k = 0; k < n; k++) {
        if (i != skipRow || k != skipColumn) {
          trail.atomsBefore(x[i][k], position, out);
        }
      }
    }
  }
}
