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

/**
 * Explanations of a chain of lexicographically ordered vectors x[0] &lt;= x[1] &lt;= ... (or &lt;)
 * ({@link org.jacop.constraints.LexChain}) that need only one side of the chain.
 *
 * <p>The smallest tuple of each vector above the one before it, starting from the smallest tuple of
 * x[0], is a lower bound of that vector in every solution, and it depends only on the domains of
 * the vectors up to it. A value of x[i] that no tuple of x[i] reaches above the bound of x[i - 1]
 * is pruned by the domains of x[0..i] alone; symmetrically with the largest tuples from the last
 * vector down. Such a pruning gets the atoms of those vectors as its reason, instead of the atoms
 * of every vector. A value that needs both sides, no tuple of x[i] with it lying between the bound
 * of the vectors below x[i] and that of the vectors above it, gets the atoms of the nearest vectors
 * on both sides that rule it out. A failure is explained by the vectors up to (or from) the first
 * one with no tuple above (below) its bound, or by those around a vector whose smallest tuple is
 * above its largest one.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LexChainExplanation {

  // more removed values than this are left to the generic reason
  private static final int MAX_VALUES = 10_000;

  private final AtomicTrail trail;
  private final IntVar[][] x;
  private final boolean strict;
  private final int m;
  private final int n;
  private final int position;
  private final IntDomain[][] domain;
  // whether a vector read has no atom before the position, so its domains are the root ones
  private final boolean[] untouched;

  // positions beyond it are read as their root domains, a weaker view whose reason is shorter
  private int limit;

  private LexChainExplanation(AtomicTrail trail, IntVar[][] x, boolean strict, int position) {
    this.trail = trail;
    this.x = x;
    this.strict = strict;
    this.m = x.length;
    this.n = m == 0 ? 0 : x[0].length;
    this.position = position;
    this.domain = new IntDomain[m][];
    this.untouched = new boolean[m];
    this.limit = n - 1;
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
          return explain(trail, entry, x, strict, i, j, out);
        }
      }
    }
    return false;
  }

  /**
   * Adds to {@code out} the reason of an atom the constraint propagated on x[i][j].
   *
   * @param trail the trail
   * @param entry the entry of the atom, on x[i][j]
   * @param x the vectors, with no variable twice
   * @param strict whether the order is strict
   * @param i the vector of the atom's variable
   * @param j its position in the vector
   * @param out where the reason entries are added
   * @return false when one side of the chain does not give the atom
   */
  public static boolean explain(
      AtomicTrail trail, int entry, IntVar[][] x, boolean strict, int i, int j, EntryList out) {
    if (i < 0 || i >= x.length || j < 0 || j >= x[i].length) {
      return false;
    }
    return new LexChainExplanation(trail, x, strict, entry)
        .explainValues(i, j, trail.removedMin(entry), trail.removedMax(entry), out);
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
        int last = i;
        int first = e.nearestFailingStart(last);
        e.addRows(first, last, -1, -1, e.shortestPrefix(p -> e.chainFails(first, last)), out);
        return true;
      }
    }
    bound = null;
    for (int i = m - 1; i >= 0; i--) {
      bound = e.largestBelow(i, bound);
      if (bound == null) {
        int first = i;
        int last = e.nearestFailingEnd(first);
        e.addRows(first, last, -1, -1, e.shortestPrefix(p -> e.chainFailsDown(first, last)), out);
        return true;
      }
    }
    // both chains have tuples, so some vector has its smallest tuple above its largest one
    for (int i = 0; i < m; i++) {
      if (e.crosses(0, m - 1, i)) {
        int[] window = e.nearestCrossing(i);
        int from = window[0];
        int to = window[1];
        int at = i;
        e.addRows(from, to, -1, -1, e.shortestPrefix(p -> e.crosses(from, to, at)), out);
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the smallest tuple of x[i] above the chain of x[from..i-1] is above the largest one of
   * x[i] below the chain of x[i+1..to], or one of the chains has no tuples.
   */
  private boolean crosses(int from, int to, int i) {
    int[] low = chainUp(from, i);
    int[] high = low == null ? null : chainDown(i, to);
    return low == null || high == null || java.util.Arrays.compare(low, high) > 0;
  }

  /** The smallest window, growing by 1, 2, 4, ... vectors on each side of x[i], that crosses. */
  private int[] nearestCrossing(int i) {
    for (long span = 1; ; span *= 2) {
      int from = (int) Math.max(0, i - span);
      int to = (int) Math.min(m - 1, i + span);
      if (crosses(from, to, i) || (from == 0 && to == m - 1)) {
        return new int[] {from, to};
      }
    }
  }

  /**
   * The shortest prefix of positions whose atoms keep the reason: the smallest limit for which the
   * check holds when the positions beyond it are read as their root domains. Weaker domains give
   * weaker bounds along the chain, so the check holds for every limit above one where it holds; it
   * holds for the whole vectors.
   */
  private int shortestPrefix(java.util.function.IntPredicate holds) {
    int low = 0;
    int high = n - 1;
    while (low < high) {
      int mid = (low + high) >>> 1;
      limit = mid;
      boolean ok = holds.test(mid);
      limit = n - 1;
      if (ok) {
        high = mid;
      } else {
        low = mid + 1;
      }
    }
    return high;
  }

  /**
   * The largest start, among last - 1, last - 2, last - 4, ..., 0, of vectors that have no chain of
   * tuples up to x[last]; the vectors before it are then not needed.
   */
  private int nearestFailingStart(int last) {
    for (long span = 1; last - span > 0; span *= 2) {
      int from = (int) (last - span);
      if (chainFails(from, last)) {
        return from;
      }
    }
    return 0;
  }

  /** Symmetric to {@link #nearestFailingStart} with the chain of largest tuples from x[first]. */
  private int nearestFailingEnd(int first) {
    for (long span = 1; first + span < m - 1; span *= 2) {
      int to = (int) (first + span);
      if (chainFailsDown(first, to)) {
        return to;
      }
    }
    return m - 1;
  }

  /** Whether the vectors from..to have no chain of largest tuples from x[to] down. */
  private boolean chainFailsDown(int from, int to) {
    int[] bound = null;
    for (int i = to; i >= from; i--) {
      bound = largestBelow(i, bound);
      if (bound == null) {
        return true;
      }
    }
    return false;
  }

  /** Whether the vectors from..to have no chain of tuples in the current view of the domains. */
  private boolean chainFails(int from, int to) {
    int[] bound = null;
    for (int i = from; i <= to; i++) {
      bound = smallestAbove(i, bound);
      if (bound == null) {
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
    if (root.intersect(lo, hi).getSize() > MAX_VALUES) {
      return false;
    }
    if (!read(i)) {
      return false;
    }
    int mark = out.size();
    int[] left = new int[16];
    int count = 0;
    for (int u = root.contains(lo) ? lo : root.nextValue(lo); u <= hi; u = root.nextValue(u)) {
      if (!trail.excludedBefore(x[i][j], u, position, out)) {
        if (count == left.length) {
          left = java.util.Arrays.copyOf(left, 2 * count);
        }
        left[count++] = u;
      }
      if (u >= root.max()) {
        break;
      }
    }
    int[] values = java.util.Arrays.copyOf(left, count);
    // the nearest vectors whose chain already rules out the values: up to the 1st, 2nd, 4th, ...
    // vector before x[i] that has an atom (or the same after it), so that a long chain is read only
    // near x[i]; the vectors still at their root domains in between cost no atom
    boolean lower = i > 0;
    boolean upper = i < m - 1;
    int from = i;
    int to = i;
    for (long span = 1; lower || upper; span *= 2) {
      if (lower) {
        int found = 0;
        while (from > 0 && found < span) {
          from--;
          if (!read(from)) {
            out.truncate(mark);
            return false;
          }
          if (!untouched[from]) {
            found++;
          }
        }
        int start = from;
        if (noneAbove(start, i, j, values)) {
          addRows(start, i, i, j, shortestPrefix(p -> noneAbove(start, i, j, values)), out);
          return true;
        }
        lower = from > 0;
      }
      if (upper) {
        int found = 0;
        while (to < m - 1 && found < span) {
          to++;
          if (!read(to)) {
            out.truncate(mark);
            return false;
          }
          if (!untouched[to]) {
            found++;
          }
        }
        int end = to;
        if (noneBelow(end, i, j, values)) {
          addRows(i, end, i, j, shortestPrefix(p -> noneBelow(end, i, j, values)), out);
          return true;
        }
        upper = to < m - 1;
      }
      if (from < i && to > i) {
        int start = from;
        int end = to;
        if (noneBetween(start, end, i, j, values)) {
          addRows(
              start, end, i, j, shortestPrefix(p -> noneBetween(start, end, i, j, values)), out);
          return true;
        }
      }
    }
    out.truncate(mark);
    return false;
  }

  // the bound of the chain of smallest tuples of x[from..to], or null when it has none
  private int[] chainUp(int from, int to) {
    int[] bound = null;
    for (int k = from; k <= to; k++) {
      bound = smallestAbove(k, bound);
      if (bound == null) {
        return null;
      }
    }
    return bound;
  }

  // the bound of the chain of largest tuples of x[to] down to x[from], or null when it has none
  private int[] chainDown(int from, int to) {
    int[] bound = null;
    for (int k = to; k >= from; k--) {
      bound = largestBelow(k, bound);
      if (bound == null) {
        return null;
      }
    }
    return bound;
  }

  // whether, in the current view, no tuple of x[i] with one of the values at j lies between the
  // bounds of the chains of x[from..i-1] from below and of x[i+1..to] from above (or one of those
  // chains has no tuples at all)
  private boolean noneBetween(int from, int to, int i, int j, int[] values) {
    int[] a = chainUp(from, i - 1);
    int[] b = a == null ? null : chainDown(i + 1, to);
    if (a == null || b == null) {
      return true;
    }
    for (int u : values) {
      if (reachesBetween(i, j, u, a, b)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Whether some tuple t of x[i] with u at j has a {@literal <=} t {@literal <=} b ({@literal <}
   * for the strict chain). The positions are read in order, keeping whether the prefix of t so far
   * equals that of a and that of b: four states at most.
   */
  private boolean reachesBetween(int i, int j, int u, int[] a, int[] b) {
    // states: bit 1 = prefix equals a's, bit 2 = prefix equals b's
    boolean[] state = new boolean[4];
    state[3] = true;
    for (int k = 0; k < n; k++) {
      boolean[] next = new boolean[4];
      IntDomain d = dom(i, k);
      for (int s = 0; s < 4; s++) {
        if (!state[s]) {
          continue;
        }
        boolean eqA = (s & 1) != 0;
        boolean eqB = (s & 2) != 0;
        if (!eqA && !eqB) {
          next[0] = true;
          continue;
        }
        long lo = eqA ? a[k] : Long.MIN_VALUE;
        long hi = eqB ? b[k] : Long.MAX_VALUE;
        // t[k] = a[k] keeps the prefix of a, and that of b too when they agree; above b it fails
        if (eqA && (!eqB || a[k] <= b[k]) && has(d, k == j, u, a[k])) {
          next[1 | (eqB && a[k] == b[k] ? 2 : 0)] = true;
        }
        if (eqB && (!eqA || a[k] <= b[k]) && has(d, k == j, u, b[k])) {
          next[2 | (eqA && a[k] == b[k] ? 1 : 0)] = true;
        }
        if (hasInside(d, k == j, u, lo, hi)) {
          // strictly between both prefixes: any suffix will do
          return true;
        }
      }
      state = next;
    }
    if (state[0]) {
      return true;
    }
    if (strict) {
      return false;
    }
    return state[1] || state[2] || state[3];
  }

  // whether position k (fixed to u when it is j) can take value v
  private static boolean has(IntDomain d, boolean fixed, int u, int v) {
    return fixed ? u == v : d.contains(v);
  }

  // whether position k (fixed to u when it is j) has a value strictly between lo and hi
  private static boolean hasInside(IntDomain d, boolean fixed, int u, long lo, long hi) {
    if (fixed) {
      return u > lo && u < hi;
    }
    if (lo >= d.max() || hi <= d.min()) {
      return false;
    }
    long first = lo < d.min() ? d.min() : d.nextValue((int) lo);
    return first < hi && first <= d.max() && first > lo;
  }

  // whether, in the current view, no tuple of x[i] with one of the values at j is above the bound
  // of the vectors from..i-1 (or those vectors have no chain at all)
  private boolean noneAbove(int from, int i, int j, int[] values) {
    int[] bound = null;
    for (int k = from; k < i; k++) {
      bound = smallestAbove(k, bound);
      if (bound == null) {
        return true;
      }
    }
    for (int u : values) {
      if (reachesAbove(i, j, u, bound)) {
        return false;
      }
    }
    return true;
  }

  // symmetric to noneAbove with the vectors x[i+1..to]
  private boolean noneBelow(int to, int i, int j, int[] values) {
    int[] bound = null;
    for (int k = to; k > i; k--) {
      bound = largestBelow(k, bound);
      if (bound == null) {
        return true;
      }
    }
    for (int u : values) {
      if (reachesBelow(i, j, u, bound)) {
        return false;
      }
    }
    return true;
  }

  /** The domain of x[i][k] in the current view: read, or the root domain beyond the limit. */
  private IntDomain dom(int i, int k) {
    return k <= limit ? domain[i][k] : trail.rootDomain(x[i][k]);
  }

  /** Whether some tuple of x[i] with u at j is above (or equal to, unless strict) the bound. */
  private boolean reachesAbove(int i, int j, int u, int[] bound) {
    if (bound == null) {
      return true;
    }
    for (int k = 0; k < n; k++) {
      int t = k == j ? u : dom(i, k).max();
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
      int t = k == j ? u : dom(i, k).min();
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
    int[] t = new int[n];
    if (bound == null) {
      for (int k = 0; k < n; k++) {
        t[k] = dom(i, k).min();
      }
      return t;
    }
    int q = 0;
    while (q < n && dom(i, q).contains(bound[q])) {
      q++;
    }
    if (q == n && !strict) {
      return bound;
    }
    for (int p = Math.min(q, n - 1); p >= 0; p--) {
      if (dom(i, p).max() > bound[p]) {
        System.arraycopy(bound, 0, t, 0, p);
        t[p] = bound[p] < dom(i, p).min() ? dom(i, p).min() : dom(i, p).nextValue(bound[p]);
        for (int k = p + 1; k < n; k++) {
          t[k] = dom(i, k).min();
        }
        return t;
      }
    }
    return null;
  }

  /** The largest tuple of x[i] below the bound, symmetric to {@link #smallestAbove}. */
  private int[] largestBelow(int i, int[] bound) {
    int[] t = new int[n];
    if (bound == null) {
      for (int k = 0; k < n; k++) {
        t[k] = dom(i, k).max();
      }
      return t;
    }
    int q = 0;
    while (q < n && dom(i, q).contains(bound[q])) {
      q++;
    }
    if (q == n && !strict) {
      return bound;
    }
    for (int p = Math.min(q, n - 1); p >= 0; p--) {
      if (dom(i, p).min() < bound[p]) {
        System.arraycopy(bound, 0, t, 0, p);
        t[p] = bound[p] > dom(i, p).max() ? dom(i, p).max() : dom(i, p).previousValue(bound[p]);
        for (int k = p + 1; k < n; k++) {
          t[k] = dom(i, k).max();
        }
        return t;
      }
    }
    return null;
  }

  /** Reads the domains of x[i] before the position; false when one is empty. */
  private boolean read(int i) {
    if (domain[i] != null) {
      return true;
    }
    IntDomain[] d = new IntDomain[n];
    boolean atRoot = true;
    for (int k = 0; k < n; k++) {
      IntVar v = x[i][k];
      int lastEntry = trail.lastEntry(v, position);
      if (lastEntry < 0) {
        d[k] = trail.rootDomain(v);
        continue;
      }
      atRoot = false;
      int lo = trail.minBefore(v, position);
      int hi = trail.maxBefore(v, position);
      if (lo > hi) {
        return false;
      }
      // the root values within the bounds, less the values removed one by one before the position
      IntDomain r = trail.rootDomain(v).intersect(lo, hi).cloneLight();
      for (int e = lastEntry; e >= 0; e = trail.previousEntry(e)) {
        if (trail.kind(e) == AtomicTrail.NE) {
          r.subtractAdapt(trail.value(e));
        }
      }
      if (r.isEmpty()) {
        return false;
      }
      d[k] = r;
    }
    domain[i] = d;
    untouched[i] = atRoot;
    return true;
  }

  /**
   * Adds the atoms of positions 0..last of the vectors from..to, except the variable
   * x[skipRow][skipColumn].
   */
  private void addRows(int from, int to, int skipRow, int skipColumn, int last, EntryList out) {
    for (int i = from; i <= to; i++) {
      for (int k = 0; k <= last; k++) {
        if (i != skipRow || k != skipColumn) {
          trail.atomsBefore(x[i][k], position, out);
        }
      }
    }
  }
}
