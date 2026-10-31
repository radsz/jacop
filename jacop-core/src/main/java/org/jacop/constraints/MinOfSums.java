/*
 * MinOfSums.java
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * The minimum of sums: m = min(x[0] + y[0], x[1] + y[1], ...), where a term without a second
 * variable (y[i] null) is x[i] alone.
 *
 * <p>It is the decomposition z[i] = x[i] + y[i], m = min(z) without the variables z[i]: shortest
 * path models (road-cons, sp[s + 1] = min(sp[s], sp[x, z, s] + sp[z, y, s])) have one such sum for
 * every pair of edges, 130k on road_26, and each change of a sum woke both constraints. The pruning
 * is that of the decomposition on bounds: m between the least low and the least high of the terms,
 * every term at least m's low, and the only term that can reach m's high at most that high. Unlike
 * {@link Min} it does not copy the values removed inside m's domain into the last term. Under lazy
 * clause generation it explains its bounds itself, with the bounds weakened as far as the pruning
 * allows.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class MinOfSums extends Constraint
    implements SatisfiedPresent, Copyable<MinOfSums>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // an upper bound of a term that leaves it free; an int can be subtracted from it
  private static final long NO_UPPER = Long.MAX_VALUE / 4;

  final IntVar[] x;

  final IntVar[] y;

  final IntVar m;

  // the terms from position on can reach m's high; the terms before it are above it
  private TimeStamp<Integer> position;

  /**
   * It constructs the minimum of sums.
   *
   * @param x the first variable of each term.
   * @param y the second variable of each term, null for a term of one variable.
   * @param m the minimum.
   */
  public MinOfSums(IntVar[] x, IntVar[] y, IntVar m) {
    checkInputForNullness("x", x);
    checkInputForNullness("m", new Object[] {m});
    if (y.length != x.length) {
      throw new IllegalArgumentException("MinOfSums needs as many y as x.");
    }
    if (x.length == 0) {
      throw new IllegalArgumentException("MinOfSums needs at least one term.");
    }
    for (int i = 0; i < x.length; i++) {
      if (x[i] == m || y[i] == m || x[i] == y[i]) {
        throw new IllegalArgumentException(
            "MinOfSums needs m outside the terms and two variables in a term.");
      }
    }
    this.x = Arrays.copyOf(x, x.length);
    this.y = Arrays.copyOf(y, y.length);
    this.m = m;
    this.queueIndex = x.length > 1000 ? 2 : 1;
    this.numberId = idNumber.incrementAndGet();
    setScope(
        Stream.<Var>concat(Stream.concat(Arrays.stream(x), Arrays.stream(y)), Stream.of(m))
            .filter(Objects::nonNull));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {
    super.impose(store);
    position = new TimeStamp<>(store, 0);
  }

  private void swap(int i, int j) {
    if (i != j) {
      IntVar t = x[i];
      x[i] = x[j];
      x[j] = t;
      t = y[i];
      y[i] = y[j];
      y[j] = t;
    }
  }

  private long low(int i) {
    IntVar b = y[i];
    return b == null ? x[i].min() : (long) x[i].min() + b.min();
  }

  private long high(int i) {
    IntVar b = y[i];
    return b == null ? x[i].max() : (long) x[i].max() + b.max();
  }

  // keeps term i within from..to
  private static void within(Store store, IntVar a, IntVar b, long from, long to) {
    if (b == null) {
      bound(store, a, from, to);
      return;
    }
    bound(store, a, from - b.max(), to - b.min());
    bound(store, b, from - a.max(), to - a.min());
  }

  private static void bound(Store store, IntVar v, long from, long to) {
    if (from > v.min() || to < v.max()) {
      int f = (int) Math.max(from, IntDomain.MIN_INT);
      int t = (int) Math.min(to, IntDomain.MAX_INT);
      if (f > t) {
        throw Store.failException;
      }
      v.domain.in(store.level, v, f, t);
    }
  }

  @Override
  public void consistency(Store store) {
    int start = position.value();
    int n = x.length;
    do {
      store.propagationHasOccurred = false;
      long mMin = m.min();
      long mMax = m.max();
      long leastLow = Long.MAX_VALUE;
      long leastHigh = Long.MAX_VALUE;
      for (int i = start; i < n; i++) {
        if (mMin > low(i)) {
          within(store, x[i], y[i], mMin, NO_UPPER);
        }
        long l = low(i);
        if (l > mMax) {
          swap(start, i);
          start++;
          continue;
        }
        leastLow = Math.min(leastLow, l);
        leastHigh = Math.min(leastHigh, high(i));
      }
      if (start == n) {
        throw Store.failException;
      }
      bound(store, m, leastLow, leastHigh);
      if (start == n - 1) {
        // the only term that can reach m is at most m's high
        within(store, x[start], y[start], m.min(), m.max());
      }
    } while (store.propagationHasOccurred);
    position.update(start);
  }

  @Override
  public boolean satisfied() {
    if (!m.singleton()) {
      return false;
    }
    boolean reached = false;
    for (int i = 0; i < x.length; i++) {
      if (!x[i].singleton() || y[i] != null && !y[i].singleton()) {
        return false;
      }
      long v = low(i);
      if (v != high(i) || v < m.value()) {
        return false;
      }
      reached |= v == m.value();
    }
    return reached;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : minOfSums([");
    for (int i = 0; i < x.length; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(x[i]);
      if (y[i] != null) {
        result.append(" + ").append(y[i]);
      }
    }
    result.append("], ").append(m).append(")");
    return result.toString();
  }

  @Override
  public MinOfSums copy(VarMap map) {
    IntVar[] ys = new IntVar[y.length];
    for (int i = 0; i < y.length; i++) {
      ys[i] = y[i] == null ? null : map.get(y[i]);
    }
    return new MinOfSums(map.get(x), ys, map.get(m));
  }

  // ------------------------------------------------------------------ explanations

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return false;
    }
    IntVar v = trail.variable(entry);
    boolean lower = kind == AtomicTrail.GE;
    if (v == m) {
      return lower ? minAtLeast(trail, entry, out) : minAtMost(trail, entry, out);
    }
    // the bound the pruning computed, before the domain skipped its holes
    int bound = trail.skippedBound(entry);
    int mark = out.size();
    for (int i = 0; i < x.length; i++) {
      IntVar other = x[i] == v ? y[i] : y[i] == v ? x[i] : null;
      if (other == null && x[i] != v) {
        continue;
      }
      boolean found =
          lower
              ? termAtLeast(trail, entry, other, bound, out)
              : onlyTerm(trail, entry, i, other, bound, out);
      if (found) {
        trail.addSkippedHoles(entry, bound, out);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // v >= bound in a term v + other: the term is at least m's low, so v >= m - other
  private boolean termAtLeast(
      AtomicTrail trail, int entry, IntVar other, long bound, EntryList out) {
    long mLow = trail.minBefore(m, entry);
    if (other == null) {
      return mLow >= bound && cite(trail.earliestLowerBound(m, bound, entry), out);
    }
    long oHigh = trail.maxBefore(other, entry);
    if (mLow - oHigh < bound) {
      return false;
    }
    long used = trail.addBoundReaching(other, entry, false, mLow - bound, out);
    trail.addBoundReaching(m, entry, true, bound + used, out);
    return true;
  }

  // v <= bound in term j, the only one that can reach m's high H: the other terms are above H, so
  // v <= H - other
  private boolean onlyTerm(
      AtomicTrail trail, int entry, int j, IntVar other, long bound, EntryList out) {
    long mHigh = trail.maxBefore(m, entry);
    long oLow = other == null ? 0 : trail.minBefore(other, entry);
    if (mHigh - oLow > bound) {
      return false;
    }
    for (int i = 0; i < x.length; i++) {
      if (i != j && !termAbove(trail, entry, i, mHigh + 1, out)) {
        return false;
      }
    }
    // m's high itself, which the other terms are above
    trail.addBoundReaching(m, entry, false, mHigh, out);
    if (other != null) {
      trail.addBoundReaching(other, entry, true, mHigh - bound, out);
    }
    return true;
  }

  // the low of term i reaches limit before the position: x[i] + y[i] >= limit
  private boolean termAbove(AtomicTrail trail, int position, int i, long limit, EntryList out) {
    return termReaching(trail, position, i, true, limit, out);
  }

  // the high of term i reaches limit before the position: x[i] + y[i] <= limit
  private boolean termBelow(AtomicTrail trail, int position, int i, long limit, EntryList out) {
    return termReaching(trail, position, i, false, limit, out);
  }

  // the low (lower) or the high of term i reaches limit before the position
  private boolean termReaching(
      AtomicTrail trail, int position, int i, boolean lower, long limit, EntryList out) {
    IntVar a = x[i];
    IntVar b = y[i];
    if (b == null) {
      return cite(
          lower
              ? trail.earliestLowerBound(a, limit, position)
              : trail.earliestUpperBound(a, limit, position),
          out);
    }
    long bBound = lower ? trail.minBefore(b, position) : trail.maxBefore(b, position);
    long sum = (lower ? trail.minBefore(a, position) : trail.maxBefore(a, position)) + bBound;
    if (lower ? sum < limit : sum > limit) {
      return false;
    }
    long used = trail.addBoundReaching(a, position, lower, limit - bBound, out);
    trail.addBoundReaching(b, position, lower, limit - used, out);
    return true;
  }

  // m >= a: every term at least t, the least low (or a), and m's values from t to a - 1 out
  private boolean minAtLeast(AtomicTrail trail, int entry, EntryList out) {
    long a = trail.value(entry);
    long t = a;
    for (int i = 0; i < x.length; i++) {
      long l = trail.minBefore(x[i], entry) + (y[i] == null ? 0L : trail.minBefore(y[i], entry));
      t = Math.min(t, l);
    }
    if (a - t > MAX_HOLES) {
      return false;
    }
    for (int i = 0; i < x.length; i++) {
      if (!termAbove(trail, entry, i, t, out)) {
        return false;
      }
    }
    return excluded(trail, entry, t, a - 1, out);
  }

  // m <= a: the term of the least high T at most T, and m's values from a + 1 to T out
  private boolean minAtMost(AtomicTrail trail, int entry, EntryList out) {
    long a = trail.value(entry);
    long least = Long.MAX_VALUE;
    int j = -1;
    for (int i = 0; i < x.length; i++) {
      long h = trail.maxBefore(x[i], entry) + (y[i] == null ? 0L : trail.maxBefore(y[i], entry));
      if (h < least) {
        least = h;
        j = i;
      }
    }
    long t = Math.max(a, least);
    if (t - a > MAX_HOLES) {
      return false;
    }
    return termBelow(trail, entry, j, t, out) && excluded(trail, entry, a + 1, t, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int now = trail.size();
    long mLow = trail.minBefore(m, now);
    long mHigh = trail.maxBefore(m, now);
    // a term below m's low
    for (int i = 0; i < x.length; i++) {
      long h = trail.maxBefore(x[i], now) + (y[i] == null ? 0L : trail.maxBefore(y[i], now));
      if (h < mLow) {
        int mark = out.size();
        if (termBelow(trail, now, i, h, out)
            && cite(trail.earliestLowerBound(m, h + 1, now), out)) {
          return true;
        }
        out.truncate(mark);
      }
    }
    // every term above m's high
    for (int i = 0; i < x.length; i++) {
      if (!termAbove(trail, now, i, mHigh + 1, out)) {
        return false;
      }
    }
    trail.addBoundReaching(m, now, false, mHigh, out);
    return true;
  }

  // values of m excluded from one explanation of its bound before giving up on it
  private static final int MAX_HOLES = 64;

  // m's values from..to are out of its domain before the position
  private boolean excluded(AtomicTrail trail, int position, long from, long to, EntryList out) {
    for (long u = from; u <= to; u++) {
      if (!trail.excludedBefore(m, (int) u, position, out)) {
        return false;
      }
    }
    return true;
  }

  // adds the entry of an earliest bound: -1 is the initial domain, MAX_VALUE no such bound
  private static boolean cite(int e, EntryList out) {
    if (e == Integer.MAX_VALUE) {
      return false;
    }
    if (e >= 0) {
      out.add(e);
    }
    return true;
  }
}
