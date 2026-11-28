/*
 * ArgMaxMonotone.java
 * <p>
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * The index of the first maximum of values that are nondecreasing functions of variables: index is
 * the first position k of the largest f[k](x[k]). It is {@link ArgMax} over the values {@code y[k]
 * = f[k](x[k])}, run on the arguments x[k] instead of on the y[k].
 *
 * <p>MiniZinc flattens {@code arg_max(t in T)(a[h, t] * e[p[t]])} with one variable per value,
 * {@code y = a * e[p]}, where the p[t] are few variables shared by many arg_max constraints (tower
 * placement: 70 handsets choose among 15 towers by their signal, a scaled function of the tower's
 * power). ArgMax over the y explains with bounds of the y, which belong to one constraint each, so
 * a clause learnt from one handset says nothing about another and the clauses grow long. Here the
 * reasons are bounds of the shared x[k], as CP-SAT gets from its affine encoding of y.
 *
 * <p>Each function is a table over an interval of its argument and is nondecreasing there; a null
 * table is the identity. A value of x outside its table's interval is removed. The rules are those
 * of ArgMax (Gange and Stuckey, CP 2020, for the index), read through the functions: the best value
 * of position k is f[k](max x[k]) and its worst f[k](min x[k]); a bound on the value of k becomes
 * the bound of x[k] at the last (or first) argument that keeps the value within it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ArgMaxMonotone extends Constraint implements SatisfiedPresent, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The most removed arguments passed over one by one to reach one still in a domain. */
  private static final int VALUE_LIMIT = 256;

  /** The arguments. */
  final IntVar[] list;

  /** The function tables, f[k][u - first[k]]; null is the identity. */
  final int[][] f;

  /** The first argument of each table. */
  final int[] first;

  /** The index of the first maximum. */
  final IntVar index;

  /** index = k + 1 + indexOffset for position k. */
  final int indexOffset;

  private final InitOnce init = new InitOnce();

  private final long[] prefixWorst;

  private final long[] suffixWorst;

  private final long[] suffixBest;

  /**
   * It creates the constraint index = first position of max_k f[k](list[k]).
   *
   * @param list the arguments
   * @param f the tables of nondecreasing functions, f[k][u - first[k]] for argument u; null entries
   *     are the identity
   * @param first the first argument of each table
   * @param index the index of the first maximum
   * @param indexOffset the index of position k is k + 1 + indexOffset
   */
  public ArgMaxMonotone(IntVar[] list, int[][] f, int[] first, IntVar index, int indexOffset) {
    checkInputForNullness(new String[] {"list", "index"}, list, new Object[] {index});
    if (list.length == 0 || f.length != list.length || first.length != list.length) {
      throw new IllegalArgumentException("ArgMaxMonotone needs one function per variable");
    }
    for (int k = 0; k < f.length; k++) {
      if (f[k] == null) {
        continue;
      }
      if (f[k].length == 0) {
        throw new IllegalArgumentException("ArgMaxMonotone: empty function table at " + k);
      }
      for (int i = 1; i < f[k].length; i++) {
        if (f[k][i] < f[k][i - 1]) {
          throw new IllegalArgumentException("ArgMaxMonotone: decreasing function at " + k);
        }
      }
    }
    this.queueIndex = 1;
    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.f = Arrays.copyOf(f, f.length);
    this.first = Arrays.copyOf(first, first.length);
    this.index = index;
    this.indexOffset = indexOffset;
    this.prefixWorst = new long[list.length + 1];
    this.suffixWorst = new long[list.length + 1];
    this.suffixBest = new long[list.length + 1];
    setScope(Stream.concat(Arrays.stream(list), Stream.of(index)));
  }

  /**
   * The value of position k at argument u; an argument outside the table's interval, which the
   * constraint removes, reads as the nearest end of the table.
   */
  long value(int k, int u) {
    if (f[k] == null) {
      return u;
    }
    int i = (int) Math.clamp((long) u - first[k], 0L, f[k].length - 1L);
    return f[k][i];
  }

  /** The largest argument of position k up to hi whose value is at most v, or lo - 1. */
  private int lastAtMost(int k, int lo, int hi, long v) {
    if (f[k] == null) {
      return (int) Math.clamp(v, lo - 1L, (long) hi);
    }
    // binary search over the nondecreasing table
    int a = lo;
    int b = hi;
    int r = lo - 1;
    while (a <= b) {
      int m = (int) (((long) a + b) >> 1);
      if (f[k][m - first[k]] <= v) {
        r = m;
        a = m + 1;
      } else {
        b = m - 1;
      }
    }
    return r;
  }

  /** The smallest argument of position k from lo whose value is at least v, or hi + 1. */
  private int firstAtLeast(int k, int lo, int hi, long v) {
    if (f[k] == null) {
      return (int) Math.clamp(v, (long) lo, hi + 1L);
    }
    int a = lo;
    int b = hi;
    int r = hi + 1;
    while (a <= b) {
      int m = (int) (((long) a + b) >> 1);
      if (f[k][m - first[k]] >= v) {
        r = m;
        b = m - 1;
      } else {
        a = m + 1;
      }
    }
    return r;
  }

  private long best(int k) {
    return value(k, list[k].max());
  }

  private long worst(int k) {
    return value(k, list[k].min());
  }

  @Override
  public void consistency(Store store) {
    if (init.begin(store)) {
      index.domain.in(store.level, index, 1 + indexOffset, list.length + indexOffset);
    }
    // every time: the arguments outside the tables (the first restriction may be undone)
    for (int k = 0; k < list.length; k++) {
      IntVar x = list[k];
      if (f[k] != null && (x.min() < first[k] || x.max() >= first[k] + f[k].length)) {
        x.domain.in(store.level, x, first[k], first[k] + f[k].length - 1);
      }
    }
    if (index.min() < 1 + indexOffset || index.max() > list.length + indexOffset) {
      index.domain.in(store.level, index, 1 + indexOffset, list.length + indexOffset);
    }
    do {
      store.propagationHasOccurred = false;
      propagate(store);
    } while (store.propagationHasOccurred);
  }

  // a value of position k at most v
  private void valueAtMost(Store store, int k, long v) {
    IntVar x = list[k];
    if (best(k) <= v) {
      return;
    }
    int u = lastAtMost(k, x.min(), x.max(), v);
    if (u < x.min()) {
      throw Store.failException;
    }
    x.domain.inMax(store.level, x, u);
  }

  // a value of position k at least v
  private void valueAtLeast(Store store, int k, long v) {
    IntVar x = list[k];
    if (worst(k) >= v) {
      return;
    }
    int u = firstAtLeast(k, x.min(), x.max(), v);
    if (u > x.max()) {
      throw Store.failException;
    }
    x.domain.inMin(store.level, x, u);
  }

  private void propagate(Store store) {
    // the largest worst value among the indexes left, and the largest best value
    long lb = Long.MIN_VALUE;
    long ub = Long.MIN_VALUE;
    int pos = -1;
    int ubPos = -1;
    for (ValueEnumeration e = index.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int k = e.nextElement() - 1 - indexOffset;
      long w = worst(k);
      if (lb < w) {
        lb = w;
        pos = k;
      }
      long b = best(k);
      if (ub < b) {
        ub = b;
        ubPos = k;
      }
    }
    if (lb == ub) {
      index.domain.inMax(store.level, index, pos + 1 + indexOffset);
    }

    pruneIndex(store);

    // the first index left with the largest best value, when its value is fixed
    ub = Long.MIN_VALUE;
    ubPos = -1;
    for (ValueEnumeration e = index.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int k = e.nextElement() - 1 - indexOffset;
      long b = best(k);
      if (ub < b) {
        ub = b;
        ubPos = k;
      }
    }
    if (worst(ubPos) == ub) {
      index.domain.in(store.level, index, ubPos + 1 + indexOffset, ubPos + 1 + indexOffset);
    }

    if (index.singleton()) {
      int i = index.value() - 1 - indexOffset;
      for (int k = 0; k < list.length; k++) {
        if (k == i) {
          continue;
        }
        if (k < i) {
          valueAtMost(store, k, best(i) - 1);
          valueAtLeast(store, i, worst(k) + 1);
        } else {
          valueAtMost(store, k, best(i));
          valueAtLeast(store, i, worst(k));
        }
      }
    } else {
      boundValuesByIndex(store, ub);
    }
  }

  /*
   * A position the index can take has a value at most ub, the largest best value over those
   * positions. A position it cannot take may not reach the first maximum: its value stays at most
   * the best value of an index position before it, or below the best value of one after it.
   */
  private void boundValuesByIndex(Store store, long ub) {
    int n = list.length;
    suffixBest[n] = Long.MIN_VALUE;
    for (int k = n - 1; k >= 0; k--) {
      suffixBest[k] = suffixBest[k + 1];
      if (index.domain.contains(k + 1 + indexOffset)) {
        suffixBest[k] = Math.max(suffixBest[k], best(k));
      }
    }
    long before = Long.MIN_VALUE;
    for (int k = 0; k < n; k++) {
      if (index.domain.contains(k + 1 + indexOffset)) {
        valueAtMost(store, k, ub);
        before = Math.max(before, best(k));
      } else {
        long after = suffixBest[k + 1] == Long.MIN_VALUE ? Long.MIN_VALUE : suffixBest[k + 1] - 1;
        long bound = Math.max(before, after);
        if (bound < worst(k)) {
          throw Store.failException;
        }
        valueAtMost(store, k, Math.min(bound, ub));
      }
    }
  }

  // the index keeps the positions that can hold the first maximum
  private void pruneIndex(Store store) {
    int n = list.length;
    prefixWorst[0] = Long.MIN_VALUE;
    for (int k = 0; k < n; k++) {
      prefixWorst[k + 1] = Math.max(prefixWorst[k], worst(k));
    }
    suffixWorst[n] = Long.MIN_VALUE;
    for (int k = n - 1; k >= 0; k--) {
      suffixWorst[k] = Math.max(suffixWorst[k + 1], worst(k));
    }
    int kept = 0;
    int removed = 0;
    for (ValueEnumeration e = index.dom().valueEnumeration(); e.hasMoreElements(); ) {
      if (canBeFirst(e.nextElement() - 1 - indexOffset)) {
        kept++;
      } else {
        removed++;
      }
    }
    if (kept == 0) {
      throw Store.failException;
    }
    if (removed == 0) {
      return;
    }
    IntervalDomain d = new IntervalDomain();
    for (ValueEnumeration e = index.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int v = e.nextElement();
      if (canBeFirst(v - 1 - indexOffset)) {
        if (d.getSize() == 0) {
          d.unionAdapt(v, v);
        } else {
          d.addLastElement(v);
        }
      }
    }
    index.domain.in(store.level, index, d);
  }

  private boolean canBeFirst(int k) {
    long b = best(k);
    return b > prefixWorst[k] && b >= suffixWorst[k + 1];
  }

  @Override
  public boolean satisfied() {
    if (!index.singleton()) {
      return false;
    }
    int i = index.value() - 1 - indexOffset;
    if (i < 0 || i >= list.length) {
      return false;
    }
    long w = worst(i);
    for (int k = 0; k < list.length; k++) {
      if (k != i && (k < i ? best(k) >= w : best(k) > w)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return v == index ? IntDomain.ANY : IntDomain.BOUND;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return new Explanation(trail, entry).explain(entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return new Explanation(trail, trail.size()).explainFailure(out);
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ArgMaxMonotone([");
    for (int k = 0; k < list.length; k++) {
      if (k > 0) {
        result.append(", ");
      }
      result.append(list[k]);
      if (f[k] != null) {
        result.append(" -> ").append(Arrays.toString(f[k])).append(" from ").append(first[k]);
      }
    }
    result.append("], ").append(index).append(", ").append(indexOffset).append(")");
    return result.toString();
  }

  /**
   * Explanations, as {@code ArgExtremumExplanation} gives them for ArgMax, with the values read
   * through the functions and each bound cited at the weakest argument that serves.
   */
  private final class Explanation {

    private final AtomicTrail trail;
    private final int position;

    Explanation(AtomicTrail trail, int position) {
      this.trail = trail;
      this.position = position;
    }

    boolean explain(int entry, EntryList out) {
      IntVar y = trail.variable(entry);
      int a = trail.value(entry);
      int kind = trail.kind(entry);
      int mark = out.size();
      if (y == index) {
        boolean done =
            switch (kind) {
              case AtomicTrail.GE -> indexesImpossible(Integer.MIN_VALUE, a - 1, out);
              case AtomicTrail.LE -> indexesImpossible(a + 1, Integer.MAX_VALUE, out);
              default -> indexesImpossible(a, a, out);
            };
        if (done) {
          return true;
        }
        out.truncate(mark);
      }
      if (kind == AtomicTrail.NE) {
        return false;
      }
      boolean upper = kind == AtomicTrail.LE;
      for (int k = 0; k < list.length; k++) {
        if (list[k] != y) {
          continue;
        }
        boolean done = upper ? aboveImpossible(k, a + 1, out) : belowImpossible(k, a - 1, out);
        if (done) {
          return true;
        }
        out.truncate(mark);
      }
      return false;
    }

    boolean explainFailure(EntryList out) {
      int mark = out.size();
      if (indexesImpossible(Integer.MIN_VALUE, Integer.MAX_VALUE, out)) {
        return true;
      }
      out.truncate(mark);
      for (int k = 0; k < list.length; k++) {
        trail.addLowerBound(list[k], position, out);
        if (aboveImpossible(k, trail.minBefore(list[k], position), out)) {
          return true;
        }
        out.truncate(mark);
        trail.addUpperBound(list[k], position, out);
        if (belowImpossible(k, trail.maxBefore(list[k], position), out)) {
          return true;
        }
        out.truncate(mark);
      }
      return false;
    }

    private long high(int k) {
      return value(k, trail.maxBefore(list[k], position));
    }

    private long low(int k) {
      return value(k, trail.minBefore(list[k], position));
    }

    // the root interval of x[k] within its table
    private int lowest(int k) {
      int m = trail.rootDomain(list[k]).min();
      return f[k] == null ? m : Math.max(m, first[k]);
    }

    private int highest(int k) {
      int m = trail.rootDomain(list[k]).max();
      return f[k] == null ? m : Math.min(m, first[k] + f[k].length - 1);
    }

    // the bound of x[k] that gives a value at most v (the value is at most v now)
    private void addHigh(int k, long v, EntryList out) {
      int u = lastAtMost(k, lowest(k), highest(k), v);
      trail.addBoundReaching(list[k], position, false, u, out);
    }

    // the bound of x[k] that gives a value at least v (the value is at least v now)
    private void addLow(int k, long v, EntryList out) {
      int u = firstAtLeast(k, lowest(k), highest(k), v);
      trail.addBoundReaching(list[k], position, true, u, out);
    }

    private boolean indexesImpossible(int lo, int hi, EntryList out) {
      int from = Math.max(lo, 1 + indexOffset);
      int to = Math.min(hi, list.length + indexOffset);
      int min = trail.minBefore(index, position);
      if (from < min) {
        trail.addLowerBound(index, position, out);
        from = min;
      }
      int maxIndex = trail.maxBefore(index, position);
      if (to > maxIndex) {
        trail.addUpperBound(index, position, out);
        to = maxIndex;
      }
      for (int v = from; v <= to; v++) {
        if (!trail.excludedBefore(index, v, position, out) && !notFirst(v - 1 - indexOffset, out)) {
          return false;
        }
      }
      return true;
    }

    // position j cannot be the first maximum because of one other position
    private boolean notFirst(int j, EntryList out) {
      long best = high(j);
      for (int i = 0; i < list.length; i++) {
        if (i == j) {
          continue;
        }
        long w = low(i);
        if (i < j ? w >= best : w > best) {
          // value(j) <= w (i before j) or <= w - 1 (i after j), and value(i) >= w
          addLow(i, w, out);
          addHigh(j, i < j ? w : w - 1, out);
          return true;
        }
      }
      return false;
    }

    // x[k] cannot take any argument from u up
    private boolean aboveImpossible(int k, int u, EntryList out) {
      u = firstKept(k, u, 1, out);
      if (u == Integer.MAX_VALUE) {
        return true;
      }
      if (u == Integer.MIN_VALUE) {
        return false;
      }
      long v = value(k, u);
      for (int j = 0; j < list.length; j++) {
        int idx = j + 1 + indexOffset;
        if (j == k) {
          if (!trail.excludedBefore(index, idx, position, out)) {
            return false;
          }
        } else if (j > k ? high(j) <= v : high(j) < v) {
          addHigh(j, j > k ? v : v - 1, out);
        } else if (!trail.excludedBefore(index, idx, position, out)) {
          return false;
        }
      }
      return true;
    }

    // x[k] cannot take any argument from u down
    private boolean belowImpossible(int k, int u, EntryList out) {
      u = firstKept(k, u, -1, out);
      if (u == Integer.MIN_VALUE) {
        return true;
      }
      if (u == Integer.MAX_VALUE) {
        return false;
      }
      for (int j = 0; j < list.length; j++) {
        if (j != k && !trail.excludedBefore(index, j + 1 + indexOffset, position, out)) {
          return false;
        }
      }
      if (trail.excludedBefore(index, k + 1 + indexOffset, position, out)) {
        return true;
      }
      long v = value(k, u);
      for (int i = 0; i < list.length; i++) {
        if (i != k && (i < k ? low(i) >= v : low(i) > v)) {
          addLow(i, i < k ? v : v + 1, out);
          return true;
        }
      }
      return false;
    }

    /**
     * Walks from argument u in direction step over arguments already out of x[k]'s domain (adding
     * their entries) and returns the first one in it; past the domain it returns MAX_VALUE going up
     * and MIN_VALUE going down, and the opposite when too many arguments are in the way.
     */
    private int firstKept(int k, int u, int step, EntryList out) {
      IntVar x = list[k];
      int end = step > 0 ? trail.maxBefore(x, position) : trail.minBefore(x, position);
      IntDomain r = trail.rootDomain(x);
      int count = 0;
      int at = u;
      while (step > 0 ? at <= end : at >= end) {
        if (r.contains(at)) {
          if (count++ == VALUE_LIMIT) {
            return step > 0 ? Integer.MIN_VALUE : Integer.MAX_VALUE;
          }
          if (!trail.excludedBefore(x, at, position, out)) {
            return at;
          }
          at += step;
        } else {
          // values outside the initial domain need no atom, so they are skipped without counting
          int next = step > 0 ? r.nextValue(at) : r.previousValue(at);
          at = next == at ? (step > 0 ? end + 1 : end - 1) : next;
        }
      }
      if (step > 0) {
        trail.addUpperBound(x, position, out);
        return Integer.MAX_VALUE;
      }
      trail.addLowerBound(x, position, out);
      return Integer.MIN_VALUE;
    }
  }
}
