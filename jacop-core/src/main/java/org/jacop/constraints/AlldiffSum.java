/*
 * AlldiffSum.java
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
import java.util.PriorityQueue;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * The conjunction of alldifferent(x) and sum(x) rel sum, where rel is ==, &lt;= or &gt;=. It
 * reaches bounds consistency on the conjunction (over the intervals of the domains) with the O(n
 * log n) algorithm of N. Beldiceanu, M. Carlsson, T. Petit and J.-C. Régin, "An O(n log n) Bound
 * Consistency Algorithm for the Conjunction of an alldifferent and an Inequality between a Sum of
 * Variables and a Constant, and its Generalization", ECAI 2012.
 *
 * <p>Each pass runs bounds consistency of alldifferent, computes the smallest sum of distinct
 * values the variables can take (values in increasing order, each given to the waiting variable
 * with the smallest maximum), and lowers the maxima so that this smallest sum, with one variable
 * moved to its new maximum, stays within the maximum of sum. The minima are filtered the same way
 * on the negated values. The sum alone, without the alldifferent, only sees the sum of the minima;
 * this constraint sees for example that three different digits sum to at least 1 + 2 + 3.
 *
 * <p>The alldifferent is part of the semantics, so this constraint can be posted alone. Posted next
 * to an alldifferent on a superset of x and a linear constraint (killer sudoku cages, rows of magic
 * squares, kakuro runs), it adds the pruning neither of them makes.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class AlldiffSum extends Constraint
    implements SatisfiedPresent, Copyable<AlldiffSum>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  static final int EQ = 0;
  static final int LE = 1;
  static final int GE = 2;

  /** The variables that are all different and summed. */
  final IntVar[] list;

  /** The variable the sum is compared to. */
  final IntVar sum;

  final int relation;

  // bounds consistency of the alldifferent; never imposed
  private final Alldiff hall;

  // bounds of the variables, negated when filtering the minima
  private final long[] lo;
  private final long[] hi;
  // positions sorted by lo, kept between calls so the insertion sort runs on nearly sorted data
  private final int[] byLo;
  // binary heap of positions keyed by hi
  private final int[] heap;
  // the k-th variable of the smallest sum, the value it gets, and the first value of the run of
  // consecutive values given to variables that contains it
  private final int[] matchedVar;
  private final long[] value;
  private final long[] runStart;
  private final long[] suffixMinLo;

  /**
   * It constructs alldifferent(list) and sum(list) rel sum.
   *
   * @param list the variables, all different.
   * @param rel the relation, one of "==", "&lt;=", "&gt;=".
   * @param sum the variable the sum of list is compared to.
   */
  public AlldiffSum(IntVar[] list, String rel, IntVar sum) {
    this(list, rel, sum, true);
  }

  /**
   * It constructs alldifferent(list) and sum(list) rel sum.
   *
   * @param list the variables, all different.
   * @param rel the relation, one of "==", "&lt;=", "&gt;=".
   * @param sum the variable the sum of list is compared to.
   * @param hallIntervals false when a bounds consistent alldifferent on list or on a superset of
   *     list is posted as well: the pruning on Hall intervals is then left to it. The result at the
   *     fixpoint is the same, each call is cheaper, and the alldifferent is still enforced (the
   *     smallest sum fails when the values cannot be all different).
   */
  public AlldiffSum(IntVar[] list, String rel, IntVar sum, boolean hallIntervals) {

    checkInputForNullness("list", list);
    checkInputForNullness("sum", new Object[] {sum});

    this.relation =
        switch (rel) {
          case "==", "=" -> EQ;
          case "<=" -> LE;
          case ">=" -> GE;
          default ->
              throw new IllegalArgumentException("AlldiffSum: relation must be ==, <= or >=");
        };
    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.sum = sum;
    this.queueIndex = 2;

    int n = list.length;
    this.hall = hallIntervals && n > 1 ? new Alldiff(this.list) : null;
    lo = new long[n];
    hi = new long[n];
    byLo = new int[n];
    for (int i = 0; i < n; i++) {
      byLo[i] = i;
    }
    heap = new int[n];
    matchedVar = new int[n];
    value = new long[n];
    runStart = new long[n];
    suffixMinLo = new long[n + 1];

    setScope(Stream.concat(Arrays.stream(this.list), Stream.of(sum)));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {
    do {
      store.propagationHasOccurred = false;

      if (hall != null) {
        hall.hallIntervalPass(store);
      }
      if (relation != GE) {
        long minSum = filter(store, false, sum.max());
        if (minSum > sum.min()) {
          sum.domain.inMin(store.level, sum, (int) minSum);
        }
      }
      if (relation != LE) {
        long maxSum = -filter(store, true, -(long) sum.min());
        if (maxSum < sum.max()) {
          sum.domain.inMax(store.level, sum, (int) maxSum);
        }
      }
    } while (store.propagationHasOccurred);
  }

  /**
   * Computes the smallest sum of distinct values and lowers the maxima of the variables so that the
   * sum stays at most cst. With negated set, it works on the negated variables, so it computes
   * minus the largest sum and raises the minima.
   *
   * @return the smallest sum, at most cst.
   */
  private long filter(Store store, boolean negated, long cst) {
    int n = list.length;
    for (int i = 0; i < n; i++) {
      IntDomain d = list[i].dom();
      lo[i] = negated ? -(long) d.max() : d.min();
      hi[i] = negated ? -(long) d.min() : d.max();
    }
    sortByLo(n);

    // phase 2: the smallest sum; values in increasing order, each to the waiting variable with the
    // smallest maximum
    long smallest = 0;
    long current = Long.MIN_VALUE / 2;
    int heapSize = 0;
    int next = 0;
    for (int k = 0; k < n; k++) {
      current = Math.max(current + 1, lo[byLo[k]]);
      while (next < n && lo[byLo[next]] <= current) {
        heapSize = heapPush(heapSize, byLo[next++]);
      }
      int i = heap[0];
      heapSize = heapPop(heapSize);
      if (hi[i] < current) {
        throw Store.failException;
      }
      matchedVar[k] = i;
      value[k] = current;
      runStart[k] = k > 0 && value[k - 1] == current - 1 ? runStart[k - 1] : current;
      smallest += current;
    }
    if (smallest > cst) {
      throw Store.failException;
    }

    // phase 3: blocks of the matching; a block ends at q when every later variable has its minimum
    // above value[q]. A variable of block b moved to u above the block costs
    // smallest - last(b) + next(u), next(u) the smallest value >= u given to no variable
    suffixMinLo[n] = Long.MAX_VALUE;
    for (int k = n - 1; k >= 0; k--) {
      suffixMinLo[k] = Math.min(suffixMinLo[k + 1], lo[matchedVar[k]]);
    }
    int first = 0;
    for (int q = 0; q < n; q++) {
      if (suffixMinLo[q + 1] <= value[q]) {
        continue;
      }
      long last = value[q];
      long newMax = Math.max(last, largestFreeValueAtMost(cst - smallest + last, n));
      for (int k = first; k <= q; k++) {
        int i = matchedVar[k];
        if (newMax < hi[i]) {
          IntVar x = list[i];
          if (negated) {
            x.domain.inMin(store.level, x, (int) -newMax);
          } else {
            x.domain.inMax(store.level, x, (int) newMax);
          }
        }
      }
      first = q + 1;
    }
    return smallest;
  }

  // the largest value at most t that the smallest sum gives to no variable
  private long largestFreeValueAtMost(long t, int n) {
    int a = 0;
    int b = n - 1;
    int k = -1;
    while (a <= b) {
      int m = (a + b) >>> 1;
      if (value[m] <= t) {
        k = m;
        a = m + 1;
      } else {
        b = m - 1;
      }
    }
    if (k < 0 || value[k] < t) {
      return t;
    }
    return runStart[k] - 1;
  }

  private void sortByLo(int n) {
    for (int i = 1; i < n; i++) {
      int e = byLo[i];
      long key = lo[e];
      int j = i - 1;
      while (j >= 0 && lo[byLo[j]] > key) {
        byLo[j + 1] = byLo[j];
        j--;
      }
      byLo[j + 1] = e;
    }
  }

  private int heapPush(int size, int i) {
    int c = size;
    while (c > 0) {
      int p = (c - 1) >>> 1;
      if (hi[heap[p]] <= hi[i]) {
        break;
      }
      heap[c] = heap[p];
      c = p;
    }
    heap[c] = i;
    return size + 1;
  }

  private int heapPop(int size) {
    int last = heap[--size];
    int c = 0;
    while (true) {
      int l = 2 * c + 1;
      if (l >= size) {
        break;
      }
      int r = l + 1;
      int s = r < size && hi[heap[r]] < hi[heap[l]] ? r : l;
      if (hi[heap[s]] >= hi[last]) {
        break;
      }
      heap[c] = heap[s];
      c = s;
    }
    if (size > 0) {
      heap[c] = last;
    }
    return size;
  }

  /**
   * Explains a bound by the bounds of the variables, as the propagation reads only them, and the
   * holes the bound skipped. A bound of the sum cites only the side of the variables' bounds it
   * needs when the smallest (largest) sum of distinct values from that side alone reaches it. A
   * bound of a variable takes the Hall set reason of the alldifferent instead when that is shorter.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != AlldiffSum.class || trail.kind(entry) == AtomicTrail.NE) {
      return false;
    }
    IntVar y = trail.variable(entry);
    boolean lower = trail.kind(entry) == AtomicTrail.GE;
    int mark = out.size();
    if (y == sum && !inList(y)) {
      if (lower ? relation == GE : relation == LE) {
        return false;
      }
      // sum >= smallest sum of distinct values, or sum <= the largest one
      long a = trail.value(entry);
      if (!sumReaches(trail, entry, lower, a, true)) {
        return false;
      }
      boolean oneSide = sumReaches(trail, entry, lower, a, false);
      for (IntVar x : list) {
        if (lower || !oneSide) {
          trail.addLowerBound(x, entry, out);
        }
        if (!lower || !oneSide) {
          trail.addUpperBound(x, entry, out);
        }
      }
      trail.addSkippedHoles(entry, lower ? Integer.MIN_VALUE : Integer.MAX_VALUE, out);
      out.sortUnique(mark);
      return true;
    }
    for (IntVar x : list) {
      trail.addLowerBound(x, entry, out);
      trail.addUpperBound(x, entry, out);
    }
    // a maximum is lowered by the smallest sum against the maximum of sum, a minimum raised by the
    // largest sum against the minimum of sum
    if (lower) {
      trail.addLowerBound(sum, entry, out);
    } else {
      trail.addUpperBound(sum, entry, out);
    }
    trail.addSkippedHoles(entry, lower ? Integer.MIN_VALUE : Integer.MAX_VALUE, out);
    out.sortUnique(mark);
    EntryList hallReason = new EntryList();
    if (AlldiffExplanation.explain(trail, entry, list, new IntervalDomain(), hallReason)
        && hallReason.size() < out.size() - mark) {
      out.truncate(mark);
      for (int k = 0; k < hallReason.size(); k++) {
        out.add(hallReason.get(k));
      }
    }
    return true;
  }

  /**
   * Explains a failure by the bounds of the variables and of sum, or by a Hall set of the
   * alldifferent when it fails alone.
   */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != AlldiffSum.class) {
      return false;
    }
    if (AlldiffExplanation.explainFailure(trail, list, new IntervalDomain(), out)) {
      return true;
    }
    int now = trail.size();
    for (IntVar x : list) {
      trail.addLowerBound(x, now, out);
      trail.addUpperBound(x, now, out);
    }
    trail.addLowerBound(sum, now, out);
    trail.addUpperBound(sum, now, out);
    return true;
  }

  private boolean inList(IntVar y) {
    for (IntVar x : list) {
      if (x == y) {
        return true;
      }
    }
    return false;
  }

  /**
   * Whether the smallest sum of distinct values (lower) or the largest one reaches a, with the
   * bounds of the variables just before the entry; with both false, the bounds of the other side
   * are left at their initial values.
   */
  private boolean sumReaches(AtomicTrail trail, int entry, boolean lower, long a, boolean both) {
    int n = list.length;
    long[] from = new long[n];
    long[] to = new long[n];
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      long min = trail.minBefore(x, entry);
      long max = trail.maxBefore(x, entry);
      if (!both) {
        IntDomain root = trail.rootDomain(x);
        if (lower) {
          max = root.max();
        } else {
          min = root.min();
        }
      }
      from[i] = lower ? min : -max;
      to[i] = lower ? max : -min;
    }
    long smallest = smallestSum(from, to);
    return smallest != Long.MAX_VALUE && (lower ? smallest >= a : -smallest <= a);
  }

  // the smallest sum of distinct values in [from[i], to[i]], Long.MAX_VALUE when there is none
  static long smallestSum(long[] from, long[] to) {
    int n = from.length;
    Integer[] order = new Integer[n];
    for (int i = 0; i < n; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (i, j) -> Long.compare(from[i], from[j]));
    PriorityQueue<Integer> waiting = new PriorityQueue<>((i, j) -> Long.compare(to[i], to[j]));
    long total = 0;
    long current = Long.MIN_VALUE / 2;
    int next = 0;
    for (int k = 0; k < n; k++) {
      current = Math.max(current + 1, from[order[k]]);
      while (next < n && from[order[next]] <= current) {
        waiting.add(order[next++]);
      }
      int i = waiting.poll();
      if (to[i] < current) {
        return Long.MAX_VALUE;
      }
      total += current;
    }
    return total;
  }

  @Override
  public boolean satisfied() {
    if (!sum.singleton()) {
      return false;
    }
    long s = 0;
    for (int i = 0; i < list.length; i++) {
      if (!list[i].singleton()) {
        return false;
      }
      int v = list[i].value();
      for (int j = 0; j < i; j++) {
        if (list[j].value() == v) {
          return false;
        }
      }
      s += v;
    }
    return switch (relation) {
      case EQ -> s == sum.value();
      case LE -> s <= sum.value();
      default -> s >= sum.value();
    };
  }

  private String relationString() {
    return switch (relation) {
      case EQ -> "==";
      case LE -> "<=";
      default -> ">=";
    };
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : AlldiffSum([");
    appendArrayToString(result, list);
    result.append("], ").append(relationString()).append(", ").append(sum).append(")");
    return result.toString();
  }

  @Override
  public AlldiffSum copy(VarMap map) {
    return new AlldiffSum(map.get(list), relationString(), map.get(sum), hall != null);
  }
}
