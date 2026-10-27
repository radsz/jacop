/*
 * CountValuesExplanation.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of the number of variables of a list equal to each of several values, each number
 * within constant bounds, as {@link CountValuesBounds} propagates it.
 *
 * <p>Every variable is in one class: one of the counted values, or the rest (no counted value).
 * Class k holds between L(k) and U(k) variables (0 and n for the rest), and the classes together
 * hold all n. Just before a trail position, F(k) variables are fixed to class k and E(k) cannot
 * take it, so class k holds at least lo(k) = max(L(k), F(k)) and at most hi(k) = min(U(k), n -
 * E(k)) variables. A conflict is one of
 *
 * <ul>
 *   <li>F(k) &gt; U(k), or n - E(k) &lt; L(k), for one class;
 *   <li>the sum of lo(k) over the classes above n;
 *   <li>the sum of hi(k) over the classes below n.
 * </ul>
 *
 * <p>The reason of a conflict is the atoms of just enough variables fixed to, or excluded from, the
 * classes it counts, taking those whose atoms came first. A variable y loses a class c when
 * assuming y in c gives a conflict (c is full), or when assuming y not in some other class b gives
 * one (y must take b, so it loses every class but b). These are the deductions of the propagator: a
 * counter at its bound, and the bounds every counter gets from the others' bounds.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CountValuesExplanation {

  private static final int NONE = -1;

  private final AtomicTrail trail;
  private final IntVar[] list;
  private final int[] values;
  private final IntDomain valuesDomain;
  private final int[] sortedValues;
  private final int[] indexOfSorted;
  private final int n;

  /** The class of the rest, after the counted values. */
  private final int rest;

  /** The least and largest number of variables in each class. */
  private final int[] low;

  private final int[] high;

  private final int position;

  // the variable whose atom is explained, and the number of its occurrences in the list
  private IntVar y;
  private int occurrences;

  // each position's domain just before the position, and its atoms there
  private final IntDomain[] domain;
  private final int[] geEntry;
  private final int[] leEntry;
  private final int[][] neEntries;

  // per class, over the positions not holding y: those fixed to it and those that can take it
  private final int[] fixed;
  private final int[] possible;

  // the domain of y and its atoms, when an atom of y is explained
  private IntDomain yDomain;
  private int[] yNe;

  private final EntryList scratch = new EntryList();

  /**
   * Prepares explanations just before a trail position.
   *
   * @param trail the trail
   * @param list the counted variables
   * @param values the counted values, without repetitions
   * @param valuesDomain the counted values as a domain
   * @param sortedValues the counted values in increasing order
   * @param indexOfSorted the position in values of each value of sortedValues
   * @param lb the least number of variables equal to each value
   * @param ub the largest number of variables equal to each value
   * @param position the trail position
   */
  CountValuesExplanation(
      AtomicTrail trail,
      IntVar[] list,
      int[] values,
      IntDomain valuesDomain,
      int[] sortedValues,
      int[] indexOfSorted,
      int[] lb,
      int[] ub,
      int position) {
    this.trail = trail;
    this.list = list;
    this.values = values;
    this.valuesDomain = valuesDomain;
    this.sortedValues = sortedValues;
    this.indexOfSorted = indexOfSorted;
    this.n = list.length;
    this.rest = values.length;
    this.low = Arrays.copyOf(lb, rest + 1);
    this.high = Arrays.copyOf(ub, rest + 1);
    high[rest] = n;
    this.position = position;
    this.domain = new IntDomain[n];
    this.geEntry = new int[n];
    this.leEntry = new int[n];
    this.neEntries = new int[n][];
    this.fixed = new int[rest + 1];
    this.possible = new int[rest + 1];
  }

  /**
   * Adds to {@code out} the reason of an entry of a counted variable.
   *
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when there is no reason of this kind
   */
  boolean explain(int entry, EntryList out) {
    y = trail.variable(entry);
    for (IntVar x : list) {
      if (x == y) {
        occurrences++;
      }
    }
    if (occurrences == 0) {
      return false;
    }
    snapshot();
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    int mark = out.size();
    // values beyond the bounds y had were removed by those bounds' entries, and the holes within
    // them by their own entries
    int min = trail.minBefore(y, entry);
    if (lo < min) {
      trail.addLowerBound(y, entry, out);
      lo = min;
    }
    int max = trail.maxBefore(y, entry);
    if (hi > max) {
      trail.addUpperBound(y, entry, out);
      hi = max;
    }
    if (lo > hi) {
      return true;
    }
    for (int e : yNe) {
      int v = trail.value(e);
      if (lo <= v && v <= hi) {
        out.add(e);
      }
    }
    IntDomain removed = yDomain.intersect(lo, hi);
    if (removed.isEmpty()) {
      return true;
    }
    // the classes the atom takes from y
    boolean[] lost = new boolean[rest + 1];
    lost[rest] = !valuesDomain.contains(removed);
    for (int k = 0; k < rest; k++) {
      lost[k] = removed.contains(values[k]);
    }

    // y must take another class, which takes every lost one from it
    EntryList best = null;
    for (int b = 0; b <= rest; b++) {
      if (!lost[b] && canTake(yDomain, b)) {
        EntryList candidate = new EntryList();
        if (conflict(NONE, b, candidate) && (best == null || candidate.size() < best.size())) {
          best = candidate;
        }
      }
    }
    // every lost class is full
    EntryList full = new EntryList();
    for (int c = 0; c <= rest && full != null; c++) {
      if (lost[c] && !conflict(c, NONE, full)) {
        full = null;
      }
    }
    if (full != null && (best == null || full.size() < best.size())) {
      best = full;
    }
    if (best == null) {
      out.truncate(mark);
      return false;
    }
    for (int k = 0; k < best.size(); k++) {
      out.add(best.get(k));
    }
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure.
   *
   * @param out where the reason entries are added
   * @return false when the counts and the bounds do not conflict
   */
  boolean explainFailure(EntryList out) {
    snapshot();
    return conflict(NONE, NONE, out);
  }

  /** Reads every position's domain just before the position, and counts the classes. */
  private void snapshot() {
    for (int p = 0; p < n; p++) {
      IntVar x = list[p];
      if (x == y) {
        if (yDomain == null) {
          read(p);
          yDomain = domain[p];
          yNe = neEntries[p];
        }
        continue;
      }
      read(p);
      IntDomain d = domain[p];
      if (d.singleton()) {
        int k = classOf(d.value());
        fixed[k]++;
        possible[k]++;
        continue;
      }
      if (!d.isIntersecting(valuesDomain)) {
        fixed[rest]++;
        possible[rest]++;
        continue;
      }
      if (!valuesDomain.contains(d)) {
        possible[rest]++;
      }
      if (d.getSize() < rest) {
        for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
          int k = classOf(e.nextElement());
          if (k != rest) {
            possible[k]++;
          }
        }
      } else {
        for (int k = 0; k < rest; k++) {
          if (d.contains(values[k])) {
            possible[k]++;
          }
        }
      }
    }
  }

  /** Reads the domain of the variable at a position, and its atoms, just before the position. */
  private void read(int p) {
    IntVar x = list[p];
    scratch.clear();
    trail.atomsBefore(x, position, scratch);
    int ge = NONE;
    int le = NONE;
    int numberNe = 0;
    for (int i = 0; i < scratch.size(); i++) {
      int e = scratch.get(i);
      switch (trail.kind(e)) {
        case AtomicTrail.GE -> ge = e;
        case AtomicTrail.LE -> le = e;
        default -> numberNe++;
      }
    }
    int[] ne = new int[numberNe];
    numberNe = 0;
    for (int i = 0; i < scratch.size(); i++) {
      int e = scratch.get(i);
      if (trail.kind(e) == AtomicTrail.NE) {
        ne[numberNe++] = e;
      }
    }
    IntDomain root = trail.rootDomain(x);
    int min = ge == NONE ? root.min() : trail.value(ge);
    int max = le == NONE ? root.max() : trail.value(le);
    IntDomain d = root.intersect(min, max);
    if (ne.length > 0) {
      if (d.domainId() == IntDomain.BOUND_DOMAIN_ID) {
        d = new IntervalDomain(d.min(), d.max());
      }
      for (int e : ne) {
        d.subtractAdapt(trail.value(e));
      }
    }
    domain[p] = d;
    geEntry[p] = ge;
    leEntry[p] = le;
    neEntries[p] = ne;
  }

  private int classOf(int value) {
    int k = Arrays.binarySearch(sortedValues, value);
    return k < 0 ? rest : indexOfSorted[k];
  }

  private boolean canTake(IntDomain d, int k) {
    return k == rest ? !valuesDomain.contains(d) : d.contains(values[k]);
  }

  private boolean fixedTo(IntDomain d, int k) {
    return k == rest ? !d.isIntersecting(valuesDomain) : d.singleton(values[k]);
  }

  // the number of y's occurrences assumed in class k, and assumed out of it
  private int inside(int in, int k) {
    return k == in ? occurrences : 0;
  }

  private int outside(int in, int notIn, int k) {
    return (in != NONE && k != in) || k == notIn ? occurrences : 0;
  }

  private int lo(int in, int k) {
    return Math.max(low[k], fixed[k] + inside(in, k));
  }

  private int hi(int in, int notIn, int k) {
    return Math.min(high[k], possible[k] + occurrences - outside(in, notIn, k));
  }

  /**
   * Adds to {@code out} the reason of a conflict among the classes, assuming y in class in and not
   * in class notIn (either NONE); false when there is none.
   */
  private boolean conflict(int in, int notIn, EntryList out) {
    // the conflict needing the fewest positions: one class over its bound, or a sum
    int bestKind = NONE;
    int bestClass = NONE;
    int bestCost = Integer.MAX_VALUE;
    long sumLo = 0;
    long sumHi = 0;
    for (int k = 0; k <= rest; k++) {
      int f = fixed[k] + inside(in, k);
      if (f > high[k]) {
        int cost = Math.max(0, high[k] + 1 - inside(in, k));
        if (cost < bestCost) {
          bestKind = 0;
          bestClass = k;
          bestCost = cost;
        }
      }
      int can = possible[k] + occurrences - outside(in, notIn, k);
      if (can < low[k]) {
        int cost = Math.max(0, n - low[k] + 1 - outside(in, notIn, k));
        if (cost < bestCost) {
          bestKind = 1;
          bestClass = k;
          bestCost = cost;
        }
      }
      sumLo += lo(in, k);
      sumHi += hi(in, notIn, k);
    }
    if (sumLo > n) {
      int cost = sumCost(in, notIn, true, sumLo - n - 1, null);
      if (cost < bestCost) {
        bestKind = 2;
        bestCost = cost;
      }
    }
    if (sumHi < n) {
      int cost = sumCost(in, notIn, false, n - 1 - sumHi, null);
      if (cost < bestCost) {
        bestKind = 3;
        bestCost = cost;
      }
    }
    switch (bestKind) {
      case 0 -> addFixed(bestClass, bestCost, out);
      case 1 -> addExcluded(bestClass, bestCost, out);
      case 2 -> sumCost(in, notIn, true, sumLo - n - 1, out);
      case 3 -> sumCost(in, notIn, false, n - 1 - sumHi, out);
      default -> {
        return false;
      }
    }
    return true;
  }

  /**
   * Returns the number of positions a sum conflict needs, and adds their reasons to {@code out}
   * unless it is null: per class, the positions fixed to it (for the sum of lo) or excluded from it
   * (for the sum of hi) that make its bound, leaving out those the slack allows.
   */
  private int sumCost(int in, int notIn, boolean lower, long slack, EntryList out) {
    int cost = 0;
    for (int k = 0; k <= rest; k++) {
      int all;
      int reducible;
      if (lower) {
        all = fixed[k];
        reducible = lo(in, k) - Math.max(low[k], inside(in, k));
      } else {
        all = n - occurrences - possible[k];
        reducible = Math.min(high[k], n - outside(in, notIn, k)) - hi(in, notIn, k);
      }
      int used;
      if (reducible <= slack) {
        slack -= reducible;
        used = 0;
      } else {
        used = (int) (all - slack);
        slack = 0;
      }
      if (used > 0 && out != null) {
        if (lower) {
          addFixed(k, used, out);
        } else {
          addExcluded(k, used, out);
        }
      }
      cost += used;
    }
    return cost;
  }

  /** Adds the reasons of count positions fixed to class k, taking those whose atoms came first. */
  private void addFixed(int k, int count, EntryList out) {
    choose(k, count, true, out);
  }

  /** Adds the reasons of count positions excluded from class k, the earliest first. */
  private void addExcluded(int k, int count, EntryList out) {
    choose(k, count, false, out);
  }

  private void choose(int k, int count, boolean isFixed, EntryList out) {
    if (count <= 0) {
      return;
    }
    int[] candidates = new int[n];
    long[] keyed = new long[n];
    int number = 0;
    for (int p = 0; p < n; p++) {
      if (list[p] == y) {
        continue;
      }
      IntDomain d = domain[p];
      if (isFixed ? fixedTo(d, k) : !canTake(d, k)) {
        candidates[number] = p;
        scratch.clear();
        if (isFixed) {
          addFixedReason(p, k, scratch);
        } else {
          addExcludedReason(p, k, scratch);
        }
        int latest = -1;
        for (int i = 0; i < scratch.size(); i++) {
          latest = Math.max(latest, scratch.get(i));
        }
        keyed[number] = ((long) (latest + 1) << 32) | number;
        number++;
      }
    }
    if (number > count) {
      Arrays.sort(keyed, 0, number);
    }
    for (int i = 0; i < Math.min(count, number); i++) {
      int p = candidates[(int) keyed[i]];
      if (isFixed) {
        addFixedReason(p, k, out);
      } else {
        addExcludedReason(p, k, out);
      }
    }
  }

  /** Adds why the variable at p is in class k: the atoms that leave it no other class. */
  private void addFixedReason(int p, int k, EntryList out) {
    if (k != rest) {
      addAll(p, out);
      return;
    }
    // no counted value
    IntDomain root = trail.rootDomain(list[p]);
    for (int v : values) {
      if (root.contains(v)) {
        addExclusion(p, v, out);
      }
    }
  }

  /** Adds why the variable at p cannot take class k. */
  private void addExcludedReason(int p, int k, EntryList out) {
    if (k != rest) {
      addExclusion(p, values[k], out);
      return;
    }
    // every value left is counted: the bounds that cut off other values, and the holes of others
    IntDomain d = domain[p];
    IntDomain root = trail.rootDomain(list[p]);
    if (geEntry[p] != NONE && !valuesDomain.contains(root.intersect(root.min(), d.min() - 1))) {
      out.add(geEntry[p]);
    }
    if (leEntry[p] != NONE && !valuesDomain.contains(root.intersect(d.max() + 1, root.max()))) {
      out.add(leEntry[p]);
    }
    for (int e : neEntries[p]) {
      if (!valuesDomain.contains(trail.value(e))) {
        out.add(e);
      }
    }
  }

  /** Adds why the variable at p does not take v. */
  private void addExclusion(int p, int v, EntryList out) {
    if (!trail.rootDomain(list[p]).contains(v)) {
      return;
    }
    if (geEntry[p] != NONE && v < trail.value(geEntry[p])) {
      out.add(geEntry[p]);
      return;
    }
    if (leEntry[p] != NONE && v > trail.value(leEntry[p])) {
      out.add(leEntry[p]);
      return;
    }
    for (int e : neEntries[p]) {
      if (trail.value(e) == v) {
        out.add(e);
        return;
      }
    }
  }

  private void addAll(int p, EntryList out) {
    if (geEntry[p] != NONE) {
      out.add(geEntry[p]);
    }
    if (leEntry[p] != NONE) {
      out.add(leEntry[p]);
    }
    for (int e : neEntries[p]) {
      out.add(e);
    }
  }
}
