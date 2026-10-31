/*
 * Values.java
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
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.util.BipartiteGraphMatching;

/**
 * Constraint Values counts number of different values on a list of Variables.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Values extends Constraint implements SatisfiedPresent, Copyable<Values>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  private static final boolean DEBUG = false;

  /** It specifies a list of variables which are counted. */
  protected final IntVar[] list;

  /** It specifies the idNumber of different values among variables on a given list. */
  protected final IntVar count;

  final Comparator<IntVar> minFdv = Comparator.comparingInt(IntVar::min);

  /** The dense value arrays are used while the values span at most this many integers. */
  private static final int DENSE_LIMIT = 1 << 16;

  private static final int NO_VALUE = Integer.MIN_VALUE;

  /** The variables sorted by their minimum for the lower bound on the number of values. */
  private IntVar[] sorted;

  /** Positions of the variables in the order of their minimum, kept between executions. */
  private int[] order;

  private int[] mins;
  private int[] maxs;

  /** Positions of the variables in decreasing order of their maximum, kept between executions. */
  private int[] orderByMax;

  /** The points of the greedy hitting sets of the intervals, built from the left and the right. */
  private int[] leftPoints;

  private int[] rightPoints;

  /** Tarjan's state over variables (0..n-1) and values (n + value - base). */
  private int[] tarjanIndex;

  private int[] tarjanLow;
  private int[] tarjanStack;
  private int tarjanStackSize;
  private int tarjanCounter;
  private int[] component;
  private boolean[] onStack;

  /** For each component, whether it reaches a value matched to no variable. */
  private boolean[] reachesFreeValue;

  private int numberOfComponents;

  /** Variables that are unmatched in some maximum matching. */
  private boolean[] notVital;

  private int[] removed;

  /** Ranges of values that keep the size of a hitting set, see keepHittingSetSize. */
  private int[] supportedMin;

  private int[] supportedMax;

  private int[] mergedMin;
  private int[] mergedMax;

  /** Variables that are not singletons and cannot take the value of a singleton. */
  private boolean[] disjoint;

  /** The different values of the singleton variables, the first differentSingletons entries. */
  private int[] singletons;

  private int[] cachedSingletons;
  private IntDomain cachedSingletonValues;
  private IntDomain cachedOtherValues;

  /** The value matched to each variable of the list, or NO_VALUE. */
  private int[] matchedValue;

  private int[] freeVariables;

  /** The smallest value covered by the dense value arrays. */
  private int base;

  /** For each value, the variable matched to it, valid when ownerStamp equals ownStamp. */
  private int[] owner;

  private int[] ownerStamp;
  private int ownStamp;
  private int[] visitStamp;
  private int visit;
  private int[] singletonStamp;
  private int singletonMark;
  private int numberSingleton;
  private int differentSingletons;

  /**
   * It constructs Values constraint.
   *
   * @param list list of variables for which different values are being counted.
   * @param count specifies the number of different values in the list.
   */
  public Values(IntVar[] list, IntVar count) {

    checkInputForNullness(new String[] {"list", "count"}, list, new Object[] {count});

    this.queueIndex = 2;

    numberId = idNumber.incrementAndGet();

    this.count = count;
    this.list = Arrays.copyOf(list, list.length);

    setScope(Stream.concat(Arrays.stream(list), Stream.of(count)));
  }

  /**
   * It constructs Values constraint.
   *
   * @param list list of variables for which different values are being counted.
   * @param count specifies the number of different values in the list.
   */
  public Values(List<? extends IntVar> list, IntVar count) {
    this(list.toArray(IntVar[]::new), count);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == Values.class
        && new ValuesExplanation(trail, list, count).explain(entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == Values.class
        && new ValuesExplanation(trail, list, count).explainFailure(out);
  }

  @Override
  public void consistency(Store store) {

    if (list.length == 0) {
      // an empty list has no values
      count.domain.in(store.level, count, 0, 0);
      return;
    }

    if (!prepareValueIndex()) {
      consistencyWithHashing(store);
      return;
    }

    do {

      store.propagationHasOccurred = false;

      sortIntervals();
      countSingletons();
      int intervalBound = leftGreedy(null);
      int disjointPoints = markDisjoint();
      int minNumberDifferent = Math.max(intervalBound, differentSingletons + disjointPoints);
      // one more than count.max() tells whether count.min() == count.max() is the maximum matching
      int enough = count.min() == count.max() ? count.max() + 1 : count.max();
      int maxNumberDifferent = maximumMatching(enough);

      if (DEBUG) {
        log.debug("Minimum number of different values = {}", minNumberDifferent);
        log.debug("Maximum number of different values = {}", maxNumberDifferent);
        log.debug(
            "Number singleton values = {} Different singleton values = {}",
            numberSingleton,
            differentSingletons);
      }

      if (minNumberDifferent > maxNumberDifferent) {
        // the matching stops at count.max(), so it can be below the lower bound
        throw Store.failException;
      }
      count.domain.in(store.level, count, minNumberDifferent, maxNumberDifferent);

      if (maxNumberDifferent < enough && maxNumberDifferent == count.min()) {
        pruneAtLeast(store);
      }

      if (minNumberDifferent == count.max()) {
        pruneAtMost(store, intervalBound, disjointPoints);
      }

      applyCountPruning(store, null);

    } while (store.propagationHasOccurred);
  }

  /**
   * It makes the dense value arrays cover all values of the variables. The arrays are indexed by
   * value - base, so they are only used while the values span at most DENSE_LIMIT integers.
   *
   * @return true if the dense arrays can be used, false if the values span too many integers.
   */
  private boolean prepareValueIndex() {
    if (list.length == 0) {
      return false;
    }
    long lo = Long.MAX_VALUE;
    long hi = Long.MIN_VALUE;
    for (IntVar v : list) {
      lo = Math.min(lo, v.min());
      hi = Math.max(hi, v.max());
    }
    if (owner != null && lo >= base && hi < (long) base + owner.length) {
      return true;
    }
    if (hi - lo + 1 > DENSE_LIMIT) {
      return false;
    }
    int length = (int) (hi - lo + 1);
    base = (int) lo;
    owner = new int[length];
    ownerStamp = new int[length];
    visitStamp = new int[length];
    singletonStamp = new int[length];
    tarjanIndex = null;
    if (matchedValue == null) {
      matchedValue = new int[list.length];
      freeVariables = new int[list.length];
      order = new int[list.length];
      for (int i = 0; i < order.length; i++) {
        order[i] = i;
      }
      mins = new int[list.length];
      maxs = new int[list.length];
      orderByMax = Arrays.copyOf(order, order.length);
      leftPoints = new int[list.length];
      rightPoints = new int[list.length];
      notVital = new boolean[list.length];
      disjoint = new boolean[list.length];
      singletons = new int[list.length];
    }
    Arrays.fill(matchedValue, NO_VALUE);
    ownStamp = 0;
    visit = 0;
    singletonMark = 0;
    return true;
  }

  /**
   * It sorts the variables by the minimum of their intervals. The order of the previous execution
   * is kept, so insertion sort is usually linear.
   */
  private void sortIntervals() {
    for (int i = 0; i < list.length; i++) {
      mins[i] = list[i].min();
      maxs[i] = list[i].max();
    }
    for (int k = 1; k < order.length; k++) {
      int index = order[k];
      int key = mins[index];
      int j = k - 1;
      while (j >= 0 && mins[order[j]] > key) {
        order[j + 1] = order[j];
        j--;
      }
      order[j + 1] = index;
    }
  }

  /** It sorts the variables by the maximum of their intervals, needed only for pruning. */
  private void sortByMax() {
    for (int k = 1; k < orderByMax.length; k++) {
      int index = orderByMax[k];
      int key = maxs[index];
      int j = k - 1;
      while (j >= 0 && maxs[orderByMax[j]] < key) {
        orderByMax[j + 1] = orderByMax[j];
        j--;
      }
      orderByMax[j + 1] = index;
    }
  }

  /**
   * It computes a minimum hitting set of the intervals of the selected variables, greedily from the
   * left: the intervals are split into groups sharing a value, and the smallest maximum of each
   * group is a point. The points are stored in leftPoints in increasing order.
   *
   * @param selected the variables whose intervals are hit, or null for all variables.
   * @return the number of points, the size of a minimum hitting set.
   */
  private int leftGreedy(boolean[] selected) {
    int points = 0;
    boolean open = false;
    int minimumMax = 0;
    for (int index : order) {
      if (selected != null && !selected[index]) {
        continue;
      }
      if (!open) {
        open = true;
        minimumMax = maxs[index];
      } else if (mins[index] > minimumMax) {
        leftPoints[points++] = minimumMax;
        minimumMax = maxs[index];
      } else if (maxs[index] < minimumMax) {
        minimumMax = maxs[index];
      }
    }
    if (open) {
      leftPoints[points++] = minimumMax;
    }
    return points;
  }

  /**
   * It computes the minimum hitting set of the same intervals greedily from the right, with the
   * largest minimum of each group as a point. The points are stored in rightPoints in increasing
   * order.
   *
   * @param selected the variables whose intervals are hit, or null for all variables.
   * @param numberOfPoints the size of the minimum hitting set found by leftGreedy.
   */
  private void rightGreedy(boolean[] selected, int numberOfPoints) {
    int point = numberOfPoints;
    boolean open = false;
    int maximumMin = 0;
    for (int index : orderByMax) {
      if (selected != null && !selected[index]) {
        continue;
      }
      if (!open) {
        open = true;
        maximumMin = mins[index];
      } else if (maxs[index] < maximumMin) {
        rightPoints[--point] = maximumMin;
        maximumMin = mins[index];
      } else if (mins[index] > maximumMin) {
        maximumMin = mins[index];
      }
    }
    if (open) {
      rightPoints[--point] = maximumMin;
    }
    assert point == 0 : "both greedy hitting sets have the same size";
  }

  /**
   * It returns the values v such that the intervals, with one of them reduced to v, still have a
   * hitting set of the same size. The intervals that contain v are hit by v, and the intervals
   * entirely below and entirely above v are hit independently, by as many points as the greedy
   * hitting sets built from the left and from the right have below and above v. So v is kept when 1
   * + (left points below v) + (right points above v) is at most the size of the hitting set.
   *
   * @param numberOfPoints the size of the minimum hitting set, with leftPoints and rightPoints set.
   * @return the number of ranges of values that keep the size of the hitting set, stored in
   *     supportedMin and supportedMax in increasing order.
   */
  private int keepHittingSetSize(int numberOfPoints) {
    if (supportedMin == null || supportedMin.length < 2 * numberOfPoints + 1) {
      supportedMin = new int[2 * numberOfPoints + 1];
      supportedMax = new int[2 * numberOfPoints + 1];
    }
    int ranges = 0;
    // below counts the left points smaller than v, above the right points larger than v
    int below = 0;
    int above = numberOfPoints;
    int left = 0;
    int right = 0;
    long from = Long.MIN_VALUE;
    while (true) {
      // the next position where below or above changes
      long nextLeft = left < numberOfPoints ? (long) leftPoints[left] + 1 : Long.MAX_VALUE;
      long nextRight = right < numberOfPoints ? rightPoints[right] : Long.MAX_VALUE;
      long next = Math.min(nextLeft, nextRight);
      if (below + above < numberOfPoints && from <= next - 1) {
        int rangeMin = (int) Math.max(from, IntDomain.MIN_INT);
        if (ranges > 0 && supportedMax[ranges - 1] == rangeMin - 1) {
          ranges--;
        } else {
          supportedMin[ranges] = rangeMin;
        }
        supportedMax[ranges++] = (int) Math.min(next - 1, IntDomain.MAX_INT);
      }
      if (next == Long.MAX_VALUE) {
        break;
      }
      while (left < numberOfPoints && (long) leftPoints[left] + 1 == next) {
        below++;
        left++;
      }
      while (right < numberOfPoints && rightPoints[right] == next) {
        above--;
        right++;
      }
      from = next;
    }
    return ranges;
  }

  /**
   * It tells whether the interval of a variable lies within one of the supported ranges, so that
   * the ranges cannot prune it.
   */
  private boolean withinOneRange(IntVar v, int ranges) {
    int min = v.min();
    for (int k = 0; k < ranges; k++) {
      if (min <= supportedMax[k]) {
        return supportedMin[k] <= min && v.max() <= supportedMax[k];
      }
    }
    return false;
  }

  /**
   * It adds the values of the singletons to the supported ranges as ranges of one value, keeping
   * the ranges in increasing order.
   *
   * @return the number of ranges.
   */
  private int addSingletonValues(int ranges) {
    Arrays.sort(singletons, 0, differentSingletons);
    int total = ranges + differentSingletons;
    if (mergedMin == null || mergedMin.length < total) {
      mergedMin = new int[total];
      mergedMax = new int[total];
    }
    int r = 0;
    int k = 0;
    int out = 0;
    while (r < ranges || k < differentSingletons) {
      if (k == differentSingletons || (r < ranges && supportedMin[r] <= singletons[k])) {
        mergedMin[out] = supportedMin[r];
        mergedMax[out++] = supportedMax[r++];
      } else {
        mergedMin[out] = singletons[k];
        mergedMax[out++] = singletons[k++];
      }
    }
    int[] swap = supportedMin;
    supportedMin = mergedMin;
    mergedMin = swap;
    swap = supportedMax;
    supportedMax = mergedMax;
    mergedMax = swap;
    return out;
  }

  /**
   * It restricts a variable to the supported ranges, which are in increasing order and may overlap,
   * by removing the gaps between them.
   */
  private void restrictToRanges(Store store, IntVar v, int ranges) {
    if (ranges == 0) {
      throw Store.failException;
    }
    v.domain.in(store.level, v, supportedMin[0], IntDomain.MAX_INT);
    int covered = supportedMax[0];
    for (int k = 1; k < ranges && covered < v.max(); k++) {
      if (supportedMin[k] > covered + 1 && covered + 1 <= v.max()) {
        v.domain.inComplement(store.level, v, covered + 1, supportedMin[k] - 1);
      }
      covered = Math.max(covered, supportedMax[k]);
    }
    if (covered < v.max()) {
      if (v.min() > covered) {
        throw Store.failException;
      }
      v.domain.in(store.level, v, v.min(), covered);
    }
  }

  /**
   * It marks the variables that are not singletons and cannot take a value of a singleton. Each of
   * them adds a value to the values of the singletons.
   *
   * @return the size of a minimum hitting set of the intervals of the marked variables.
   */
  private int markDisjoint() {
    if (differentSingletons == 0) {
      // the bound is then at most the bound on the intervals of all variables
      return 0;
    }
    for (int i = 0; i < list.length; i++) {
      IntDomain d = list[i].domain;
      disjoint[i] = !d.singleton();
      if (!disjoint[i]) {
        continue;
      }
      if (d.getSize() <= differentSingletons) {
        disjoint[i] = !containsSingletonValue(d);
      } else {
        for (int k = 0; k < differentSingletons; k++) {
          if (d.contains(singletons[k])) {
            disjoint[i] = false;
            break;
          }
        }
      }
    }
    return leftGreedy(disjoint);
  }

  private boolean containsSingletonValue(IntDomain d) {
    int max = d.max();
    for (int value = d.min(); ; value = d.nextValue(value)) {
      int end = d.runEnd(value);
      for (int v = value; v <= end; v++) {
        if (singletonStamp[v - base] == singletonMark) {
          return true;
        }
      }
      if (end >= max) {
        return false;
      }
      value = end;
    }
  }

  /**
   * It prunes the values that would need more than count.max() different values. The first lower
   * bound is a minimum hitting set of the intervals of all variables; when it equals count.max(), a
   * value is kept if it keeps the size of the hitting set. The second lower bound is the number of
   * values of the singletons plus a minimum hitting set of the intervals of the variables that
   * cannot take any of them; when it equals count.max(), a variable can take a value of a singleton
   * or a value that keeps the size of the second hitting set.
   *
   * @param store the constraint store.
   * @param intervalBound the first lower bound.
   * @param disjointPoints the size of the second hitting set.
   */
  private void pruneAtMost(Store store, int intervalBound, int disjointPoints) {
    sortByMax();
    if (intervalBound == count.max()) {
      leftGreedy(null);
      rightGreedy(null, intervalBound);
      int ranges = keepHittingSetSize(intervalBound);
      for (IntVar v : list) {
        if (!withinOneRange(v, ranges)) {
          restrictToRanges(store, v, ranges);
        }
      }
    }
    // without disjoint variables this is the pruning of applyCountPruning to the singleton values
    if (disjointPoints > 0 && differentSingletons + disjointPoints == count.max()) {
      leftGreedy(disjoint);
      rightGreedy(disjoint, disjointPoints);
      int ranges = keepHittingSetSize(disjointPoints);
      boolean merged = false;
      for (IntVar v : list) {
        if (!v.singleton() && !withinOneRange(v, ranges)) {
          if (!merged) {
            ranges = addSingletonValues(ranges);
            merged = true;
          }
          restrictToRanges(store, v, ranges);
        }
      }
    }
  }

  /** It counts the singleton variables and the different values they take. */
  private void countSingletons() {
    singletonMark = nextStamp(singletonMark, singletonStamp);
    numberSingleton = 0;
    differentSingletons = 0;
    for (IntVar v : list) {
      if (v.singleton()) {
        numberSingleton++;
        int index = v.value() - base;
        if (singletonStamp[index] != singletonMark) {
          singletonStamp[index] = singletonMark;
          singletons[differentSingletons++] = v.value();
        }
      }
    }
  }

  /**
   * It computes a maximum matching between the variables and their values. The matching found by
   * the previous execution is kept for every variable whose matched value is still in its domain,
   * and only the other variables are matched again with augmenting paths.
   *
   * <p>The search stops once enough variables are matched to reach the largest count still allowed,
   * since a larger matching cannot prune the count any further.
   *
   * @param enough the size of matching that is enough.
   * @return the size of the maximum matching, the largest possible number of different values, or a
   *     number at least as large as enough.
   */
  private int maximumMatching(int enough) {
    ownStamp = nextStamp(ownStamp, ownerStamp);
    int matched = 0;
    int free = 0;
    for (int i = 0; i < list.length; i++) {
      int value = matchedValue[i];
      if (value != NO_VALUE
          && value >= base
          && value - base < owner.length
          && ownerStamp[value - base] != ownStamp
          && list[i].domain.contains(value)) {
        ownerStamp[value - base] = ownStamp;
        owner[value - base] = i;
        matched++;
      } else {
        matchedValue[i] = NO_VALUE;
        freeVariables[free++] = i;
      }
    }
    // values visited by a failed search stay visited: with the matching unchanged they still
    // lead to no free value, so the marks are only cleared after a successful augmentation
    visit = nextStamp(visit, visitStamp);
    for (int k = 0; k < free && matched < enough; k++) {
      if (augment(freeVariables[k])) {
        matched++;
        visit = nextStamp(visit, visitStamp);
      }
    }
    return matched;
  }

  private boolean augment(int i) {
    IntDomain d = list[i].domain;
    int max = d.max();
    for (int value = d.min(); ; value = d.nextValue(value)) {
      int end = d.runEnd(value);
      for (int v = value; v <= end; v++) {
        if (ownerStamp[v - base] != ownStamp) {
          assign(i, v);
          return true;
        }
      }
      value = end;
      if (value >= max) {
        break;
      }
    }
    for (int value = d.min(); ; value = d.nextValue(value)) {
      int end = d.runEnd(value);
      for (int v = value; v <= end; v++) {
        int index = v - base;
        if (visitStamp[index] != visit) {
          visitStamp[index] = visit;
          if (augment(owner[index])) {
            assign(i, v);
            return true;
          }
        }
      }
      value = end;
      if (value >= max) {
        break;
      }
    }
    return false;
  }

  /**
   * It prunes the values that would leave fewer than count.min() different values, when the maximum
   * matching has exactly count.min() edges. A variable that is unmatched in some maximum matching
   * keeps all its values. For a variable that is matched in every maximum matching, a value is kept
   * only when the edge belongs to some maximum matching: the value and the variable are in the same
   * strongly connected component of the matching graph, or the value reaches a value matched to no
   * variable.
   *
   * @param store the constraint store.
   */
  private void pruneAtLeast(Store store) {
    int n = list.length;
    for (int i = 0; i < n; i++) {
      int value = matchedValue[i];
      if (value != NO_VALUE && !list[i].domain.contains(value)) {
        // the domains changed since the matching was computed; the next round prunes
        return;
      }
    }
    markNotVital();
    int nodes = n + owner.length;
    if (tarjanIndex == null || tarjanIndex.length < nodes) {
      tarjanIndex = new int[nodes];
      tarjanLow = new int[nodes];
      tarjanStack = new int[nodes];
      component = new int[nodes];
      onStack = new boolean[nodes];
      reachesFreeValue = new boolean[nodes];
    }
    Arrays.fill(tarjanIndex, 0, nodes, -1);
    tarjanCounter = 0;
    tarjanStackSize = 0;
    numberOfComponents = 0;
    for (int i = 0; i < n; i++) {
      if (matchedValue[i] != NO_VALUE && !notVital[i] && tarjanIndex[i] < 0) {
        strongConnect(i);
      }
    }
    for (int i = 0; i < n; i++) {
      if (matchedValue[i] == NO_VALUE || notVital[i]) {
        continue;
      }
      IntDomain d = list[i].domain;
      int numberRemoved = 0;
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        int node = n + v - base;
        if (v != matchedValue[i]
            && component[node] != component[i]
            && !reachesFreeValue[component[node]]) {
          if (removed == null || removed.length == numberRemoved) {
            removed = Arrays.copyOf(removed == null ? new int[0] : removed, 2 * numberRemoved + 8);
          }
          removed[numberRemoved++] = v;
        }
      }
      for (int k = 0; k < numberRemoved; k++) {
        list[i].domain.inComplement(store.level, list[i], removed[k]);
      }
    }
  }

  /** It marks the variables reachable from an unmatched variable by alternating paths. */
  private void markNotVital() {
    int n = list.length;
    int queueSize = 0;
    for (int i = 0; i < n; i++) {
      notVital[i] = matchedValue[i] == NO_VALUE;
      if (notVital[i]) {
        freeVariables[queueSize++] = i;
      }
    }
    for (int k = 0; k < queueSize; k++) {
      IntDomain d = list[freeVariables[k]].domain;
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int index = e.nextElement() - base;
        if (ownerStamp[index] == ownStamp && !notVital[owner[index]]) {
          notVital[owner[index]] = true;
          freeVariables[queueSize++] = owner[index];
        }
      }
    }
  }

  /**
   * Tarjan's algorithm on the matching graph: a variable points to the values of its domain other
   * than its matched value, and a matched value points to its variable. Components are completed
   * after all components they reach, so whether a component reaches a free value is known from its
   * members and their edges when it is completed.
   */
  private void strongConnect(int node) {
    int n = list.length;
    tarjanIndex[node] = tarjanCounter;
    tarjanLow[node] = tarjanCounter;
    tarjanCounter++;
    tarjanStack[tarjanStackSize++] = node;
    onStack[node] = true;

    if (node < n) {
      IntDomain d = list[node].domain;
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        if (v != matchedValue[node]) {
          follow(node, n + v - base);
        }
      }
    } else {
      int index = node - n;
      if (ownerStamp[index] == ownStamp) {
        follow(node, owner[index]);
      }
    }

    if (tarjanLow[node] == tarjanIndex[node]) {
      int c = numberOfComponents++;
      boolean free = false;
      int member;
      int start = tarjanStackSize;
      do {
        member = tarjanStack[--start];
        onStack[member] = false;
        component[member] = c;
      } while (member != node);
      for (int k = start; k < tarjanStackSize && !free; k++) {
        free = reachesFree(tarjanStack[k], c);
      }
      tarjanStackSize = start;
      reachesFreeValue[c] = free;
    }
  }

  private void follow(int node, int next) {
    if (tarjanIndex[next] < 0) {
      strongConnect(next);
      tarjanLow[node] = Math.min(tarjanLow[node], tarjanLow[next]);
    } else if (onStack[next]) {
      tarjanLow[node] = Math.min(tarjanLow[node], tarjanIndex[next]);
    }
  }

  /** It tells whether a member of a just completed component is or leads to a free value. */
  private boolean reachesFree(int member, int c) {
    int n = list.length;
    if (member >= n) {
      int index = member - n;
      if (ownerStamp[index] != ownStamp) {
        return true;
      }
      int next = owner[index];
      return component[next] != c && reachesFreeValue[component[next]];
    }
    IntDomain d = list[member].domain;
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      int v = e.nextElement();
      if (v != matchedValue[member]) {
        int next = n + v - base;
        if (component[next] != c && reachesFreeValue[component[next]]) {
          return true;
        }
      }
    }
    return false;
  }

  private void assign(int i, int value) {
    ownerStamp[value - base] = ownStamp;
    owner[value - base] = i;
    matchedValue[i] = value;
  }

  /** It returns the next stamp, clearing the stamp array when the stamps wrap around. */
  private static int nextStamp(int stamp, int[] stamps) {
    if (stamp == Integer.MAX_VALUE) {
      Arrays.fill(stamps, 0);
      return 1;
    }
    return stamp + 1;
  }

  /**
   * It returns the values of the singleton variables as a domain. The domain built last time is
   * reused while the values stay the same, which is common along a branch of the search.
   */
  private IntDomain singletonValues() {
    Arrays.sort(singletons, 0, differentSingletons);
    if (cachedSingletons != null
        && Arrays.equals(
            singletons, 0, differentSingletons, cachedSingletons, 0, cachedSingletons.length)) {
      return cachedSingletonValues;
    }
    IntervalDomain values = new IntervalDomain(differentSingletons);
    int k = 0;
    while (k < differentSingletons) {
      int start = singletons[k];
      int end = start;
      while (k + 1 < differentSingletons && singletons[k + 1] == end + 1) {
        end++;
        k++;
      }
      values.unionAdapt(start, end);
      k++;
    }
    cachedSingletons = Arrays.copyOf(singletons, differentSingletons);
    cachedSingletonValues = values;
    cachedOtherValues = null;
    return values;
  }

  private IntDomain otherValues() {
    IntDomain singletonValues = singletonValues();
    if (cachedOtherValues == null) {
      cachedOtherValues = singletonValues.complement();
    }
    return cachedOtherValues;
  }

  /**
   * It prunes the variables that are not singletons when the count forces them to take the values
   * of the singletons, or values different from them.
   *
   * @param store the constraint store.
   * @param hashedSingletons the values of the singletons computed by the hashing path, or null to
   *     take them from the dense arrays.
   */
  private void applyCountPruning(Store store, IntDomain hashedSingletons) {
    if (count.max() == differentSingletons && numberSingleton < list.length) {
      IntDomain singletonValues = hashedSingletons == null ? singletonValues() : hashedSingletons;
      for (IntVar v : list) {
        if (!v.singleton()) {
          v.domain.in(store.level, v, singletonValues);
        }
      }
    } else if (count.min() - differentSingletons == list.length - numberSingleton) {
      IntDomain otherValues =
          hashedSingletons == null ? otherValues() : hashedSingletons.complement();
      for (IntVar v : list) {
        if (!v.singleton()) {
          v.domain.in(store.level, v, otherValues);
        }
      }
    }
  }

  /**
   * It is the consistency function used when the values of the variables span too many integers for
   * the dense value arrays. It builds the value graph with a hash map and matches it from scratch.
   */
  private void consistencyWithHashing(Store store) {

    IntVar[] order = sorted == null ? Arrays.copyOf(list, list.length) : sorted;
    sorted = order;

    do {

      store.propagationHasOccurred = false;

      Arrays.sort(order, minFdv);

      ValuesConsistencyState state = buildAdjAndCounts(order);

      count.domain.in(store.level, count, state.minNumberDifferent, state.maxNumberDifferent);

      numberSingleton = state.numberSingleton;
      differentSingletons = state.singletonValues.getSize();
      applyCountPruning(store, state.singletonValues);

    } while (store.propagationHasOccurred);
  }

  private static class ValuesConsistencyState {
    int minNumberDifferent;
    int maxNumberDifferent;
    int numberSingleton;
    IntDomain singletonValues;
  }

  private static ValuesConsistencyState buildAdjAndCounts(IntVar[] order) {
    ValuesConsistencyState state = new ValuesConsistencyState();
    state.minNumberDifferent = 1;
    int minimumMax = order[0].max();
    int[][] adj = new int[order.length + 1][];
    adj[0] = new int[0];
    Map<Integer, Integer> valueMap = new HashMap<>();
    int valueIndex = 0;
    state.numberSingleton = 0;
    state.singletonValues = new IntervalDomain();

    for (int i = 0; i < order.length; i++) {
      IntVar v = order[i];
      minimumMax = updateStateForVariable(state, v, minimumMax);
      valueIndex = fillAdjRowFromVariable(adj, i + 1, v, valueMap, valueIndex);
    }
    BipartiteGraphMatching matcher = new BipartiteGraphMatching(adj, order.length, valueMap.size());
    state.maxNumberDifferent = matcher.hopcroftKarp();
    return state;
  }

  private static int updateStateForVariable(
      ValuesConsistencyState state, IntVar v, int minimumMax) {
    if (v.singleton()) {
      state.numberSingleton++;
      state.singletonValues.unionAdapt(v.min(), v.min());
    }
    if (v.min() > minimumMax) {
      state.minNumberDifferent++;
      minimumMax = v.max();
    }
    if (v.max() < minimumMax) {
      minimumMax = v.max();
    }
    return minimumMax;
  }

  private static int fillAdjRowFromVariable(
      int[][] adj, int rowIndex, IntVar v, Map<Integer, Integer> valueMap, int valueIndex) {
    adj[rowIndex] = new int[v.dom().getSize()];
    int j = 0;
    for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int el = e.nextElement();
      Integer elIndex = valueMap.get(el);
      if (elIndex == null) {
        valueMap.put(el, valueIndex);
        adj[rowIndex][j] = valueIndex + 1;
        valueIndex++;
      } else {
        adj[rowIndex][j] = elIndex + 1;
      }
      j++;
    }
    return valueIndex;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : Values([");
    for (int i = 0; i < list.length; i++) {
      if (i < list.length - 1) {
        result.append(list[i]).append(", ");
      } else {
        result.append(list[i]);
      }
    }
    result.append("], ").append(count).append(" )");
    return result.toString();
  }

  // the matching and the values no other variable can take read the domains, so a value removed
  // inside a domain can change the number of different values
  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {

    return grounded()
        && Arrays.stream(list).map(IntVar::value).collect(Collectors.toSet()).size()
            == count.value();
  }

  @Override
  public Values copy(VarMap map) {
    return new Values(map.get(list), map.get(count));
  }
}
