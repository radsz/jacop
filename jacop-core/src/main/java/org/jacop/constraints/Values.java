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
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.util.BipartiteGraphMatching;

/**
 * Constraint Values counts number of different values on a list of Variables.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Values extends Constraint implements SatisfiedPresent {

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
  public void consistency(Store store) {

    if (!prepareValueIndex()) {
      consistencyWithHashing(store);
      return;
    }

    do {

      store.propagationHasOccurred = false;

      int minNumberDifferent = minNumberDifferent();
      countSingletons();
      int maxNumberDifferent = maximumMatching(count.max());

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
    if (matchedValue == null) {
      matchedValue = new int[list.length];
      freeVariables = new int[list.length];
      order = new int[list.length];
      for (int i = 0; i < order.length; i++) {
        order[i] = i;
      }
      mins = new int[list.length];
      maxs = new int[list.length];
      singletons = new int[list.length];
    }
    Arrays.fill(matchedValue, NO_VALUE);
    ownStamp = 0;
    visit = 0;
    singletonMark = 0;
    return true;
  }

  /**
   * It returns a lower bound on the number of different values, computed on intervals sorted by
   * their minimum. The order of the previous execution is kept, so insertion sort is usually
   * linear.
   */
  private int minNumberDifferent() {
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
    int minNumberDifferent = 1;
    int minimumMax = maxs[order[0]];
    for (int index : order) {
      if (mins[index] > minimumMax) {
        minNumberDifferent++;
        minimumMax = maxs[index];
      }
      if (maxs[index] < minimumMax) {
        minimumMax = maxs[index];
      }
    }
    return minNumberDifferent;
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

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {

    return grounded()
        && Arrays.stream(list).map(IntVar::value).collect(Collectors.toSet()).size()
            == count.value();
  }
}
