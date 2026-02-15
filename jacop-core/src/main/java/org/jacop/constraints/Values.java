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

  /**
   * It constructs Values constraint.
   *
   * @param list list of variables for which different values are being counted.
   * @param count specifies the number of different values in the list.
   */
  public Values(IntVar[] list, IntVar count) {

    checkInputForNullness(new String[] {"list", "count"}, new Object[][] {list, {count}});

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
    this(list.toArray(new IntVar[0]), count);
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      Arrays.sort(list, minFdv);

      if (DEBUG) {
        log.debug("Sorted : \n{}", this);
      }

      ValuesConsistencyState state = buildAdjAndCounts();

      logStateIfDebug(state);

      count.domain.in(store.level, count, state.minNumberDifferent, state.maxNumberDifferent);

      applyCountPruning(store, state);

    } while (store.propagationHasOccurred);
  }

  private void logStateIfDebug(ValuesConsistencyState state) {
    if (DEBUG) {
      log.debug("Minimum number of different values = {}", state.minNumberDifferent);
      log.debug("Maximum number of different values = {}", state.maxNumberDifferent);
      log.debug(
          "Number singleton values = {} Values = {}", state.numberSingleton, state.singletonValues);
    }
  }

  private static class ValuesConsistencyState {
    int minNumberDifferent;
    int maxNumberDifferent;
    int numberSingleton;
    IntDomain singletonValues;
  }

  private ValuesConsistencyState buildAdjAndCounts() {
    ValuesConsistencyState state = new ValuesConsistencyState();
    state.minNumberDifferent = 1;
    int minimumMax = list[0].max();
    int[][] adj = new int[list.length + 1][];
    adj[0] = new int[0];
    Map<Integer, Integer> valueMap = new HashMap<>();
    int valueIndex = 0;
    state.numberSingleton = 0;
    state.singletonValues = new IntervalDomain();

    for (int i = 0; i < list.length; i++) {
      IntVar v = list[i];
      minimumMax = updateStateForVariable(state, v, minimumMax);
      valueIndex = fillAdjRowFromVariable(adj, i + 1, v, valueMap, valueIndex);
    }
    BipartiteGraphMatching matcher = new BipartiteGraphMatching(adj, list.length, valueMap.size());
    state.maxNumberDifferent = matcher.hopcroftKarp();
    return state;
  }

  private int updateStateForVariable(ValuesConsistencyState state, IntVar v, int minimumMax) {
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

  private int fillAdjRowFromVariable(
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

  private void applyCountPruning(Store store, ValuesConsistencyState state) {
    if (count.max() == state.singletonValues.getSize() && state.numberSingleton < list.length) {
      for (IntVar v : list) {
        if (!v.singleton()) {
          v.domain.in(store.level, v, state.singletonValues);
        }
      }
    } else {
      int diffMin = count.min() - state.singletonValues.getSize();
      int diffSingleton = list.length - state.numberSingleton;
      if (diffMin == diffSingleton) {
        for (IntVar v : list) {
          if (!v.singleton()) {
            v.domain.in(store.level, v, state.singletonValues.complement());
          }
        }
      }
    }
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
