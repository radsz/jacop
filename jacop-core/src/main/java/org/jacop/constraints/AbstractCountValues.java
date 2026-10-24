/*
 * AbstractCountValues.java
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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * Abstract base for CountValues and CountValuesBounds constraints. Provides shared fields (list,
 * values, valuesDomain, position, equal[], rest), impose, swap, and default pruning event.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractCountValues extends Constraint implements SatisfiedPresent {

  /** The list of variables which are checked and counted if equal to specified value. */
  protected final IntVar[] list;

  /** The values to which variables are compared. */
  protected final int[] values;

  /** Domain consisting of all counted values. */
  final IntDomain valuesDomain;

  /** Complement of valuesDomain. */
  final IntDomain valuesDomainComplement;

  /** Length of the list. */
  final int n;

  /** The counted values in increasing order. */
  private final int[] sortedValues;

  /** True when the counted values form one interval, so a value's sorted position is computed. */
  private final boolean contiguous;

  /** The position in values of each value of sortedValues. */
  private final int[] indexOfSorted;

  /** The number of variables equal to each value, reused by consistency. */
  private final int[] numberEq;

  /** The number of undecided variables that can take each value, reused by consistency. */
  private final int[] numberMayBe;

  /**
   * Differences between consecutive sorted values of the number of undecided variables that can
   * take them; a run of counted values inside one interval of a domain costs two updates.
   */
  private final int[] mayBeDifference;

  /** Up to this many counted values within the bounds of a domain are checked one by one. */
  private static final int SMALL_RANGE = 64;

  /** Tracks the first position of undecided variables. */
  protected TimeStamp<Integer> position;

  /** Tracks the number of variables equal to each value. */
  @SuppressWarnings("unchecked")
  protected TimeStamp<Integer>[] equal;

  /** Tracks the number of variables not matching any counted value. */
  protected TimeStamp<Integer> rest;

  /**
   * Constructs the common parts of a CountValues constraint.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param list the array of variables to count over.
   * @param values the array of values to count, without repetitions.
   * @throws IllegalArgumentException if a value is repeated.
   */
  protected AbstractCountValues(AtomicInteger idNum, IntVar[] list, int[] values) {
    checkInputForNullness("list", list);
    checkInputForNullness("values", values);
    this.queueIndex = 1;
    this.numberId = idNum.incrementAndGet();
    this.n = list.length;
    this.list = Arrays.copyOf(list, n);
    this.values = values;

    this.valuesDomain = new IntervalDomain();
    for (int v : values) {
      valuesDomain.unionAdapt(v);
    }
    if (valuesDomain.getSize() != values.length) {
      throw new IllegalArgumentException(
          "Constraint "
              + getClass().getSimpleName()
              + " has repeated values "
              + Arrays.toString(values));
    }
    this.valuesDomainComplement = valuesDomain.complement();

    this.sortedValues = values.clone();
    Arrays.sort(sortedValues);
    this.contiguous =
        values.length > 0 && sortedValues[values.length - 1] - sortedValues[0] == values.length - 1;
    this.indexOfSorted = new int[values.length];
    for (int i = 0; i < values.length; i++) {
      indexOfSorted[Arrays.binarySearch(sortedValues, values[i])] = i;
    }
    this.numberEq = new int[values.length];
    this.numberMayBe = new int[values.length];
    this.mayBeDifference = new int[values.length + 1];
  }

  @SuppressWarnings("unchecked")
  @Override
  public void impose(Store store) {

    super.impose(store);

    position = new TimeStamp<>(store, 0);
    equal = new TimeStamp[values.length];
    for (int i = 0; i < values.length; i++) {
      equal[i] = new TimeStamp<>(store, 0);
    }
    rest = new TimeStamp<>(store, 0);
  }

  /**
   * Swaps two elements in the list array.
   *
   * @param i first index.
   * @param j second index.
   */
  protected void swap(int i, int j) {
    if (i != j) {
      IntVar tmp = list[i];
      list[i] = list[j];
      list[j] = tmp;
    }
  }

  /**
   * Updates the counterRest domain to be within [restEq, restEq + restMayBe].
   *
   * @param store the store for propagation.
   * @param restEq the number of variables definitely not matching any counted value.
   * @param restMayBe the number of variables that may not match any counted value.
   */
  protected abstract void updateCounterRest(Store store, int restEq, int restMayBe);

  /**
   * Updates the counter[i] domain to be within [numberEq, numberEq + numberMayBe].
   *
   * @param store the store for propagation.
   * @param i the index of the counter to update.
   * @param numberEq the number of variables definitely equal to values[i].
   * @param numberMayBe the number of variables that may be equal to values[i].
   */
  protected abstract void updateCounter(Store store, int i, int numberEq, int numberMayBe);

  /**
   * Gets the minimum value of counter[i].
   *
   * @param i the index of the counter.
   * @return the minimum value.
   */
  protected abstract int getCounterMin(int i);

  /**
   * Gets the maximum value of counter[i].
   *
   * @param i the index of the counter.
   * @return the maximum value.
   */
  protected abstract int getCounterMax(int i);

  /**
   * Gets the minimum value of counterRest.
   *
   * @return the minimum value.
   */
  protected abstract int getCounterRestMin();

  /**
   * Gets the maximum value of counterRest.
   *
   * @return the maximum value.
   */
  protected abstract int getCounterRestMax();

  /**
   * Gets the length of the extendedCounter array.
   *
   * @return the length of extendedCounter.
   */
  protected abstract int getExtendedCounterLength();

  /**
   * Gets the minimum value of extendedCounter[i].
   *
   * @param i the index.
   * @return the minimum value.
   */
  protected abstract int getExtendedCounterMin(int i);

  /**
   * Gets the maximum value of extendedCounter[i].
   *
   * @param i the index.
   * @return the maximum value.
   */
  protected abstract int getExtendedCounterMax(int i);

  /**
   * Updates extendedCounter[i] domain to be within [newMin, newMax].
   *
   * @param store the store for propagation.
   * @param i the index to update.
   * @param newMin the new minimum value.
   * @param newMax the new maximum value.
   */
  protected abstract void updateExtendedCounter(Store store, int i, int newMin, int newMax);

  /**
   * Assigns a specific value to a variable.
   *
   * @param store the store for propagation.
   * @param v the variable to assign.
   * @param value the value to assign.
   */
  protected abstract void assignValue(Store store, IntVar v, int value);

  /**
   * Counts how many variables in the list are singleton and equal to the given value.
   *
   * @param value the value to count occurrences of.
   * @return the count of variables that are singleton and equal to value.
   */
  protected int countOccurrences(int value) {
    int count = 0;
    for (int j = 0; j < n; j++) {
      if (list[j].singleton(value)) {
        count++;
      }
    }
    return count;
  }

  /**
   * Shared consistency propagation logic for CountValues and CountValuesBounds.
   *
   * @param store the store for propagation.
   */
  private int restMayBe;

  private int restEq;

  @Override
  public void consistency(final Store store) {

    int start = position.value();
    restEq = rest.value();
    for (int i = 0; i < values.length; i++) {
      numberEq[i] = equal[i].value();
    }

    do {

      store.propagationHasOccurred = false;

      restMayBe = 0;

      start = scanListAndCount(start, numberEq, numberMayBe);

      updateCounterRest(store, restEq, restMayBe);

      for (int i = 0; i < values.length; i++) {
        updateCounter(store, i, numberEq[i], numberMayBe[i]);
      }

      updateExtendedCounters(store);

      assignOrPruneByCounter(store, start, numberEq, numberMayBe);

    } while (store.propagationHasOccurred);

    for (int i = 0; i < values.length; i++) {
      equal[i].update(numberEq[i]);
    }
    rest.update(restEq);

    position.update(start);
  }

  /**
   * Counts, for the undecided variables from start on, how many are equal to or may take each value
   * and how many may take a value that is not counted. Variables that become decided (assigned, or
   * without any counted value) are moved before the new start and counted for good.
   */
  private int scanListAndCount(int start, int[] numberEq, int[] numberMayBe) {
    Arrays.fill(mayBeDifference, 0);
    for (int i = start; i < n; i++) {
      IntVar v = list[i];
      if (v.singleton()) {
        int k = sortedPosition(v.value());
        if (k >= 0) {
          numberEq[indexOfSorted[k]]++;
        } else {
          restEq++;
        }
        swap(start, i);
        start++;
        continue;
      }

      int matched = countMayBe(v.domain);
      if (matched == 0) {
        swap(start, i);
        start++;
        restEq++;
      } else if (matched < v.domain.getSize()) {
        restMayBe++;
      }
    }
    int mayBe = 0;
    for (int k = 0; k < sortedValues.length; k++) {
      mayBe += mayBeDifference[k];
      numberMayBe[indexOfSorted[k]] = mayBe;
    }
    return start;
  }

  /**
   * Records in mayBeDifference that the counted values of the domain may be taken, looking at the
   * intervals of the domain, or at either the counted values within the domain bounds or the domain
   * values, whichever are fewer.
   *
   * @return the number of counted values in the domain.
   */
  private int countMayBe(IntDomain domain) {
    if (domain.domainId() == IntDomain.INTERVAL_DOMAIN_ID) {
      // every counted value between the bounds of an interval is in the domain
      IntervalDomain intervals = (IntervalDomain) domain;
      int matched = 0;
      for (int i = 0; i < intervals.size; i++) {
        Interval interval = intervals.intervals[i];
        matched += mayBeRange(lowerBound(interval.min()), upperBound(interval.max()));
      }
      return matched;
    }
    int from = lowerBound(domain.min());
    int to = upperBound(domain.max());
    if (domain.domainId() == IntDomain.BOUND_DOMAIN_ID) {
      return mayBeRange(from, to);
    }
    if (from >= to) {
      return 0;
    }
    int matched = 0;
    if (to - from <= SMALL_RANGE) {
      for (int k = from; k < to; k++) {
        if (domain.contains(sortedValues[k])) {
          matched += mayBeRange(k, k + 1);
        }
      }
      return matched;
    }
    // walk the runs of consecutive domain values that meet the counted values within the bounds
    int last = Math.min(domain.max(), sortedValues[to - 1]);
    int value =
        domain.min() < sortedValues[from] ? domain.nextValue(sortedValues[from] - 1) : domain.min();
    while (value <= last) {
      int end = domain.runEnd(value);
      matched += mayBeRange(lowerBound(value), upperBound(end));
      if (end >= last) {
        break;
      }
      value = domain.nextValue(end);
    }
    return matched;
  }

  /**
   * Records that the sorted values from position from (inclusive) to to (exclusive) may be taken.
   */
  private int mayBeRange(int from, int to) {
    if (from >= to) {
      return 0;
    }
    mayBeDifference[from]++;
    mayBeDifference[to]--;
    return to - from;
  }

  /** Returns the position of value among the sorted values, or a negative number if not counted. */
  private int sortedPosition(int value) {
    if (contiguous) {
      long k = (long) value - sortedValues[0];
      return k >= 0 && k < sortedValues.length ? (int) k : -1;
    }
    return Arrays.binarySearch(sortedValues, value);
  }

  /** Returns the position of the first sorted value that is not smaller than value. */
  private int lowerBound(int value) {
    if (contiguous) {
      return (int) Math.clamp((long) value - sortedValues[0], 0, sortedValues.length);
    }
    int k = Arrays.binarySearch(sortedValues, value);
    return k < 0 ? -k - 1 : k;
  }

  /** Returns the position of the first sorted value that is greater than value. */
  private int upperBound(int value) {
    if (contiguous) {
      return (int) Math.clamp((long) value - sortedValues[0] + 1, 0, sortedValues.length);
    }
    int k = Arrays.binarySearch(sortedValues, value);
    return k < 0 ? -k - 1 : k + 1;
  }

  private void updateExtendedCounters(Store store) {
    int min = 0;
    int max = 0;
    int extendedCounterLength = getExtendedCounterLength();
    for (int i = 0; i < extendedCounterLength; i++) {
      min += getExtendedCounterMin(i);
      max += getExtendedCounterMax(i);
    }
    for (int i = 0; i < extendedCounterLength; i++) {
      updateExtendedCounter(
          store, i, n - max + getExtendedCounterMax(i), n - min + getExtendedCounterMin(i));
    }
  }

  private void assignOrPruneByCounter(Store store, int start, int[] numberEq, int[] numberMayBe) {
    assignOrPruneCounters(store, start, numberEq, numberMayBe);
    assignOrPruneRest(store, start);
  }

  private void assignOrPruneCounters(Store store, int start, int[] numberEq, int[] numberMayBe) {
    for (int i = 0; i < values.length; i++) {
      if (numberMayBe[i] == 0) {
        // no undecided variable can take the value, so there is nothing to assign or prune
        continue;
      }
      if (numberMayBe[i] == getCounterMin(i) - numberEq[i]) {
        assignValuesForCounter(store, start, i);
      } else if (numberEq[i] == getCounterMax(i)) {
        pruneValuesForCounter(store, start, i);
      }
    }
  }

  private void assignValuesForCounter(Store store, int start, int valueIndex) {
    for (int j = start; j < n; j++) {
      IntVar v = list[j];
      if (v.domain.contains(values[valueIndex])) {
        assignValue(store, v, values[valueIndex]);
      }
    }
  }

  private void pruneValuesForCounter(Store store, int start, int valueIndex) {
    for (int j = start; j < n; j++) {
      IntVar v = list[j];
      v.domain.inComplement(store.level, v, values[valueIndex]);
    }
  }

  private void assignOrPruneRest(Store store, int start) {
    if (restMayBe == 0) {
      // every undecided variable takes a counted value, so there is nothing to assign or prune
      return;
    }
    if (restMayBe == getCounterRestMin() - this.restEq) {
      for (int j = start; j < n; j++) {
        IntVar v = list[j];
        if (!valuesDomain.contains(v.domain)) {
          v.domain.in(store.level, v, valuesDomainComplement);
        }
      }
    } else if (this.restEq == getCounterRestMax()) {
      for (int j = start; j < n; j++) {
        IntVar v = list[j];
        v.domain.in(store.level, v, valuesDomain);
      }
    }
  }
}
