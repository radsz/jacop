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
   * @param values the array of values to count.
   */
  protected AbstractCountValues(AtomicInteger idNum, IntVar[] list, int[] values) {
    this.queueIndex = 1;
    this.numberId = idNum.incrementAndGet();
    this.n = list.length;
    this.list = Arrays.copyOf(list, n);
    this.values = values;

    this.valuesDomain = new IntervalDomain();
    for (int v : values) {
      valuesDomain.unionAdapt(v);
    }
    this.valuesDomainComplement = valuesDomain.complement();
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
    int[] numberMayBe = new int[values.length];
    int[] numberEq = new int[values.length];
    restEq = rest.value();
    for (int i = 0; i < values.length; i++) {
      numberEq[i] = equal[i].value();
    }

    do {

      store.propagationHasOccurred = false;

      restMayBe = 0;
      Arrays.fill(numberMayBe, 0);

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

  private int scanListAndCount(int start, int[] numberEq, int[] numberMayBe) {
    int[] startRef = new int[] {start};
    for (int i = start; i < n; i++) {
      IntVar v = list[i];
      int noValuesInDomain = processVariableValues(v, numberEq, numberMayBe, startRef, i);
      start = startRef[0];

      if (!v.domain.subtract(valuesDomain).isEmpty()) {
        restMayBe++;
      }

      if (noValuesInDomain == values.length) {
        swap(start, i);
        start++;
        restEq++;
      }
      startRef[0] = start;
    }
    return start;
  }

  private int processVariableValues(
      IntVar v, int[] numberEq, int[] numberMayBe, int[] startRef, int i) {
    int noValuesInDomain = 0;
    for (int j = 0; j < values.length; j++) {
      if (v.domain.contains(values[j])) {
        if (v.singleton()) {
          numberEq[j]++;
          swap(startRef[0], i);
          startRef[0]++;
        } else {
          numberMayBe[j]++;
        }
      } else {
        noValuesInDomain++;
      }
    }
    return noValuesInDomain;
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
    if (restMayBe == getCounterRestMin() - this.restEq) {
      for (int j = start; j < n; j++) {
        IntVar v = list[j];
        if (!v.domain.subtract(valuesDomain).isEmpty()) {
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
