/*
 * FloatIntervalDomain.java
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

package org.jacop.floats.core;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.Iterator;
import org.jacop.constraints.Constraint;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Defines interval of numbers which is part of FDV definition which consist of one or several
 * intervals.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class FloatIntervalDomain extends FloatDomain {

  /** An empty domain, so no constant creation of empty domains is required. */
  public static final FloatIntervalDomain emptyDomain = new FloatIntervalDomain(0);

  /** It specifies an empty float domain. */
  public static final FloatDomain EMPTY = emptyDomain;

  /** The values of the domain are encoded as a list of intervals. */
  public FloatInterval[] intervals;

  /** It specifies number of intervals needed to encode the domain. */
  public int size;

  private static final String ASSERT_MIN_NOT_ADDED = "The minimum was not added";
  private static final String ASSERT_MAX_NOT_ADDED = "The maximum was not added";

  /**
   * Clones this domain and installs the clone on the variable, returning the clone for further
   * modification.
   *
   * @param storeLevel the current store level
   * @param v the variable to install the clone on
   * @return the cloned domain
   */
  private FloatIntervalDomain cloneAndInstall(int storeLevel, Var v) {
    FloatIntervalDomain result = this.cloneLight();
    installResultDomain(result, storeLevel, v);
    return result;
  }

  private void installResultDomain(FloatIntervalDomain result, int storeLevel, Var v) {
    result.modelConstraints = modelConstraints;
    result.searchConstraints = searchConstraints;
    result.stamp = storeLevel;
    result.prevDomain = this;
    result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
    result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
    ((FloatVar) v).domain = result;
  }

  /**
   * Copies interval data from the source domain into this domain's intervals array, resizing if
   * needed.
   */
  private void adoptIntervalsFrom(FloatIntervalDomain source) {
    if (source.size <= intervals.length) {
      System.arraycopy(source.intervals, 0, intervals, 0, source.size);
    } else {
      intervals = new FloatInterval[source.size];
      System.arraycopy(source.intervals, 0, intervals, 0, source.size);
    }
    size = source.size;
  }

  /**
   * Applies a computed intersection result to the current domain or installs it as a new domain,
   * then notifies the variable of the change.
   *
   * @param result the intersection result domain
   * @param storeLevel the current store level
   * @param v the variable being updated
   * @param event the domain change event to fire
   */
  private void applyResultAndNotify(FloatIntervalDomain result, int storeLevel, Var v, int event) {
    if (stamp == storeLevel) {
      adoptIntervalsFrom(result);
    } else {
      if (ASSERTS_ENABLED && stamp >= storeLevel) {
        throw new IllegalStateException("Assertion failed");
      }
      installResultDomain(result, storeLevel, v);
    }
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    v.domainHasChanged(event);
  }

  /**
   * Determines the appropriate event for a new-level complement result and notifies the variable.
   *
   * @param result the result domain after complement
   * @param v the variable to notify
   * @param counter the interval index where the change occurred
   * @param isLow true if the change is at the low end of the interval (min was removed)
   */
  private static void notifyComplementEvent(
      FloatIntervalDomain result, Var v, int counter, boolean isLow) {
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    if (result.singleton()) {
      v.domainHasChanged(IntDomain.GROUND);
      return;
    }
    int boundaryIndex = isLow ? 0 : result.size - 1;
    if (counter == boundaryIndex) {
      v.domainHasChanged(IntDomain.BOUND);
    } else {
      v.domainHasChanged(IntDomain.ANY);
    }
  }

  /**
   * Computes the propagation event for a narrowed domain.
   *
   * @param narrowed the new (narrower) domain
   * @return GROUND, BOUND, or ANY
   */
  private int computeEvent(FloatDomain narrowed) {
    if (narrowed.singleton()) {
      return IntDomain.GROUND;
    } else if (narrowed.min() > min() || narrowed.max() < max()) {
      return IntDomain.BOUND;
    }
    return IntDomain.ANY;
  }

  /**
   * Removes a range when the range minimum is at or before the interval start. May shrink or remove
   * intervals from counter onward.
   */
  private void removeRangeFromIntervalsMinAtOrBefore(int counter, double maxValue) {
    if (maxValue < intervals[counter].min()) {
      return;
    }
    if (intervals[counter].max() > maxValue) {
      intervals[counter] = new FloatInterval(next(maxValue), intervals[counter].max());
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      return;
    }
    int maxCurrent = counter;
    while (maxCurrent < size && intervals[maxCurrent].max() <= maxValue) {
      maxCurrent++;
    }
    if (maxCurrent == size) {
      size = counter;
      return;
    }
    if (maxValue >= intervals[maxCurrent].min()) {
      intervals[maxCurrent] = new FloatInterval(next(maxValue), intervals[maxCurrent].max());
    }
    int i = counter;
    for (; maxCurrent < size; i++, maxCurrent++) {
      intervals[i] = intervals[maxCurrent];
    }
    size = i;
  }

  /**
   * Removes a range when the range minimum is after the interval start (splits or removes from
   * counter).
   */
  private void removeRangeFromIntervalsMinAfter(int counter, double minValue, double maxValue) {
    if (maxValue < intervals[counter].max()) {
      if (intervals.length == size + 1) {
        FloatInterval[] newIntervals = new FloatInterval[intervals.length * 2];
        System.arraycopy(intervals, 0, newIntervals, 0, size);
        intervals = newIntervals;
      }
      for (int i = size; i > counter; i--) {
        intervals[i] = intervals[i - 1];
      }
      intervals[counter] = new FloatInterval(intervals[counter].min(), previous(minValue));
      intervals[counter + 1] = new FloatInterval(next(maxValue), intervals[counter + 1].max());
      size++;
      return;
    }
    intervals[counter] = new FloatInterval(intervals[counter].min(), previous(minValue));
    counter++;
    int maxCurrent = counter;
    while (maxCurrent < size && intervals[maxCurrent].max() <= maxValue) {
      maxCurrent++;
    }
    if (maxCurrent == size) {
      size = counter;
      return;
    }
    if (intervals[maxCurrent].min() <= maxValue) {
      intervals[maxCurrent] = new FloatInterval(next(maxValue), intervals[maxCurrent].max());
    }
    int i = counter;
    for (; maxCurrent < size; i++, maxCurrent++) {
      intervals[i] = intervals[maxCurrent];
    }
    size = i;
  }

  /**
   * Removes a range of values starting from the specified counter position.
   *
   * @param counter the starting index of the interval
   * @param minValue the minimum value to remove
   * @param maxValue the maximum value to remove
   */
  private void removeRangeFromIntervals(int counter, double minValue, double maxValue) {
    if (minValue <= intervals[counter].min()) {
      removeRangeFromIntervalsMinAtOrBefore(counter, maxValue);
    } else {
      removeRangeFromIntervalsMinAfter(counter, minValue, maxValue);
    }
  }

  /**
   * Removes a value from the interval at the specified counter position.
   *
   * @param counter the index of the interval containing the value
   * @param value the value to remove
   */
  private void removeValueFromIntervals(int counter, double value) {

    if (intervals[counter].min() == value) {

      if (intervals[counter].max() != value) {

        intervals[counter] = new FloatInterval(next(value), intervals[counter].max());

        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }

      } else {
        // if domain like this 1..3, 5, 7..10, and 5 being removed.

        for (int i = counter; i < size - 1; i++) {
          intervals[i] = intervals[i + 1];
        }

        size--;

        // below size, instead of size-1 as size has been
        // just decreased, e.g. domain like 1..3, 5, 7..9 and 5
        // being removed.

      }
      return;
    }

    if (intervals[counter].max() == value) {

      // domain like this 1..3, 5, 7..10, and 5 being
      // removed taken care of above.

      intervals[counter] = new FloatInterval(intervals[counter].min(), previous(value));

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      return;
    }

    if (size + 1 < intervals.length) {
      for (int i = size; i > counter + 1; i--) {
        intervals[i] = intervals[i - 1];
      }
    } else {
      FloatInterval[] updatedIntervals = new FloatInterval[size + 1];
      System.arraycopy(intervals, 0, updatedIntervals, 0, counter + 1);
      System.arraycopy(intervals, counter, updatedIntervals, counter + 1, size - counter);
      intervals = updatedIntervals;
    }

    double max = intervals[counter].max();

    intervals[counter] = new FloatInterval(intervals[counter].min(), previous(value));
    intervals[counter + 1] = new FloatInterval(next(value), max);

    // One interval has been split, size increased by one.
    size++;

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /**
   * Computes the intersection of this domain with the range [min, max]. Assumes the caller has
   * already verified the range overlaps this domain.
   *
   * @param min the minimum value of the range
   * @param max the maximum value of the range
   * @return a new domain containing only values within [min, max]
   */
  private FloatIntervalDomain computeRangeIntersection(double min, double max) {

    int pointer = 0;

    // pointer is always smaller than size as domains intersect
    while (intervals[pointer].max() < min) {
      pointer++;
    }

    if (intervals[pointer].min() > max) {
      throw failException;
    }

    FloatIntervalDomain result = new FloatIntervalDomain(size + 1);

    if (intervals[pointer].min() >= min) {
      if (intervals[pointer].max() <= max) {
        result.unionAdapt(intervals[pointer]);
      } else {
        result.unionAdapt(new FloatInterval(intervals[pointer].min(), max));
      }
    } else if (intervals[pointer].max() <= max) {
      result.unionAdapt(new FloatInterval(min, intervals[pointer].max()));
    } else {
      result.unionAdapt(new FloatInterval(min, max));
    }

    pointer++;

    while (pointer < size) {
      if (intervals[pointer].max() <= max) {
        result.unionAdapt(intervals[pointer++]);
      } else {
        break;
      }
    }

    if (pointer < size) {
      if (intervals[pointer].min() <= max) {
        result.unionAdapt(new FloatInterval(intervals[pointer].min(), max));
      }
    }

    return result;
  }

  /** Advances pointer1, updates interval1, returns true if loop should break. */
  private boolean computeIntersectionAdvanceP1(
      int[] pointer1, double[] interval1Min, double[] interval1Max) {
    pointer1[0]++;
    if (pointer1[0] < size) {
      interval1Min[0] = intervals[pointer1[0]].min();
      interval1Max[0] = intervals[pointer1[0]].max();
      return false;
    }
    return true;
  }

  /** Advances pointer2, updates interval2, returns true if loop should break. */
  private boolean computeIntersectionAdvanceP2(
      FloatInterval[] inputIntervals,
      int inputSize,
      double shift,
      int[] pointer2,
      double[] interval2Min,
      double[] interval2Max) {
    pointer2[0]++;
    if (pointer2[0] < inputSize) {
      interval2Min[0] = inputIntervals[pointer2[0]].min() + shift;
      interval2Max[0] = inputIntervals[pointer2[0]].max() + shift;
      return false;
    }
    return true;
  }

  /**
   * Performs one step of the intersection loop: advance pointers or add overlapping interval.
   * Updates state in place. Returns true if the loop should break.
   */
  private boolean computeIntersectionStep(
      FloatIntervalDomain result,
      FloatInterval[] inputIntervals,
      int inputSize,
      double shift,
      int[] pointer1,
      int[] pointer2,
      double[] interval1Min,
      double[] interval1Max,
      double[] interval2Min,
      double[] interval2Max) {
    if (interval1Max[0] < interval2Min[0]) {
      return computeIntersectionAdvanceP1(pointer1, interval1Min, interval1Max);
    }
    if (interval2Max[0] < interval1Min[0]) {
      return computeIntersectionAdvanceP2(
          inputIntervals, inputSize, shift, pointer2, interval2Min, interval2Max);
    }
    if (interval1Min[0] <= interval2Min[0]) {
      return computeIntersectionStepInterval1MinLte(
          result,
          inputIntervals,
          inputSize,
          shift,
          pointer1,
          pointer2,
          interval1Min,
          interval1Max,
          interval2Min,
          interval2Max);
    }
    if (interval2Max[0] <= interval1Max[0]) {
      result.unionAdapt(new FloatInterval(interval1Min[0], interval2Max[0]));
      if (interval2Max[0] >= interval1Max[0]) {
        if (computeIntersectionAdvanceP1(pointer1, interval1Min, interval1Max)) {
          return true;
        }
      }
      return computeIntersectionAdvanceP2(
          inputIntervals, inputSize, shift, pointer2, interval2Min, interval2Max);
    }
    result.unionAdapt(intervals[pointer1[0]]);
    return computeIntersectionAdvanceP1(pointer1, interval1Min, interval1Max);
  }

  private boolean computeIntersectionStepInterval1MinLte(
      FloatIntervalDomain result,
      FloatInterval[] inputIntervals,
      int inputSize,
      double shift,
      int[] pointer1,
      int[] pointer2,
      double[] interval1Min,
      double[] interval1Max,
      double[] interval2Min,
      double[] interval2Max) {
    if (interval1Max[0] <= interval2Max[0]) {
      result.unionAdapt(new FloatInterval(interval2Min[0], interval1Max[0]));
      return computeIntersectionAdvanceP1(pointer1, interval1Min, interval1Max);
    }
    result.unionAdapt(
        new FloatInterval(
            inputIntervals[pointer2[0]].min() + shift, inputIntervals[pointer2[0]].max() + shift));
    return computeIntersectionAdvanceP2(
        inputIntervals, inputSize, shift, pointer2, interval2Min, interval2Max);
  }

  private FloatIntervalDomain computeIntersection(
      FloatInterval[] inputIntervals, int inputSize, double shift) {

    int pointer1 = 0;
    int pointer2 = 0;

    // Chance for no event - skip non-intersecting intervals
    while (pointer2 < inputSize
        && inputIntervals[pointer2].max() + shift < intervals[pointer1].min()) {
      pointer2++;
    }

    if (pointer2 == inputSize) {
      throw failException;
    }

    // Traverse within while loop until certain that change will occur
    while (intervals[pointer1].min() >= inputIntervals[pointer2].min() + shift
        && intervals[pointer1].max() <= inputIntervals[pointer2].max() + shift
        && ++pointer1 < size) {

      while (intervals[pointer1].max() > inputIntervals[pointer2].max() + shift
          && ++pointer2 < inputSize) {}

      if (pointer2 == inputSize) {
        break;
      }
    }

    // No change
    if (pointer1 == size) {
      return null;
    }

    FloatIntervalDomain result = new FloatIntervalDomain(this.size);
    int temp = 0;
    // Add all common intervals to result as indicated by progress of the previous loop
    while (temp < pointer1) {
      result.unionAdapt(intervals[temp++]);
    }

    pointer2 = 0;

    double[] interval1Min = new double[] {intervals[pointer1].min()};
    double[] interval1Max = new double[] {intervals[pointer1].max()};
    double[] interval2Min = new double[] {inputIntervals[pointer2].min() + shift};
    double[] interval2Max = new double[] {inputIntervals[pointer2].max() + shift};
    int[] p1 = new int[] {pointer1};
    int[] p2 = new int[] {pointer2};

    while (true) {
      if (computeIntersectionStep(
          result,
          inputIntervals,
          inputSize,
          shift,
          p1,
          p2,
          interval1Min,
          interval1Max,
          interval2Min,
          interval2Max)) {
        break;
      }
    }

    if (result.isEmpty()) {
      throw failException;
    }

    return result;
  }

  /** Empty constructor, does not initialize anything. */
  public FloatIntervalDomain() {
    this(0);
  }

  /**
   * It creates an empty domain, with at least specified number of places in an array list for
   * intervals.
   *
   * @param size defines the initial size of an array storing the intervals.
   */
  public FloatIntervalDomain(int size) {
    intervals = new FloatInterval[size];
    this.size = 0;
    searchConstraints = null;
    searchConstraintsToEvaluate = 0;
    prevDomain = null;
    searchConstraintsCloned = false;
  }

  /**
   * It creates domain with all values between min and max.
   *
   * @param min defines the left bound of a domain.
   * @param max defines the right bound of a domain.
   */
  public FloatIntervalDomain(double min, double max) {

    if (Double.isNaN(min)) {
      min = FloatDomain.MIN_FLOAT;
    }
    if (Double.isNaN(max)) {
      max = FloatDomain.MAX_FLOAT;
    }

    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException(
          String.valueOf("Min value " + min + " can not be greater than max value " + max));
    }

    intervals = new FloatInterval[5];
    searchConstraints = null;
    searchConstraintsToEvaluate = 0;
    prevDomain = null;
    searchConstraintsCloned = false;
    intervals[0] = new FloatInterval(min, max);
    this.size = 1;
  }

  /** It returns an unique identifier of the domain. */
  @Override
  public int domainId() {
    return FLOAT_INTERVAL_DOMAIN_ID;
  }

  /** {@inheritDoc} */
  public FloatDomain previousDomain() {
    return prevDomain;
  }

  /**
   * It adds interval of values to the domain. It adds at the end without checks for the correctness
   * of domain representation.
   */
  @Override
  public void unionAdapt(FloatInterval i) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == intervals.length) {
      FloatInterval[] oldIntervals = intervals;
      intervals = new FloatInterval[oldIntervals.length + 5];
      System.arraycopy(oldIntervals, 0, intervals, 0, size);
    }

    intervals[size++] = i;

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /** Inserts [min, max] at position i (before current interval i) and returns. */
  private void unionAdaptInsertBefore(int i, double min, double max) {
    if (size == intervals.length) {
      FloatInterval[] oldIntervals = intervals;
      intervals = new FloatInterval[intervals.length + 5];
      System.arraycopy(oldIntervals, 0, intervals, 0, size);
    }
    FloatInterval temp = intervals[i];
    intervals[i] = new FloatInterval(min, max);
    int t = size;
    while (t > i) {
      intervals[t] = intervals[t - 1];
      t--;
    }
    intervals[i + 1] = temp;
    size++;
  }

  /** Appends [min, max] at the end of intervals. */
  private void unionAdaptAppendAtEnd(double min, double max) {
    if (size == intervals.length) {
      FloatInterval[] oldIntervals = intervals;
      intervals = new FloatInterval[intervals.length + 5];
      System.arraycopy(oldIntervals, 0, intervals, 0, size);
    }
    intervals[size] = new FloatInterval(min, max);
    size++;
  }

  /** Merges [min, max] with overlapping intervals starting at index i. */
  private void unionAdaptMergeOverlapping(int i, double min, double max) {
    double newMin = min < intervals[i].min() ? min : intervals[i].min();
    int target = i;
    while (target < size && max >= intervals[target].max()) {
      target++;
    }
    double newMax;
    if (target == size) {
      newMax = max;
    } else if (intervals[target].min() > next(max)) {
      newMax = max;
    } else {
      newMax = intervals[target].max();
      target++;
    }
    intervals[i] = new FloatInterval(newMin, newMax);
    while (target < size) {
      intervals[++i] = intervals[target++];
    }
    while (size > i + 1) {
      intervals[--size] = null;
    }
  }

  /** It adds all values between min and max to the domain. */
  @Override
  public void unionAdapt(double min, double max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == 0) {
      intervals = new FloatInterval[1];
      intervals[size++] = new FloatInterval(min, max);
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && !contains(min)) {
        throw new IllegalStateException(String.valueOf(ASSERT_MIN_NOT_ADDED));
      }
      if (ASSERTS_ENABLED && !contains(max)) {
        throw new IllegalStateException(String.valueOf(ASSERT_MAX_NOT_ADDED));
      }
      return;
    }

    int i = 0;
    for (; i < size; i++) {
      if ((next(max) >= intervals[i].min() && max <= next(intervals[i].max()))
          || (next(min) >= intervals[i].min() && min <= next(intervals[i].max()))
          || (min <= intervals[i].min() && intervals[i].max() <= max)) {
        break;
      }
      if (next(max) < intervals[i].min()) {
        unionAdaptInsertBefore(i, min, max);
        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }
        if (ASSERTS_ENABLED && !contains(min)) {
          throw new IllegalStateException(String.valueOf(ASSERT_MIN_NOT_ADDED));
        }
        if (ASSERTS_ENABLED && !contains(max)) {
          throw new IllegalStateException(String.valueOf(ASSERT_MAX_NOT_ADDED));
        }
        return;
      }
    }

    if (i == size) {
      unionAdaptAppendAtEnd(min, max);
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && !contains(min)) {
        throw new IllegalStateException(String.valueOf(ASSERT_MIN_NOT_ADDED));
      }
      if (ASSERTS_ENABLED && !contains(max)) {
        throw new IllegalStateException(String.valueOf(ASSERT_MAX_NOT_ADDED));
      }
      return;
    }

    unionAdaptMergeOverlapping(i, min, max);
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !contains(min)) {
      throw new IllegalStateException(String.valueOf(ASSERT_MIN_NOT_ADDED));
    }
    if (ASSERTS_ENABLED && !contains(max)) {
      throw new IllegalStateException(String.valueOf(ASSERT_MAX_NOT_ADDED));
    }
  }

  @Override
  public void unionAdapt(double value) {
    unionAdapt(value, value);
  }

  @Override
  public int unionAdapt(FloatDomain union) {

    FloatDomain result = union(union);

    if (((FloatIntervalDomain) result).getSizeFloat() == getSizeFloat()) {
      return Domain.NONE;
    } else {
      setDomain(result);
      return IntDomain.ANY;
    }
  }

  /**
   * It adds a value to the domain. It adds at the end without checks for the correctness of domain
   * representation.
   *
   * @param i value to be added
   */
  public void addLastElement(double i) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (next(intervals[size - 1].max()) == i) {
      intervals[size - 1] = new FloatInterval(intervals[size - 1].min(), i);
    } else {
      if (size == intervals.length) {
        FloatInterval[] oldIntervals = intervals;
        intervals = new FloatInterval[oldIntervals.length + 5];
        System.arraycopy(oldIntervals, 0, intervals, 0, size);
      }

      intervals[size] = new FloatInterval(i, i);
      size++;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /**
   * It adds values as specified by the parameter to the domain. The input parameter can not be an
   * empty set.
   */
  @Override
  public void addDom(FloatDomain domain) {

    FloatIntervalDomain d = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == 0) {
      if (intervals == null || intervals.length < d.intervals.length) {
        intervals = new FloatInterval[d.intervals.length];
      }

      System.arraycopy(d.intervals, 0, intervals, 0, d.size);
      size = d.size;

    } else {
      for (int i = 0; i < d.size; i++) {
        // can not use function add(Interval)
        unionAdapt(d.intervals[i].min(), d.intervals[i].max());
      }
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /** Checks if two domains intersect. */
  @Override
  public boolean isIntersecting(FloatDomain domain) {

    if (domain.isEmpty()) {
      return false;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain intervalDomain = (FloatIntervalDomain) domain;
    int size2 = intervalDomain.size;

    if (size == 0 || size2 == 0) {
      return false;
    }

    int p1 = 0;
    int p2 = 0;
    FloatInterval interval1 = intervals[p1];
    FloatInterval interval2 = intervalDomain.intervals[p2];

    while (true) {
      if (interval1.max() < interval2.min()) {
        p1++;
        if (p1 >= size) {
          break;
        }
        interval1 = intervals[p1];
      } else if (interval2.max() < interval1.min()) {
        p2++;
        if (p2 >= size2) {
          break;
        }
        interval2 = intervalDomain.intervals[p2];
      } else {
        return true;
      }
    }

    return false;
  }

  @Override
  public boolean isIntersecting(double min, double max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    int i = 0;
    for (; i < size && intervals[i].max() < min; i++) {}

    return i != size && !(intervals[i].min() > max);
  }

  /** It removes all elements. */
  @Override
  public void clear() {
    size = 0;
  }

  /**
   * It clones the domain object, only data responsible for encoding domain values is cloned. All
   * other fields must be set separately.
   *
   * @return It returns a clone of this domain.
   */
  public FloatIntervalDomain cloneLight() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain cloned = new FloatIntervalDomain(this.intervals.length);

    System.arraycopy(intervals, 0, cloned.intervals, 0, size);

    cloned.size = size;

    return cloned;
  }

  @Override
  public FloatIntervalDomain copy() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain cloned = new FloatIntervalDomain();

    cloned.intervals = new FloatInterval[this.intervals.length];

    System.arraycopy(intervals, 0, cloned.intervals, 0, size);

    cloned.size = size;

    cloned.stamp = stamp;
    cloned.prevDomain = prevDomain;

    cloned.searchConstraints = searchConstraints;
    cloned.searchConstraintsToEvaluate = searchConstraintsToEvaluate;

    cloned.modelConstraints = modelConstraints;
    cloned.modelConstraintsToEvaluate = modelConstraintsToEvaluate;

    cloned.searchConstraintsCloned = searchConstraintsCloned;

    return cloned;
  }

  /**
   * It specifies if the current domain contains the domain given as a parameter. It assumes that
   * input parameter does not represent an empty domain.
   */
  @Override
  public boolean contains(FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (isEmpty()) {
      return domain.isEmpty();
    }

    if (domain.isEmpty()) {
      return true;
    }

    FloatIntervalDomain dom2 = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && dom2.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(dom2.checkInvariants()));
    }

    int max2 = dom2.size;

    int i1 = 0;
    int i2 = 0;

    if (max2 == 0) {
      return true;
    }

    FloatInterval interval1 = intervals[0];
    FloatInterval interval2 = dom2.intervals[0];

    while (true) {

      while (interval2.min() > interval1.max()) {

        i1++;

        if (i1 == size) {
          return false;
        }

        interval1 = intervals[i1];
      }

      if (interval2.min() < interval1.min() || interval2.max() > interval1.max()) {
        return false;
      }

      i2++;

      if (i2 == max2) {
        return true;
      }

      interval2 = dom2.intervals[i2];
    }
  }

  /** It checks if value belongs to the domain. */
  @Override
  public boolean contains(int value) {
    return contains((double) value);
  }

  /** {@inheritDoc} */
  public boolean contains(double value) {
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    for (int m = 0; m < size; m++) {
      FloatInterval i = intervals[m];
      if (i.max() >= value) {
        if (value >= i.min()) {
          return true;
        }
      }
    }

    return false;
  }

  @Override
  public boolean contains(double min, double max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    for (int m = 0; m < size; m++) {
      FloatInterval i = intervals[m];
      if (i.max() >= max) {
        if (min >= i.min()) {
          return true;
        }
      }
    }

    return false;
  }

  /** It creates a complement of a domain. */
  @Override
  public FloatDomain complement() {

    if (size == 0) {
      return new FloatIntervalDomain(FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain result = new FloatIntervalDomain(size + 1);

    if (min() != FloatDomain.MIN_FLOAT) {
      result.unionAdapt(new FloatInterval(FloatDomain.MIN_FLOAT, previous(intervals[0].min())));
    }

    for (int i = 0; i < size - 1; i++) {
      result.unionAdapt(
          new FloatInterval(next(intervals[i].max()), previous(intervals[i + 1].min())));
    }

    if (max() != FloatDomain.MAX_FLOAT) {
      result.unionAdapt(new FloatInterval(next(max()), FloatDomain.MAX_FLOAT));
    }

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    return result;
  }

  /**
   * It returns the next value in the domain after the specified value.
   *
   * @param value the value for which the next value is sought
   * @return the next value in the domain after the given value
   */
  public double nextValue(double value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    for (int m = 0; m < size; m++) {
      FloatInterval i = intervals[m];
      if (i.max() > value) {
        if (value >= previous(i.min())) {
          return next(value);
        } else {
          return i.min();
        }
      }
    }

    return value;
  }

  /** It returns value enumeration of the domain values. */
  @Override
  public ValueEnumeration valueEnumeration() {
    throw new RuntimeException("This does not exist for floats :(");
  }

  /** It returns interval enumeration of the domain values. */
  @Override
  public IntervalEnumeration intervalEnumeration() {
    throw new RuntimeException("This does not exist for floats :(");
  }

  /**
   * It returns interval enumeration of the domain values.
   *
   * @return intervalEnumeration which can be used to enumerate intervals in this domain.
   */
  public FloatIntervalEnumeration floatIntervalEnumeration() {
    return new FloatIntervalDomainIntervalEnumeration(this);
  }

  /** It checks if the domain is equal to the supplied domain. */
  @Override
  public boolean eq(FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain intervalDomain = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && intervalDomain.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(intervalDomain.checkInvariants()));
    }

    boolean equal = true;
    int i = 0;

    if (size == intervalDomain.size) {
      while (equal && i < size) {
        equal = intervals[i].eq(intervalDomain.intervals[i]);
        i++;
      }
    } else {
      equal = false;
    }

    return equal;
  }

  /** It returns the size of the domain. */
  @Override
  public int getSize() {

    throw new RuntimeException("getSize() has no meanning for floats. Not implemented.");
  }

  /**
   * It returns the size of the domain as a floating-point value.
   *
   * @return the size of the domain as a double
   */
  public double getSizeFloat() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    double n = 0;

    for (int i = 0; i < size; i++) {
      n += intervals[i].max() - intervals[i].min();
    }

    return n;
  }

  /** It interesects current domain with the one given as a parameter. */
  @Override
  public FloatDomain intersect(FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.isEmpty()) {
      return emptyDomain;
    }

    FloatIntervalDomain input = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && input.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(input.checkInvariants()));
    }

    FloatIntervalDomain temp;

    if (size > input.size) {
      temp = new FloatIntervalDomain(size);
    } else {
      temp = new FloatIntervalDomain(input.size);
    }

    int pointer1 = 0;
    int pointer2 = 0;

    int size1 = size;
    int size2 = input.size;

    if (size1 == 0 || size2 == 0) {
      return temp;
    }

    int[] p1 = new int[] {pointer1};
    int[] p2 = new int[] {pointer2};
    while (true) {
      FloatInterval i1 = intervals[p1[0]];
      FloatInterval i2 = input.intervals[p2[0]];
      if (intersectTwoDomainsStep(temp, size1, size2, p1, p2, i1, i2)) {
        break;
      }
    }

    if (ASSERTS_ENABLED && temp.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(temp.checkInvariants()));
    }

    return temp;
  }

  /**
   * One step of the two-domain intersection loop. Updates p1 or p2 and adds to temp. Returns true
   * to break.
   */
  private boolean intersectTwoDomainsStep(
      FloatIntervalDomain temp,
      int size1,
      int size2,
      int[] p1,
      int[] p2,
      FloatInterval interval1,
      FloatInterval interval2) {
    if (interval1.max() < interval2.min()) {
      p1[0]++;
      return p1[0] >= size1;
    }
    if (interval2.max() < interval1.min()) {
      p2[0]++;
      return p2[0] >= size2;
    }
    if (interval1.min() <= interval2.min()) {
      if (interval1.max() <= interval2.max()) {
        temp.unionAdapt(interval2.min(), interval1.max());
        p1[0]++;
        return p1[0] >= size1;
      }
      temp.unionAdapt(interval2.min(), interval2.max());
      p2[0]++;
      return p2[0] >= size2;
    }
    if (interval2.max() <= interval1.max()) {
      temp.unionAdapt(interval1.min(), interval2.max());
      p2[0]++;
      return p2[0] >= size2;
    }
    temp.unionAdapt(interval1.min(), interval1.max());
    p1[0]++;
    return p1[0] >= size1;
  }

  /** Result of one intersect loop iteration: new pointer, new interval, whether to break. */
  private static final class IntersectIterResult {
    int pointer;
    FloatInterval interval;
    boolean doBreak;

    IntersectIterResult(int pointer, FloatInterval interval, boolean doBreak) {
      this.pointer = pointer;
      this.interval = interval;
      this.doBreak = doBreak;
    }
  }

  private IntersectIterResult intersectProcessInterval(
      FloatIntervalDomain temp, int pointer1, FloatInterval interval1, double min, double max) {
    if (interval1.max() < min) {
      pointer1++;
      return new IntersectIterResult(
          pointer1, pointer1 < size ? intervals[pointer1] : null, pointer1 >= size);
    }
    if (max < interval1.min()) {
      return new IntersectIterResult(pointer1, interval1, true);
    }
    if (interval1.min() <= min) {
      if (interval1.max() <= max) {
        temp.unionAdapt(new FloatInterval(min, interval1.max()));
        pointer1++;
        return new IntersectIterResult(
            pointer1, pointer1 < size ? intervals[pointer1] : null, pointer1 >= size);
      }
      temp.unionAdapt(new FloatInterval(min, max));
      return new IntersectIterResult(pointer1, interval1, true);
    }
    if (max <= interval1.max()) {
      temp.unionAdapt(new FloatInterval(interval1.min(), max));
      return new IntersectIterResult(pointer1, interval1, true);
    }
    temp.unionAdapt(new FloatInterval(interval1.min(), interval1.max()));
    pointer1++;
    return new IntersectIterResult(
        pointer1, pointer1 < size ? intervals[pointer1] : null, pointer1 >= size);
  }

  /** In intersects current domain with the domain min..max. */
  @Override
  public FloatDomain intersect(double min, double max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain temp = new FloatIntervalDomain(size);

    if (size == 0) {
      return this;
    }

    int pointer1 = 0;
    FloatInterval interval1 = intervals[pointer1];

    while (true) {
      IntersectIterResult r = intersectProcessInterval(temp, pointer1, interval1, min, max);
      pointer1 = r.pointer;
      interval1 = r.interval;
      if (r.doBreak) {
        break;
      }
      if (ASSERTS_ENABLED && interval1 == null) {
        throw new IllegalStateException("Assertion failed");
      }
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && temp.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(temp.checkInvariants()));
    }

    return temp;
  }

  /** It returns true if given domain is empty. */
  @Override
  public boolean isEmpty() {
    return size == 0;
  }

  /** It returns the maximum value in a domain. */
  @Override
  public double max() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && size == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    return intervals[size - 1].max();
  }

  /** It returns the minimum value in a domain. */
  @Override
  public double min() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && size == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    return intervals[0].min();
  }

  /**
   * It removes the counter-th interval from the domain.
   *
   * @param position it specifies the position of the removed interval.
   */
  public void removeInterval(int position) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && position >= size) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && position < 0) {
      throw new IllegalStateException("Assertion failed");
    }

    size--;

    while (position < size) {
      intervals[position] = intervals[position + 1];
      position++;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /** It sets the domain to the specified domain. */
  @Override
  public void setDomain(FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain intervalDomain = (FloatIntervalDomain) domain;

    size = intervalDomain.size;

    intervals = new FloatInterval[intervalDomain.intervals.length];
    System.arraycopy(intervalDomain.intervals, 0, intervals, 0, size);

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /** It sets the domain to all values between min and max. */
  @Override
  public void setDomain(double min, double max) {
    size = 1;
    intervals[0] = new FloatInterval(min, max);
  }

  /** It returns true if given domain has only one element. */
  @Override
  public boolean singleton() {
    return size == 1 && intervals[0].singleton();
  }

  /** It returns true if given domain has only one element equal c. */
  @Override
  public boolean singleton(double c) {
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    return size == 1
        && intervals[0].singleton()
        && intervals[0].min() <= c
        && c <= intervals[0].max();
  }

  private void subtractValueFromInterval(
      FloatIntervalDomain result, int pointer1, FloatInterval interval1, double value) {
    if (interval1.min() != value) {
      double oldMax = interval1.max();
      result.intervals[pointer1] = new FloatInterval(interval1.min(), previous(value));
      if (value != oldMax) {
        result.unionAdapt(next(value), oldMax);
      }
    } else if (interval1.max() != value) {
      result.intervals[pointer1] = new FloatInterval(next(value), interval1.max());
    } else {
      result.removeInterval(pointer1);
    }
  }

  @Override
  public FloatDomain subtract(double value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain result = cloneLight();

    int pointer1 = 0;

    if (size == 0) {
      return result;
    }

    FloatInterval interval1 = intervals[pointer1];

    while (true) {
      if (interval1.max() < value) {
        pointer1++;
        if (pointer1 < size) {
          interval1 = intervals[pointer1];
          continue;
        }
        break;
      }
      if (interval1.min() <= value) {
        subtractValueFromInterval(result, pointer1, interval1, value);
      }
      break;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    return result;
  }

  /**
   * One step of subtract(domain) when currentDomain1.min() >= currentDomain2.min(). Updates i1, i2,
   * minIncluded. Returns true to break.
   */
  private boolean subtractDomainStepFirstMinGte(
      FloatIntervalDomain result,
      FloatIntervalDomain intervalDomain,
      int size,
      int max2,
      int[] i1,
      int[] i2,
      boolean[] minIncluded,
      FloatInterval currentDomain1,
      FloatInterval currentDomain2) {
    if (currentDomain1.max() <= currentDomain2.max()) {
      i1[0]++;
      if (i1[0] == size) {
        return true;
      }
      minIncluded[0] = false;
      return false;
    }
    double oldMax = currentDomain2.max();
    i2[0]++;
    if (i2[0] == max2) {
      result.unionAdapt(new FloatInterval(next(oldMax), currentDomain1.max()));
      i1[0]++;
      if (i1[0] == size) {
        return true;
      }
      minIncluded[0] = false;
      return true;
    }
    FloatInterval nextDomain2 = intervalDomain.intervals[i2[0]];
    if (nextDomain2.min() > currentDomain1.max()) {
      result.unionAdapt(new FloatInterval(next(oldMax), currentDomain1.max()));
      i1[0]++;
      if (i1[0] == size) {
        return true;
      }
      minIncluded[0] = false;
      return false;
    }
    result.unionAdapt(new FloatInterval(next(oldMax), previous(nextDomain2.min())));
    minIncluded[0] = true;
    return false;
  }

  /**
   * One step of subtract(domain) when currentDomain1.min() < currentDomain2.min(). Updates i1, i2,
   * minIncluded. Returns true to break.
   */
  private boolean subtractDomainStepFirstMinLt(
      FloatIntervalDomain result,
      FloatIntervalDomain intervalDomain,
      int size,
      int max2,
      int[] i1,
      int[] i2,
      boolean[] minIncluded,
      FloatInterval currentDomain1,
      FloatInterval currentDomain2) {
    if (currentDomain1.max() <= currentDomain2.max()) {
      if (!minIncluded[0]) {
        if (currentDomain1.max() >= currentDomain2.min()) {
          result.unionAdapt(
              new FloatInterval(currentDomain1.min(), previous(currentDomain2.min())));
        } else {
          result.unionAdapt(new FloatInterval(currentDomain1.min(), currentDomain1.max()));
        }
      }
      i1[0]++;
      if (i1[0] == size) {
        return true;
      }
      minIncluded[0] = false;
      return false;
    }
    if (!minIncluded[0]) {
      result.unionAdapt(new FloatInterval(currentDomain1.min(), previous(currentDomain2.min())));
      minIncluded[0] = true;
    }
    double oldMax = currentDomain2.max();
    i2[0]++;
    if (i2[0] != max2) {
      currentDomain2 = intervalDomain.intervals[i2[0]];
    }
    if (i2[0] == max2 || currentDomain2.min() > currentDomain1.max()) {
      result.unionAdapt(new FloatInterval(next(oldMax), currentDomain1.max()));
      i1[0]++;
      if (i1[0] == size) {
        return true;
      }
      minIncluded[0] = false;
      return i2[0] == max2;
    }
    result.unionAdapt(new FloatInterval(next(oldMax), previous(currentDomain2.min())));
    return false;
  }

  /** It subtracts domain from current domain and returns the result. */
  @Override
  public FloatDomain subtract(FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (isEmpty()) {
      return EMPTY;
    }

    FloatIntervalDomain intervalDomain = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && intervalDomain.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(intervalDomain.checkInvariants()));
    }

    if (intervalDomain.size == 0) {
      return cloneLight();
    }

    FloatIntervalDomain result = new FloatIntervalDomain();

    result.intervals = new FloatInterval[size + 1];

    int[] i1Ref = new int[] {0};
    int[] i2Ref = new int[] {0};
    int i1 = 0;
    int i2 = 0;

    FloatInterval currentDomain1 = intervals[i1];
    FloatInterval currentDomain2 = intervalDomain.intervals[i2];

    boolean[] minIncluded = new boolean[] {false};

    int max2 = intervalDomain.size;

    while (true) {

      if (currentDomain1.max() < currentDomain2.min()) {
        result.unionAdapt(currentDomain1);
        i1Ref[0]++;
        i1 = i1Ref[0];
        if (i1 == size) {
          break;
        }
        currentDomain1 = intervals[i1];
        minIncluded[0] = false;
        continue;
      }

      if (currentDomain2.max() < currentDomain1.min()) {
        i2Ref[0]++;
        i2 = i2Ref[0];
        if (i2 == max2) {
          break;
        }
        currentDomain2 = intervalDomain.intervals[i2];
        continue;
      }

      if (currentDomain1.min() >= currentDomain2.min()) {
        if (subtractDomainStepFirstMinGte(
            result,
            intervalDomain,
            size,
            max2,
            i1Ref,
            i2Ref,
            minIncluded,
            currentDomain1,
            currentDomain2)) {
          break;
        }
      } else {
        if (subtractDomainStepFirstMinLt(
            result,
            intervalDomain,
            size,
            max2,
            i1Ref,
            i2Ref,
            minIncluded,
            currentDomain1,
            currentDomain2)) {
          break;
        }
      }
      i1 = i1Ref[0];
      i2 = i2Ref[0];
      currentDomain1 = intervals[i1];
      currentDomain2 = intervalDomain.intervals[i2];
    }

    while (i1 < size) {
      result.unionAdapt(intervals[i1]);
      i1++;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result;
  }

  /** Result of one subtract(min,max) loop iteration. */
  private static final class SubtractRangeIterResult {
    int i1;
    FloatInterval currentInterval1;
    boolean doBreak;

    SubtractRangeIterResult(int i1, FloatInterval currentInterval1, boolean doBreak) {
      this.i1 = i1;
      this.currentInterval1 = currentInterval1;
      this.doBreak = doBreak;
    }
  }

  private SubtractRangeIterResult subtractRangeProcessInterval(
      FloatIntervalDomain result, int i1, FloatInterval currentInterval1, double min, double max) {
    if (currentInterval1.max() < min) {
      result.unionAdapt(intervals[i1]);
      i1++;
      return new SubtractRangeIterResult(i1, i1 < size ? intervals[i1] : null, i1 >= size);
    }
    if (max < currentInterval1.min()) {
      return new SubtractRangeIterResult(i1, currentInterval1, true);
    }
    if (currentInterval1.min() >= min) {
      if (currentInterval1.max() <= max) {
        i1++;
        return new SubtractRangeIterResult(i1, i1 < size ? intervals[i1] : null, i1 >= size);
      }
      result.unionAdapt(new FloatInterval(next(max), currentInterval1.max()));
      return new SubtractRangeIterResult(i1 + 1, null, true);
    }
    if (currentInterval1.max() <= max) {
      result.unionAdapt(new FloatInterval(currentInterval1.min(), previous(min)));
      i1++;
      return new SubtractRangeIterResult(i1, i1 < size ? intervals[i1] : null, i1 >= size);
    }
    result.unionAdapt(currentInterval1.min(), previous(min));
    result.unionAdapt(next(max), currentInterval1.max());
    return new SubtractRangeIterResult(i1 + 1, null, true);
  }

  /** It subtracts min..max from current domain and returns the result. */
  @Override
  public FloatIntervalDomain subtract(double min, double max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException("Assertion failed");
    }

    if (size == 0) {
      return emptyDomain;
    }

    int i1 = 0;
    FloatInterval currentInterval1 = intervals[i1];
    FloatIntervalDomain result = new FloatIntervalDomain(intervals.length + 1);

    while (true) {
      SubtractRangeIterResult r =
          subtractRangeProcessInterval(result, i1, currentInterval1, min, max);
      i1 = r.i1;
      currentInterval1 = r.currentInterval1;
      if (r.doBreak) {
        break;
      }
    }

    for (int i = i1; i < size; i++) {
      result.unionAdapt(intervals[i]);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    return result;
  }

  private static boolean intervalsOverlapOrAdjacent(FloatInterval a, FloatInterval b) {
    return (FloatDomain.next(a.max()) >= b.min() && a.min() <= b.min())
        || (FloatDomain.next(b.max()) >= a.min() && b.min() <= a.min());
  }

  private void unionDomainAdvanceOverlapping(
      FloatIntervalDomain intervalDomain,
      int max1,
      int max2,
      int[] i1Ref,
      int[] i2Ref,
      FloatInterval[] cur1Ref,
      FloatInterval[] cur2Ref) {
    FloatInterval currentDomain1 = cur1Ref[0];
    FloatInterval currentDomain2 = cur2Ref[0];
    while (intervalsOverlapOrAdjacent(currentDomain1, currentDomain2)) {
      if (currentDomain1.max() <= currentDomain2.max()) {
        i1Ref[0]++;
        if (i1Ref[0] == max1) {
          return;
        }
        cur1Ref[0] = intervals[i1Ref[0]];
        currentDomain1 = cur1Ref[0];
        continue;
      }
      if (currentDomain2.max() < currentDomain1.max()) {
        i2Ref[0]++;
        if (i2Ref[0] == max2) {
          return;
        }
        cur2Ref[0] = intervalDomain.intervals[i2Ref[0]];
        currentDomain2 = cur2Ref[0];
      }
    }
  }

  /**
   * When i1 == max1: advance i2 while currentDomain2 is contained in currentDomain1, then add one
   * interval to result. Updates i2Ref and cur2Ref.
   */
  private void unionDomainFlushI2AndBreak(
      FloatIntervalDomain result,
      FloatIntervalDomain intervalDomain,
      double min,
      int max2,
      int[] i2Ref,
      FloatInterval currentDomain1,
      FloatInterval[] cur2Ref) {
    FloatInterval currentDomain2 = cur2Ref[0];
    while (currentDomain2.max() <= currentDomain1.max()) {
      i2Ref[0]++;
      if (i2Ref[0] == max2) {
        result.unionAdapt(new FloatInterval(min, currentDomain1.max()));
        return;
      }
      currentDomain2 = intervalDomain.intervals[i2Ref[0]];
      cur2Ref[0] = currentDomain2;
    }
    if (currentDomain1.max() <= currentDomain2.max()
        && next(currentDomain1.max()) >= currentDomain2.min()) {
      result.unionAdapt(new FloatInterval(min, currentDomain2.max()));
      i2Ref[0]++;
    } else {
      result.unionAdapt(new FloatInterval(min, currentDomain1.max()));
    }
  }

  /**
   * When i2 == max2: advance i1 while currentDomain1 is contained in currentDomain2, then add one
   * interval to result. Updates i1Ref and cur1Ref.
   */
  private void unionDomainFlushI1AndBreak(
      FloatIntervalDomain result,
      FloatIntervalDomain intervalDomain,
      double min,
      int max1,
      int[] i1Ref,
      FloatInterval currentDomain2,
      FloatInterval[] cur1Ref) {
    FloatInterval currentDomain1 = cur1Ref[0];
    while (currentDomain1.max() <= currentDomain2.max()) {
      i1Ref[0]++;
      if (i1Ref[0] == max1) {
        result.unionAdapt(new FloatInterval(min, currentDomain2.max()));
        return;
      }
      currentDomain1 = intervals[i1Ref[0]];
      cur1Ref[0] = currentDomain1;
    }
    if (currentDomain2.max() <= currentDomain1.max()
        && next(currentDomain2.max()) >= currentDomain1.min()) {
      result.unionAdapt(new FloatInterval(min, currentDomain1.max()));
      i1Ref[0]++;
    } else {
      result.unionAdapt(new FloatInterval(min, currentDomain2.max()));
    }
  }

  /** It computes union of dom1 from dom2 and returns the result. */
  @Override
  public FloatDomain union(FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain intervalDomain = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && intervalDomain.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(intervalDomain.checkInvariants()));
    }

    if (intervalDomain.size == 0) {

      return cloneLight();
    }

    if (size == 0) {

      return intervalDomain.cloneLight();
    }

    FloatIntervalDomain result = new FloatIntervalDomain(size + intervalDomain.size);

    int max1 = size;
    int max2 = intervalDomain.size;
    int[] i1Ref = new int[] {0};
    int[] i2Ref = new int[] {0};
    FloatInterval[] cur1Ref = new FloatInterval[] {intervals[0]};
    FloatInterval[] cur2Ref = new FloatInterval[] {intervalDomain.intervals[0]};

    while (true) {
      FloatInterval currentDomain1 = cur1Ref[0];
      FloatInterval currentDomain2 = cur2Ref[0];
      int i1 = i1Ref[0];
      int i2 = i2Ref[0];

      if (next(currentDomain1.max()) < currentDomain2.min()) {
        result.unionAdapt(new FloatInterval(currentDomain1.min(), currentDomain1.max()));
        i1Ref[0]++;
        if (i1Ref[0] == max1) {
          break;
        }
        cur1Ref[0] = intervals[i1Ref[0]];
        continue;
      }

      if (next(currentDomain2.max()) < currentDomain1.min()) {
        result.unionAdapt(new FloatInterval(currentDomain2.min(), currentDomain2.max()));
        i2Ref[0]++;
        if (i2Ref[0] == max2) {
          break;
        }
        cur2Ref[0] = intervalDomain.intervals[i2Ref[0]];
        continue;
      }

      final double min = Math.min(currentDomain1.min(), currentDomain2.min());
      unionDomainAdvanceOverlapping(intervalDomain, max1, max2, i1Ref, i2Ref, cur1Ref, cur2Ref);
      i1 = i1Ref[0];
      i2 = i2Ref[0];
      currentDomain1 = cur1Ref[0];
      currentDomain2 = cur2Ref[0];

      if (i1 == max1) {
        unionDomainFlushI2AndBreak(
            result, intervalDomain, min, max2, i2Ref, currentDomain1, cur2Ref);
        break;
      }
      if (i2 == max2) {
        unionDomainFlushI1AndBreak(
            result, intervalDomain, min, max1, i1Ref, currentDomain2, cur1Ref);
        break;
      }
      if (currentDomain1.max() < currentDomain2.max()) {
        result.unionAdapt(new FloatInterval(min, currentDomain1.max()));
        i1Ref[0]++;
        if (i1Ref[0] == max1) {
          break;
        }
        cur1Ref[0] = intervals[i1Ref[0]];
      } else {
        result.unionAdapt(new FloatInterval(min, currentDomain2.max()));
        i2Ref[0]++;
        if (i2Ref[0] == max2) {
          break;
        }
        cur2Ref[0] = intervalDomain.intervals[i2Ref[0]];
      }
    }

    int i1 = i1Ref[0];
    int i2 = i2Ref[0];
    if (i1 < max1) {
      for (; i1 < max1; i1++) {
        result.unionAdapt(intervals[i1]);
      }
    }

    if (i2 < max2) {
      for (; i2 < max2; i2++) {
        result.unionAdapt(intervalDomain.intervals[i2]);
      }
    }

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result;
  }

  private int unionMinMaxHandleOverlap(
      FloatIntervalDomain result,
      int i1,
      FloatInterval currentInterval1,
      double tempMin,
      double min,
      double max) {
    if (currentInterval1.max() > max) {
      result.unionAdapt(new FloatInterval(tempMin, currentInterval1.max()));
      return i1 + 1;
    }
    while (currentInterval1.max() <= max) {
      i1++;
      if (i1 == size) {
        result.unionAdapt(new FloatInterval(tempMin, max));
        return i1;
      }
      currentInterval1 = intervals[i1];
    }
    if (next(max) >= currentInterval1.min()) {
      result.unionAdapt(new FloatInterval(tempMin, currentInterval1.max()));
      return i1 + 1;
    }
    result.unionAdapt(new FloatInterval(tempMin, max));
    return i1;
  }

  /** It computes union of current domain and an interval min..max;. */
  @Override
  public FloatDomain union(double min, double max) {

    if (size == 0) {
      return new FloatIntervalDomain(min, max);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain result = new FloatIntervalDomain(size + 1);
    int i1 = 0;
    FloatInterval currentInterval1 = intervals[i1];

    while (true) {
      if (next(currentInterval1.max()) < min) {
        result.unionAdapt(currentInterval1);
        i1++;
        if (i1 == size) {
          result.unionAdapt(new FloatInterval(min, max));
          break;
        }
        currentInterval1 = intervals[i1];
        continue;
      }
      if (next(max) < currentInterval1.min()) {
        result.unionAdapt(new FloatInterval(min, max));
        break;
      }
      double tempMin = currentInterval1.min() < min ? currentInterval1.min() : min;
      i1 = unionMinMaxHandleOverlap(result, i1, currentInterval1, tempMin, min, max);
      break;
    }

    if (i1 < size) {
      for (; i1 < size; i1++) {
        result.unionAdapt(intervals[i1]);
      }
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    return result;
  }

  private int unionValueMergeWithInterval(
      FloatIntervalDomain result, int i1, FloatInterval currentInterval, double value) {
    double tempMin = currentInterval.min() < value ? currentInterval.min() : value;
    double tempMax = currentInterval.max() > value ? currentInterval.max() : value;
    if (i1 + 1 < size && next(tempMax) == intervals[i1 + 1].min()) {
      tempMax = intervals[i1 + 1].max();
      i1++;
    }
    result.unionAdapt(new FloatInterval(tempMin, tempMax));
    return i1 + 1;
  }

  /** It computes union of dom1 and value and returns the result. */
  @Override
  public FloatDomain union(double value) {

    if (size == 0) {
      return new FloatIntervalDomain(value, value);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    FloatIntervalDomain result = new FloatIntervalDomain(size + 1);
    int i1 = 0;
    FloatInterval currentInterval = intervals[i1];

    while (next(currentInterval.max()) < value) {
      result.unionAdapt(currentInterval);
      i1++;
      if (i1 == size) {
        result.unionAdapt(new FloatInterval(value, value));
        return result;
      }
      currentInterval = intervals[i1];
    }

    if (next(value) < currentInterval.min()) {
      result.unionAdapt(new FloatInterval(value, value));
    } else {
      i1 = unionValueMergeWithInterval(result, i1, currentInterval, value);
    }

    if (i1 < size) {
      for (; i1 < size; i1++) {
        result.unionAdapt(intervals[i1]);
      }
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    return result;
  }

  /** It returns string description of the domain (only values in the domain). */
  @Override
  public String toString() {

    StringBuilder s = new StringBuilder();

    if (!singleton()) {
      s.append("{");
      for (int e = 0; e < size; e++) {
        s.append(intervals[e]);
        if (e + 1 < size) {
          s.append(", ");
        }
      }
      s.append("}");
    } else {
      s.append(intervals[0]);
    }

    return s.toString();
  }

  /** It returns string description of the constraints attached to the domain. */
  @Override
  public String toStringConstraints() {

    StringBuilder result = new StringBuilder();

    for (Iterator<Constraint> e = searchConstraints.iterator(); e.hasNext(); ) {
      result.append(e.next().id());
      if (e.hasNext()) {
        result.append(", ");
      }
    }

    return result.toString();
  }

  /** It returns complete string description containing all relevant information. */
  @Override
  public String toStringFull() {

    StringBuilder result = new StringBuilder();

    FloatDomain domain = this;

    do {
      if (!domain.singleton()) {
        result.append("{");

        for (int e = 0; e < size; e++) {
          result.append(intervals[e]);
          if (e + 1 < size) {
            result.append(", ");
          }
        }

        result.append("} ").append("(").append(domain.stamp()).append(") ");
      } else {
        result.append(intervals[0]).append("(").append(domain.stamp()).append(") ");
      }

      result.append("constraints: ");

      for (Constraint searchConstraint : domain.searchConstraints) {
        result.append(searchConstraint);
      }

      FloatIntervalDomain dom = (FloatIntervalDomain) domain;
      domain = dom.prevDomain;

    } while (domain != null);

    return result.toString();
  }

  /**
   * It updates the domain according to the minimum value and stamp value. It informs the variable
   * of a change if it occurred.
   */
  private void notifyInMinMaxChange(Var v, boolean isSingleton) {
    if (isSingleton) {
      v.domainHasChanged(IntDomain.GROUND);
    } else {
      v.domainHasChanged(IntDomain.BOUND);
    }
  }

  @Override
  public void inMin(int storeLevel, Var v, double min) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (min > intervals[size - 1].max()) {
      throw failException;
    }

    if (min <= intervals[0].min()) {
      return;
    }

    if (stamp == storeLevel) {
      int pointer = 0;
      while (intervals[pointer].max() < min) {
        pointer++;
      }
      int i = 0;
      if (intervals[pointer].min() < min) {
        intervals[0] = new FloatInterval(min, intervals[pointer].max());
        pointer++;
        i++;
      }
      for (; pointer < size; i++, pointer++) {
        intervals[i] = intervals[pointer];
      }
      size = i;
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      notifyInMinMaxChange(v, singleton());
    } else {
      if (ASSERTS_ENABLED && stamp >= storeLevel) {
        throw new IllegalStateException("Assertion failed");
      }
      FloatIntervalDomain result = new FloatIntervalDomain(size + 1);
      int pointer = 0;
      while (intervals[pointer].max() < min) {
        pointer++;
      }
      if (intervals[pointer].min() < min) {
        result.unionAdapt(new FloatInterval(min, intervals[pointer++].max()));
      }
      for (; pointer < size; pointer++) {
        result.unionAdapt(intervals[pointer]);
      }
      installResultDomain(result, storeLevel, v);
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }
      notifyInMinMaxChange(v, result.singleton());
    }
  }

  /**
   * It updates the domain according to the maximum value and stamp value. It informs the variable
   * of a change if it occurred.
   */
  @Override
  public void inMax(int storeLevel, Var v, double max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (max < intervals[0].min()) {
      throw failException;
    }

    double currentMax = intervals[size - 1].max();
    if (max >= currentMax) {
      return;
    }

    int pointer = size - 1;

    if (stamp == storeLevel) {
      while (intervals[pointer].min() > max) {
        pointer--;
      }
      if (intervals[pointer].max() > max) {
        intervals[pointer] = new FloatInterval(intervals[pointer].min(), max);
      }
      size = pointer + 1;
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      notifyInMinMaxChange(v, singleton());
    } else {
      if (ASSERTS_ENABLED && stamp >= storeLevel) {
        throw new IllegalStateException("Assertion failed");
      }
      while (intervals[pointer].min() > max) {
        pointer--;
      }
      FloatIntervalDomain result = new FloatIntervalDomain(pointer + 1);
      for (int i = 0; i < pointer; i++) {
        result.unionAdapt(intervals[i]);
      }
      if (intervals[pointer].max() > max) {
        result.unionAdapt(new FloatInterval(intervals[pointer].min(), max));
      } else {
        result.unionAdapt(intervals[pointer]);
      }
      installResultDomain(result, storeLevel, v);
      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      notifyInMinMaxChange(v, result.singleton());
    }
  }

  /**
   * It updates the domain to have values only within the interval min..max. The type of update is
   * decided by the value of stamp. It informs the variable of a change if it occurred.
   */
  @Override
  public void in(int storeLevel, Var v, double min, double max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException(
          String.valueOf("Min value greater than max value " + min + " > " + max));
    }

    if (max < intervals[0].min()) {
      throw failException;
    }

    double currentMax = intervals[size - 1].max();
    if (min > currentMax) {
      throw failException;
    }

    if (min <= intervals[0].min() && max >= currentMax) {
      return;
    }

    FloatIntervalDomain result = computeRangeIntersection(min, max);

    applyResultAndNotify(
        result, storeLevel, v, result.singleton() ? IntDomain.GROUND : IntDomain.BOUND);
  }

  /**
   * It updates the domain to have values only within the domain. The type of update is decided by
   * the value of stamp. It informs the variable of a change if it occurred.
   */
  @Override
  public void in(int storeLevel, Var v, FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && this.stamp > storeLevel) {
      throw new IllegalStateException("Assertion failed");
    }

    FloatIntervalDomain input = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && input.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(input.checkInvariants()));
    }

    if (input.size == 0) {
      throw failException;
    }

    if (ASSERTS_ENABLED && size == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    FloatIntervalDomain result = computeIntersection(input.intervals, input.size, 0.0);

    if (result == null) {
      return;
    }

    applyResultAndNotify(result, storeLevel, v, computeEvent(result));
  }

  /** It returns the number intervals into which this domain is split. */
  @Override
  public int noIntervals() {

    return size;
  }

  /**
   * It specifies the position of the interval which contains specified value.
   *
   * @param value value for which an interval containing it is searched.
   * @return the position of the interval containing the specified value.
   */
  public int intervalNo(double value) {

    for (int i = 0; i < size; i++) {
      if (intervals[i].min() > value) {
      } else if (intervals[i].max() < value) {
      } else {
        return i;
      }
    }

    return -1;
  }

  @Override
  public FloatInterval getInterval(int position) {

    if (ASSERTS_ENABLED && position >= size) {
      throw new IllegalStateException("Assertion failed");
    }

    return intervals[position];
  }

  private void notifyInComplementEvent(
      Var v, boolean minEquals, boolean maxEquals, int originalCounter) {
    if (minEquals && !maxEquals) {
      v.domainHasChanged(originalCounter == 0 ? IntDomain.BOUND : IntDomain.ANY);
    } else if (maxEquals) {
      v.domainHasChanged(originalCounter == size - 1 ? IntDomain.BOUND : IntDomain.ANY);
    } else {
      v.domainHasChanged(IntDomain.ANY);
    }
  }

  /**
   * It updates the domain to not contain the value complement. It informs the variable of a change
   * if it occurred.
   */
  @Override
  public void inComplement(int storeLevel, Var v, double complement) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    int counter = intervalNo(complement);

    if (counter == -1) {
      return;
    }

    if (storeLevel == stamp) {

      boolean wasSingleton = singleton(complement);
      boolean minEquals = intervals[counter].min() == complement;
      boolean maxEquals = intervals[counter].max() == complement;
      int originalCounter = counter;

      if (minEquals && maxEquals && wasSingleton) {
        throw failException;
      }

      removeValueFromIntervals(counter, complement);

      if (singleton()) {
        v.domainHasChanged(IntDomain.GROUND);
        return;
      }

      notifyInComplementEvent(v, minEquals, maxEquals, originalCounter);

    } else {
      inComplementToNewDomain(storeLevel, v, complement, counter);
    }
    v.domainHasChanged(IntDomain.ANY);
  }

  /**
   * Handles inComplement when storeLevel != stamp: installs a new result domain and removes the
   * complement value.
   */
  private void inComplementToNewDomain(int storeLevel, Var v, double complement, int counter) {
    if (singleton(complement)) {
      throw failException;
    }
    if (ASSERTS_ENABLED && storeLevel <= stamp) {
      throw new IllegalStateException("Assertion failed");
    }
    FloatIntervalDomain result = new FloatIntervalDomain(this.size + 1);
    installResultDomain(result, storeLevel, v);
    if (intervals[counter].min() == complement) {
      if (intervals[counter].max() != complement) {
        System.arraycopy(intervals, 0, result.intervals, 0, size);
        result.intervals[counter] =
            new FloatInterval(next(complement), result.intervals[counter].max());
        result.size = size;
        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }
        notifyComplementEvent(result, v, counter, true);
      } else {
        System.arraycopy(intervals, 0, result.intervals, 0, counter);
        System.arraycopy(intervals, counter + 1, result.intervals, counter, size - counter - 1);
        result.size = size - 1;
        notifyComplementEvent(result, v, counter, true);
      }
      return;
    }
    if (intervals[counter].max() == complement) {
      System.arraycopy(intervals, 0, result.intervals, 0, size);
      result.intervals[counter] =
          new FloatInterval(result.intervals[counter].min(), previous(complement));
      result.size = size;
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      notifyComplementEvent(result, v, counter, false);
      return;
    }
    if (size != 1) {
      System.arraycopy(intervals, 0, result.intervals, 0, counter + 1);
      System.arraycopy(intervals, counter, result.intervals, counter + 1, size - counter);
    }
    double max = intervals[counter].max();
    result.intervals[counter] = new FloatInterval(intervals[counter].min(), previous(complement));
    result.intervals[counter + 1] = new FloatInterval(next(complement), max);
    result.size = size + 1;
  }

  private void notifyInComplementRangeEvent(Var v, boolean isSingleton, boolean boundChange) {
    if (isSingleton) {
      v.domainHasChanged(IntDomain.GROUND);
    } else if (boundChange) {
      v.domainHasChanged(IntDomain.BOUND);
    } else {
      v.domainHasChanged(IntDomain.ANY);
    }
  }

  private void inComplementRangeInPlace(int counter, double min, double max, Var v) {
    if (intervals[counter].min() < min && intervals[counter].max() > max) {
      if (size < intervals.length) {
        for (int i = size; i > counter; i--) {
          intervals[i] = intervals[i - 1];
        }
        intervals[counter + 1] = new FloatInterval(next(max), intervals[counter].max());
        intervals[counter] = new FloatInterval(intervals[counter].min(), previous(min));
      } else {
        FloatInterval[] oldIntervals = intervals;
        intervals = new FloatInterval[oldIntervals.length + 5];
        if (counter > 0) {
          System.arraycopy(oldIntervals, 0, intervals, 0, counter);
        }
        System.arraycopy(oldIntervals, counter + 1, intervals, counter + 2, size - counter - 1);
        intervals[counter + 1] = new FloatInterval(next(max), oldIntervals[counter].max());
        intervals[counter] = new FloatInterval(oldIntervals[counter].min(), previous(min));
      }
      size++;
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      v.domainHasChanged(IntDomain.ANY);
      return;
    }
    int originalCounter = counter;
    removeRangeFromIntervals(counter, min, max);
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (singleton()) {
      v.domainHasChanged(IntDomain.GROUND);
      return;
    }
    notifyInComplementRangeEvent(v, false, originalCounter == 0 || max() > max || min <= min());
  }

  private void inComplementRangeToResult(
      int counter, double min, double max, int storeLevel, Var v) {
    if (ASSERTS_ENABLED && storeLevel <= stamp) {
      throw new IllegalStateException("Assertion failed");
    }
    FloatIntervalDomain result = new FloatIntervalDomain(this.size + 1);
    installResultDomain(result, storeLevel, v);
    result.size = size;
    int noRemoved = 0;
    System.arraycopy(intervals, 0, result.intervals, 0, counter);
    if (intervals[counter].min() < min) {
      if (intervals[counter].max() > max) {
        if (size - counter >= 0) {
          System.arraycopy(intervals, counter, result.intervals, counter + 1, size - counter);
        }
        result.intervals[counter + 1] = new FloatInterval(next(max), intervals[counter].max());
        result.intervals[counter] = new FloatInterval(intervals[counter].min(), previous(min));
        result.size++;
        if (ASSERTS_ENABLED && result.checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(result.checkInvariants()));
        }
        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }
        v.domainHasChanged(IntDomain.ANY);
      } else {
        inComplementRangeToResultLeftThenRemove(result, counter, min, max, noRemoved, v);
      }
    } else {
      inComplementRangeToResultRightOnly(result, counter, min, max, noRemoved, v);
    }
  }

  private void inComplementRangeToResultLeftThenRemove(
      FloatIntervalDomain result, int counter, double min, double max, int noRemoved, Var v) {
    result.intervals[counter] = new FloatInterval(intervals[counter].min(), previous(min));
    int position = ++counter;
    while (position < size && intervals[position].max() <= max) {
      position++;
      noRemoved++;
    }
    for (int i = counter; i + noRemoved < size; i++) {
      result.intervals[i] = intervals[i + noRemoved];
    }
    if (counter + noRemoved < size && intervals[counter + noRemoved].min() <= max) {
      result.intervals[counter] =
          new FloatInterval(next(max), intervals[counter + noRemoved].max());
    }
    result.size -= noRemoved;
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    notifyInComplementRangeEvent(v, result.singleton(), result.max() > max);
  }

  private void inComplementRangeToResultRightOnly(
      FloatIntervalDomain result, int counter, double min, double max, int noRemoved, Var v) {
    if (intervals[counter].max() > max) {
      if (size - (counter + 1) >= 0) {
        System.arraycopy(
            intervals, counter + 1, result.intervals, counter + 1, size - (counter + 1));
      }
      result.intervals[counter] = new FloatInterval(next(max), intervals[counter].max());
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }
      if (result.singleton()) {
        v.domainHasChanged(IntDomain.GROUND);
        return;
      }
      notifyInComplementRangeEvent(v, false, counter == 0);
    } else {
      int position = counter;
      while (position < size && intervals[position].max() <= max) {
        position++;
        noRemoved++;
      }
      for (int i = counter; i + noRemoved < size; i++) {
        result.intervals[i] = intervals[i + noRemoved];
      }
      result.size -= noRemoved;
      if (counter + noRemoved < size && intervals[counter + noRemoved].min() <= max) {
        result.intervals[counter] =
            new FloatInterval(next(max), intervals[counter + noRemoved].max());
      }
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }
      notifyInComplementRangeEvent(v, result.singleton(), result.max() >= max || min <= min());
    }
  }

  @Override
  public void inComplement(int storeLevel, Var v, double min, double max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (intervals[0].min() > max || intervals[size - 1].max() < min) {
      return;
    }

    int counter = 0;

    while (intervals[counter].max() < min) {
      counter++;
    }

    if (intervals[counter].min() > max) {
      return;
    }

    if (min <= min() && max >= max()) {
      throw failException;
    }

    if (storeLevel == stamp) {
      inComplementRangeInPlace(counter, min, max, v);
    } else {
      inComplementRangeToResult(counter, min, max, storeLevel, v);
    }
  }

  /**
   * It updates the domain to contain the elements as specifed by the domain, which is shifted. E.g.
   * {1..4} + 3 = 4..7
   */
  @Override
  public void inShift(int storeLevel, Var v, FloatDomain domain, double shift) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && this.stamp > storeLevel) {
      throw new IllegalStateException("Assertion failed");
    }

    FloatIntervalDomain input = (FloatIntervalDomain) domain;

    if (input.size == 0) {
      throw failException;
    }

    if (ASSERTS_ENABLED && size == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    FloatIntervalDomain result = computeIntersection(input.intervals, input.size, shift);

    if (result == null) {
      return;
    }

    applyResultAndNotify(result, storeLevel, v, computeEvent(result));
  }

  /** It specifies if the domain type is more suited to representing sparse domain. */
  @Override
  public boolean isSparseRepresentation() {
    return false;
  }

  /** It specifies if domain is a finite domain of numeric values (integers). */
  @Override
  public boolean isNumeric() {
    return true;
  }

  /** It returns the left most element of the given interval. */
  @Override
  public double leftElement(int intervalNo) {

    if (ASSERTS_ENABLED && intervalNo >= size) {
      throw new IllegalStateException("Assertion failed");
    }
    return intervals[intervalNo].min();
  }

  /** It returns the left most element of the given interval. */
  @Override
  public double rightElement(int intervalNo) {

    if (ASSERTS_ENABLED && intervalNo >= size) {
      throw new IllegalStateException("Assertion failed");
    }
    return intervals[intervalNo].max();
  }

  /**
   * It removes a level of a domain. If domain is represented as a list of domains, the domain
   * pointer within variable will be updated.
   */
  @Override
  public void removeLevel(int level, Var v) {

    if (ASSERTS_ENABLED && this.stamp > level) {
      throw new IllegalStateException("Assertion failed");
    }

    if (this.stamp == level) {

      ((FloatVar) v).domain = this.prevDomain;
    }

    if (ASSERTS_ENABLED && ((FloatVar) v).domain.stamp >= level) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  /**
   * It adds a constraint to a domain, it should only be called by putConstraint function of
   * Variable object. putConstraint function from Variable must make a copy of a vector of
   * constraints if vector was not cloned.
   */
  @Override
  public void putSearchConstraint(int storeLevel, Var v, Constraint constraint) {

    if (!searchConstraints.contains(constraint)) {

      if (stamp < storeLevel) {

        FloatIntervalDomain result = this.cloneLight();

        installResultDomain(result, storeLevel, v);
        result.searchConstraints =
            new ArrayList<>(searchConstraints.subList(0, searchConstraintsToEvaluate));
        result.searchConstraintsCloned = true;

        result.putSearchConstraint(storeLevel, v, constraint);
        return;
      }

      if (searchConstraints.size() == searchConstraintsToEvaluate) {
        searchConstraints.add(constraint);
      } else {
        // Exchange the first satisfied constraint with just added
        // constraint
        // Order of satisfied constraints is not preserved

        if (searchConstraintsCloned) {
          Constraint firstSatisfied = searchConstraints.get(searchConstraintsToEvaluate);
          searchConstraints.set(searchConstraintsToEvaluate, constraint);
          searchConstraints.add(firstSatisfied);
        } else {
          searchConstraints =
              new ArrayList<>(searchConstraints.subList(0, searchConstraintsToEvaluate));
          searchConstraintsCloned = true;
          searchConstraints.add(constraint);
        }
      }
      searchConstraintsToEvaluate++;
    }
  }

  /**
   * It removes a constraint from a domain, it should only be called by removeConstraint function of
   * Variable object.
   *
   * @param storeLevel the current level of the store.
   * @param v the variable for which the constraint is being removed.
   * @param constraint the constraint being removed.
   */
  public void removeSearchConstraint(int storeLevel, Var v, Constraint constraint) {

    if (stamp < storeLevel) {
      cloneAndInstall(storeLevel, v).removeSearchConstraint(storeLevel, v, constraint);
      return;
    }

    if (ASSERTS_ENABLED && stamp != storeLevel) {
      throw new IllegalStateException("Assertion failed");
    }

    int i = 0;

    while (i < searchConstraintsToEvaluate) {
      if (searchConstraints.get(i) == constraint) {

        searchConstraints.set(i, searchConstraints.get(searchConstraintsToEvaluate - 1));
        searchConstraints.set(searchConstraintsToEvaluate - 1, constraint);
        searchConstraintsToEvaluate--;

        break;
      }
      i++;
    }
  }

  /**
   * It removes a constraint from a domain, it should only be called by removeConstraint function of
   * Variable object.
   */
  @Override
  public void removeSearchConstraint(int storeLevel, Var v, int position, Constraint constraint) {

    if (stamp < storeLevel) {
      cloneAndInstall(storeLevel, v).removeSearchConstraint(storeLevel, v, position, constraint);
      return;
    }

    if (ASSERTS_ENABLED && stamp != storeLevel) {
      throw new IllegalStateException("Assertion failed");
    }

    if (ASSERTS_ENABLED && searchConstraints.get(position) != constraint) {
      throw new IllegalStateException(
          String.valueOf("Position of the removed constraint not specified properly"));
    }

    if (position < searchConstraintsToEvaluate) {

      searchConstraints.set(position, searchConstraints.get(searchConstraintsToEvaluate - 1));
      searchConstraints.set(searchConstraintsToEvaluate - 1, constraint);
      searchConstraintsToEvaluate--;
    }
  }

  /**
   * It removes a constraint from a domain, it should only be called by removeConstraint function of
   * Variable object.
   */
  @Override
  public FloatDomain recentDomainPruning(int storeLevel) {

    if (prevDomain == null) {
      return emptyDomain;
    }

    if (stamp < storeLevel) {
      return emptyDomain;
    }

    return prevDomain.subtract(this);
  }

  /**
   * It returns all constraints which are associated with variable, even the ones which are already
   * satisfied.
   */
  @Override
  public int sizeConstraintsOriginal() {

    FloatDomain domain = this;

    while (true) {

      FloatIntervalDomain dom = (FloatIntervalDomain) domain;

      if (dom.prevDomain != null) {
        domain = dom.prevDomain;
      } else {
        break;
      }
    }

    return domain.modelConstraintsToEvaluate[0]
        + domain.modelConstraintsToEvaluate[1]
        + domain.modelConstraintsToEvaluate[2];
  }

  /** Checks that no interval slot is null. Returns error message or null. */
  private String checkInvariantsIntervalsNotNull() {
    for (int i = 0; i < size; i++) {
      if (this.intervals[i] == null) {
        return "size of the domain is not set up properly";
      }
    }
    return null;
  }

  /** Checks that global min <= max. Returns error message or null. */
  private String checkInvariantsMinMax() {
    if (this.intervals[0].min() > this.intervals[size - 1].max()) {
      return "Min value is larger than max value " + this;
    }
    return null;
  }

  /** Checks each interval has min <= max. Returns error message or null. */
  private String checkInvariantsIntervalBounds() {
    for (int i = 0; i < size; i++) {
      if (this.intervals[i].min() > this.intervals[i].max()) {
        return "One of the intervals not properly build. Min value is larger than max value "
            + this;
      }
    }
    return null;
  }

  /** Checks consecutive intervals are not mergeable. Returns error message or null. */
  private String checkInvariantsConsecutiveNotMerged() {
    for (int i = 0; i < size - 1; i++) {
      if (next(this.intervals[i].max()) == this.intervals[i + 1].min()) {
        return "Two consequtive intervals should be merged. Improper representation" + this;
      }
    }
    return null;
  }

  /**
   * It is a function to check if the object is in consistent state.
   *
   * @return String describing the violated invariant, null if no invariant is violated.
   */
  public String checkInvariants() {
    if (size == 0) {
      return null;
    }
    String err = checkInvariantsIntervalsNotNull();
    if (err != null) {
      return err;
    }
    err = checkInvariantsMinMax();
    if (err != null) {
      return err;
    }
    err = checkInvariantsIntervalBounds();
    if (err != null) {
      return err;
    }
    err = checkInvariantsConsecutiveNotMerged();
    if (err != null) {
      return err;
    }
    return null;
  }

  @Override
  public void subtractAdapt(double value) {

    int counter = intervalNo(value);

    if (counter == -1) {
      return;
    }

    removeValueFromIntervals(counter, value);
  }

  @Override
  public void subtractAdapt(double minValue, double maxValue) {

    int current = 0;
    while (current < size && intervals[current].max() < minValue) {
      current++;
    }

    if (current == size) {
      return;
    }

    removeRangeFromIntervals(current, minValue, maxValue);
  }

  @Override
  public int intersectAdapt(FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == 0) {
      return Domain.NONE;
    }

    FloatIntervalDomain input = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && input.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(input.checkInvariants()));
    }

    if (input.size == 0) {
      size = 0;
      return IntDomain.GROUND;
    }

    FloatIntervalDomain result = computeIntersection(input.intervals, input.size, 0.0);

    if (result == null) {
      return Domain.NONE;
    }

    if (result.isEmpty()) {
      size = 0;
      return IntDomain.GROUND;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    int returnedEvent = computeEvent(result);

    adoptIntervalsFrom(result);

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    return returnedEvent;
  }

  @Override
  public int intersectAdapt(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException(
          String.valueOf("Min value greater than max value " + min + " > " + max));
    }

    if (max < intervals[0].min()) {
      size = 0;
      return IntDomain.GROUND;
    }

    double currentMax = intervals[size - 1].max();
    if (min > currentMax) {
      size = 0;
      return IntDomain.GROUND;
    }

    if (min <= intervals[0].min() && max >= currentMax) {
      return Domain.NONE;
    }

    FloatIntervalDomain result = computeRangeIntersection(min, max);

    adoptIntervalsFrom(result);

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result.singleton() ? IntDomain.GROUND : IntDomain.BOUND;
  }

  @Override
  public int sizeOfIntersection(FloatDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.isEmpty()) {
      return 0;
    }

    FloatIntervalDomain input = (FloatIntervalDomain) domain;

    if (ASSERTS_ENABLED && input.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(input.checkInvariants()));
    }

    int temp = 0;
    //                      FloatIntervalDomain temp;

    int pointer1 = 0;
    int pointer2 = 0;

    int size1 = size;
    int size2 = input.size;

    if (size1 == 0 || size2 == 0) {
      return 0;
    }

    int[] p1 = new int[] {pointer1};
    int[] p2 = new int[] {pointer2};
    int[] tempRef = new int[] {temp};
    sizeOfIntersectionLoop(input, size1, size2, p1, p2, tempRef);
    return tempRef[0];
  }

  /** Result for sizeOfIntersection step: new interval1, new interval2, or null to break. */
  private static final class SizeOfIntersectionStepResult {
    final FloatInterval interval1;
    final FloatInterval interval2;
    final boolean done;

    SizeOfIntersectionStepResult(FloatInterval i1, FloatInterval i2, boolean done) {
      this.interval1 = i1;
      this.interval2 = i2;
      this.done = done;
    }
  }

  private SizeOfIntersectionStepResult sizeOfIntersectionStep(
      FloatIntervalDomain input,
      int size1,
      int size2,
      int[] pointer1,
      int[] pointer2,
      int[] tempRef,
      FloatInterval interval1,
      FloatInterval interval2) {
    if (interval1.max() < interval2.min()) {
      pointer1[0]++;
      return new SizeOfIntersectionStepResult(
          pointer1[0] < size1 ? intervals[pointer1[0]] : null, interval2, pointer1[0] >= size1);
    }
    if (interval2.max() < interval1.min()) {
      pointer2[0]++;
      return new SizeOfIntersectionStepResult(
          interval1,
          pointer2[0] < size2 ? input.intervals[pointer2[0]] : null,
          pointer2[0] >= size2);
    }
    if (interval1.min() <= interval2.min()) {
      if (interval1.max() <= interval2.max()) {
        tempRef[0] += next(interval1.max() - interval2.min());
        pointer1[0]++;
        return new SizeOfIntersectionStepResult(
            pointer1[0] < size1 ? intervals[pointer1[0]] : null, interval2, pointer1[0] >= size1);
      }
      tempRef[0] += next(interval2.max() - interval2.min());
      pointer2[0]++;
      return new SizeOfIntersectionStepResult(
          interval1,
          pointer2[0] < size2 ? input.intervals[pointer2[0]] : null,
          pointer2[0] >= size2);
    }
    if (interval2.max() <= interval1.max()) {
      tempRef[0] += next(interval2.max() - interval1.min());
      pointer2[0]++;
      return new SizeOfIntersectionStepResult(
          interval1,
          pointer2[0] < size2 ? input.intervals[pointer2[0]] : null,
          pointer2[0] >= size2);
    }
    tempRef[0] += next(interval1.max() - interval1.min());
    pointer1[0]++;
    return new SizeOfIntersectionStepResult(
        pointer1[0] < size1 ? intervals[pointer1[0]] : null, interval2, pointer1[0] >= size1);
  }

  /**
   * Accumulates intersection size into tempRef while advancing pointer1/pointer2 over the two
   * interval arrays.
   */
  private void sizeOfIntersectionLoop(
      FloatIntervalDomain input,
      int size1,
      int size2,
      int[] pointer1,
      int[] pointer2,
      int[] tempRef) {
    FloatInterval interval1 = intervals[pointer1[0]];
    FloatInterval interval2 = input.intervals[pointer2[0]];
    while (true) {
      SizeOfIntersectionStepResult r =
          sizeOfIntersectionStep(
              input, size1, size2, pointer1, pointer2, tempRef, interval1, interval2);
      if (r.done) {
        return;
      }
      interval1 = r.interval1;
      interval2 = r.interval2;
    }
  }
}
