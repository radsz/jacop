/*
 * IntervalDomain.java
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

package org.jacop.core;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.Arrays;
import java.util.Iterator;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Constraint;

/**
 * Defines interval of numbers which is part of FDV definition which consist of one or several
 * intervals.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class IntervalDomain extends IntDomain {

  /** An empty domain, so no constant creation of empty domains is required. */
  public static final IntervalDomain emptyDomain = new IntervalDomain(0);

  /** It specifies an empty integer domain. */
  public static final IntDomain EMPTY = emptyDomain;

  /**
   * Extra capacity added to size-based int[] allocations for headroom and fewer resizes. Helps to
   * reduce the resize operations by 75%. Used in all in / inMin / inMax / inValue / in(IntDomain) /
   * inComplement propagation methods. Not used for length-based allocations (e.g. (intervals.length
   * >> 1) + 5) to avoid unbounded growth.
   */
  private static final int ALLOCATION_MARGIN = 1;

  /**
   * The values of the domain, encoded as a flat array of interval bounds: interval {@code i} is
   * {@code bounds[2 * i]..bounds[2 * i + 1]}. Only the first {@code 2 * size} entries are valid.
   */
  int[] bounds;

  /** It specifies number of intervals needed to encode the domain. */
  public int size;

  private static void put(int[] a, int i, int min, int max) {
    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException("min value " + min + " is larger than max value " + max);
    }
    a[2 * i] = min;
    a[2 * i + 1] = max;
  }

  private static void move(int[] dst, int i, int[] src, int j) {
    dst[2 * i] = src[2 * j];
    dst[2 * i + 1] = src[2 * j + 1];
  }

  private static Interval intervalAt(int[] a, int i) {
    return new Interval(a[2 * i], a[2 * i + 1]);
  }

  private static final String ASSERT_MIN_ADDED = "The minimum was not added";
  private static final String ASSERT_MAX_ADDED = "The maximum was not added";
  private static final String IS_INTERSECTING_NOT_IMPLEMENTED =
      "isIntersecting not properly implemented";

  /**
   * Copies metadata from this domain into the result domain and installs it on the variable. Sets
   * previousDomain to this.
   */
  private void installResultDomain(IntervalDomain result, int storeLevel, Var v) {
    result.modelConstraints = modelConstraints;
    result.searchConstraints = searchConstraints;
    result.stamp = storeLevel;
    result.previousDomain = this;
    result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
    result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
    ((IntVar) v).domain = result;
  }

  /**
   * Copies interval data from the source domain into this domain's intervals array, resizing if
   * needed.
   */
  private void adoptIntervalsFrom(IntervalDomain source) {
    if (source.size <= (bounds.length >> 1)) {
      System.arraycopy(source.bounds, 2 * 0, bounds, 2 * 0, 2 * source.size);
    } else {
      bounds = new int[2 * (source.size + ALLOCATION_MARGIN)];
      System.arraycopy(source.bounds, 2 * 0, bounds, 2 * 0, 2 * source.size);
    }
    size = source.size;
  }

  /**
   * Computes the propagation event for a narrowed domain.
   *
   * @param narrowed the new (narrower) domain
   * @return GROUND, BOUND, or ANY
   */
  private int computeEvent(IntDomain narrowed) {
    if (narrowed.singleton()) {
      return GROUND;
    } else if (narrowed.min() > min() || narrowed.max() < max()) {
      return BOUND;
    }
    return ANY;
  }

  /**
   * Computes the event reported to the variable for a narrowed domain.
   *
   * @param narrowed the new (narrower) domain
   * @return GROUND, BOUND, MIN_EVENT, MAX_EVENT or ANY
   */
  private int computeChangeEvent(IntDomain narrowed) {
    if (narrowed.singleton()) {
      return GROUND;
    } else if (narrowed.min() > min() || narrowed.max() < max()) {
      return boundEvent(narrowed.min() > min(), narrowed.max() < max());
    }
    return ANY;
  }

  private IntDomain intersectFromSparse(IntDomain domain) {
    IntDomain temp = null;
    try {
      temp = domain.getClass().getConstructor().newInstance();
    } catch (Exception ex) {
      log.error("{}", ex.getMessage());
    }
    ValueEnumeration enumer = domain.valueEnumeration();
    while (enumer.hasMoreElements()) {
      int next = enumer.nextElement();
      if (this.contains(next)) {
        temp.unionAdapt(next, next);
      }
    }
    return temp;
  }

  /** Ensures the intervals array can hold at least one more element beyond current size. */
  private void ensureCapacity() {
    if (size >= (bounds.length >> 1)) {
      int[] old = bounds;
      // grow geometrically, so that building a domain value by value stays linear
      bounds = new int[2 * ((old.length >> 1) + Math.max(5, (old.length >> 1) >> 1))];
      System.arraycopy(old, 2 * 0, bounds, 2 * 0, 2 * size);
    }
  }

  /**
   * Finds the first interval whose maximum is not smaller than the given value, by binary search.
   *
   * @param value the value
   * @return the position of that interval, or size if all intervals end before the value
   */
  private int firstIntervalEndingAtOrAfter(int value) {
    int low = 0;
    int high = size;
    while (low < high) {
      int middle = (low + high) >>> 1;
      if (bounds[2 * middle + 1] < value) {
        low = middle + 1;
      } else {
        high = middle;
      }
    }
    return low;
  }

  /**
   * Shrinks the domain to its first intervals.
   *
   * @param newSize the number of intervals kept
   */
  private void clearIntervalsFrom(int newSize) {
    size = newSize;
  }

  /**
   * Informs the variable that a bound of this domain, changed in place, has changed.
   *
   * @param v the variable of this domain
   * @param boundEvent the event reported unless the domain has become a singleton
   */
  private void notifyInPlaceBoundChange(Var v, int boundEvent) {
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    v.domainHasChanged(singleton() ? GROUND : boundEvent);
  }

  /**
   * Finds the first interval whose minimum is larger than the given value, by binary search.
   *
   * @param value the value
   * @return the position of that interval, or size if all intervals start at or before the value
   */
  private int firstIntervalStartingAfter(int value) {
    int low = 0;
    int high = size;
    while (low < high) {
      int middle = (low + high) >>> 1;
      if (bounds[2 * middle] <= value) {
        low = middle + 1;
      } else {
        high = middle;
      }
    }
    return low;
  }

  /**
   * Appends a human-readable representation of the domain intervals to the given StringBuilder. If
   * the domain is a singleton, just the single interval is appended; otherwise the intervals are
   * wrapped in braces and separated by commas.
   *
   * @param sb the StringBuilder to append to
   */
  private void appendIntervals(StringBuilder sb) {
    if (!singleton()) {
      sb.append("{");
      for (int e = 0; e < size; e++) {
        sb.append(intervalAt(bounds, e));
        if (e + 1 < size) {
          sb.append(", ");
        }
      }
      sb.append("}");
    } else {
      sb.append(intervalAt(bounds, 0));
    }
  }

  /**
   * Installs a computed interval array as the new domain on a variable, handling both the in-place
   * (stamp==storeLevel) and copy-on-write cases. Fires a GROUND event or the given bound event.
   *
   * @param copy the new intervals array
   * @param out the number of valid intervals in copy
   * @param storeLevel the current store level
   * @param v the variable to update
   * @param boundEvent the event reported unless the domain has become a singleton
   */
  private void installArrayResult(int[] copy, int out, int storeLevel, Var v, int boundEvent) {
    IntervalDomain result = null;
    if (stamp == storeLevel) {
      bounds = copy;
      size = out;
    } else {
      result = new IntervalDomain(copy, out);
      installResultDomain(result, storeLevel, v);
    }
    IntervalDomain effective = stamp == storeLevel ? this : result;
    if (ASSERTS_ENABLED && effective.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(effective.checkInvariants()));
    }
    v.domainHasChanged(effective.singleton() ? GROUND : boundEvent);
  }

  /**
   * Returns the intervals of a domain as {min0, max0, min1, max1, ...}: the array of an
   * IntervalDomain itself, or a new array for any other representation.
   */
  private static int[] boundsOf(IntDomain domain) {
    if (domain.domainId() == INTERVAL_DOMAIN_ID) {
      return ((IntervalDomain) domain).bounds;
    }
    int n = domain.noIntervals();
    int[] result = new int[2 * n];
    for (int i = 0; i < n; i++) {
      result[2 * i] = domain.leftElement(i);
      result[2 * i + 1] = domain.rightElement(i);
    }
    return result;
  }

  /**
   * Finds the first interval of a that no interval of b shifted by shift contains whole.
   *
   * @return its position, or aSize if each interval of a is inside an interval of b + shift
   */
  private static int firstNotCovered(int[] a, int aSize, int[] b, int bSize, int shift) {
    int j = 0;
    for (int i = 0; i < aSize; i++) {
      // the only interval of b that can contain interval i is the first one ending at or after it
      while (j < bSize && b[2 * j + 1] + shift < a[2 * i + 1]) {
        j++;
      }
      if (j == bSize || b[2 * j] + shift > a[2 * i]) {
        return i;
      }
    }
    return aSize;
  }

  /**
   * Writes the intersection of the intervals i..aSize-1 of a with the intervals of b shifted by
   * shift to out, starting at interval position k of out.
   *
   * @return the number of intervals in out
   */
  private static int intersectInto(
      int[] a, int i, int aSize, int[] b, int bSize, int shift, int[] out, int k) {
    int j = 0;
    while (i < aSize && j < bSize) {
      int aMax = a[2 * i + 1];
      int bMax = b[2 * j + 1] + shift;
      int lo = Math.max(a[2 * i], b[2 * j] + shift);
      int hi = Math.min(aMax, bMax);
      if (lo <= hi) {
        out[2 * k] = lo;
        out[2 * k + 1] = hi;
        k++;
      }
      if (aMax <= bMax) {
        i++;
      }
      if (bMax <= aMax) {
        j++;
      }
    }
    return k;
  }

  /**
   * Appends to result the values of lo..hi that are in no interval of b, looking at the intervals
   * of b from position j on.
   *
   * @return the position of the first interval of b that may still meet values above hi
   */
  private static int subtractFrom(
      IntervalDomain result, int lo, int hi, int[] b, int bSize, int j) {
    while (j < bSize && b[2 * j + 1] < lo) {
      j++;
    }
    int from = lo;
    for (; j < bSize && b[2 * j] <= hi; j++) {
      if (b[2 * j] > from) {
        result.appendInterval(from, b[2 * j] - 1);
      }
      if (b[2 * j + 1] >= hi) {
        return j;
      }
      from = b[2 * j + 1] + 1;
    }
    result.appendInterval(from, hi);
    return j;
  }

  /**
   * Computes the event of narrowing this domain to the intervals of copy.
   *
   * @param copy the new intervals
   * @param out the number of new intervals, at least one
   * @param boundEvents true for MIN_EVENT and MAX_EVENT, false for BOUND
   * @return GROUND, a bound event or ANY
   */
  private int narrowingEvent(int[] copy, int out, boolean boundEvents) {
    int newMin = copy[0];
    int newMax = copy[2 * out - 1];
    if (newMin == newMax) {
      return GROUND;
    }
    boolean minChanged = newMin > bounds[0];
    boolean maxChanged = newMax < bounds[2 * size - 1];
    if (!minChanged && !maxChanged) {
      return ANY;
    }
    return boundEvents ? boundEvent(minChanged, maxChanged) : BOUND;
  }

  /**
   * Installs a small dense intersection of this domain on the variable, unless it removes nothing.
   */
  private void inSmallDense(int storeLevel, Var v, SmallDenseDomain result) {

    if (result.isEmpty()) {
      throw Store.failException;
    }

    // the result is a subset of this domain, nothing is removed if it has as many values
    if (result.getSize() == getSize()) {
      return;
    }

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    final int returnedEvent = computeChangeEvent(result);

    result.modelConstraints = modelConstraints;
    result.searchConstraints = searchConstraints;
    result.stamp = storeLevel;
    result.previousDomain = stamp == storeLevel ? previousDomain : this;
    result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
    result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
    ((IntVar) v).domain = result;

    v.domainHasChanged(returnedEvent);
  }

  /** Empty constructor, does not initialize anything. */
  public IntervalDomain() {
    this(0);
  }

  /**
   * It creates an empty domain, with at least specified number of places in an array list for
   * intervals.
   *
   * @param size defines the initial size of an array storing the intervals.
   */
  public IntervalDomain(int size) {
    bounds = new int[2 * (size + ALLOCATION_MARGIN)];
    this.size = 0;
    searchConstraints = null;
    searchConstraintsToEvaluate = 0;
    previousDomain = null;
    searchConstraintsCloned = false;
  }

  /**
   * It creates domain with all values between min and max.
   *
   * @param min defines the left bound of a domain.
   * @param max defines the right bound of a domain.
   */
  public IntervalDomain(int min, int max) {

    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException(
          String.valueOf("Min value can not be greater than max value"));
    }

    bounds = new int[2 * (5 + ALLOCATION_MARGIN)];
    searchConstraints = null;
    searchConstraintsToEvaluate = 0;
    previousDomain = null;
    searchConstraintsCloned = false;
    put(bounds, 0, min, max);
    this.size = 1;
  }

  /**
   * Creates a domain that takes ownership of the given intervals array. The array must hold sorted,
   * disjoint intervals in {@code [0..size-1]}; slots at {@code size} and beyond are ignored.
   *
   * @param intervals array of intervals (caller transfers ownership)
   * @param size number of valid intervals
   */
  public IntervalDomain(int[] bounds, int size) {
    this.bounds = bounds;
    this.size = size;
    searchConstraints = null;
    searchConstraintsToEvaluate = 0;
    previousDomain = null;
    searchConstraintsCloned = false;
  }

  public IntDomain getPreviousDomain() {
    return previousDomain;
  }

  /**
   * {@inheritDoc}
   *
   * <p>It adds at the end without checks for the correctness of domain representation.
   */
  @Override
  public void unionAdapt(Interval i) {
    appendInterval(i.min(), i.max());
  }

  /**
   * It adds the interval min..max at the end without checks for the correctness of the domain
   * representation, as {@link #unionAdapt(Interval)} does.
   *
   * @param min the minimum of the added interval
   * @param max the maximum of the added interval
   */
  void appendInterval(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    ensureCapacity();

    put(bounds, size++, min, max);

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  @Override
  public void unionAdapt(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == 0) {

      bounds = new int[2 * (1 + ALLOCATION_MARGIN)];
      put(bounds, size++, min, max);

    } else if (min > bounds[2 * (size - 1) + 1] + 1) {

      // the most common case when a domain is built in increasing order: append at the end
      ensureCapacity();
      put(bounds, size++, min, max);

    } else if (min >= bounds[2 * (size - 1)]) {

      // min..max starts within or right after the last interval: only the last interval changes
      int lastMin = bounds[2 * (size - 1)];
      int lastMax = bounds[2 * (size - 1) + 1];
      if (max > lastMax) {
        put(bounds, size - 1, lastMin, max);
      }

    } else {

      // min..max starts before the last interval: the first interval it touches, by binary search
      int i = firstIntervalEndingAtOrAfter(min - 1);

      if (max + 1 < bounds[2 * i]) {

        // min..max touches no interval, so it is inserted at position i
        ensureCapacity();
        System.arraycopy(bounds, 2 * i, bounds, 2 * (i + 1), 2 * (size - i));
        put(bounds, i, min, max);
        size++;

      } else {

        // the intervals i..j - 1 touch min..max and are merged with it
        int j = i + 1;
        while (j < size && bounds[2 * j] <= max + 1) {
          j++;
        }
        int newMin = Math.min(min, bounds[2 * i]);
        int newMax = Math.max(max, bounds[2 * (j - 1) + 1]);
        put(bounds, i, newMin, newMax);
        int removed = j - i - 1;
        if (removed > 0) {
          System.arraycopy(bounds, 2 * j, bounds, 2 * (i + 1), 2 * (size - j));
          clearIntervalsFrom(size - removed);
        }
      }
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !contains(min)) {
      throw new IllegalStateException(String.valueOf(ASSERT_MIN_ADDED));
    }
    if (ASSERTS_ENABLED && !contains(max)) {
      throw new IllegalStateException(String.valueOf(ASSERT_MAX_ADDED));
    }
  }

  @Override
  public void unionAdapt(int value) {
    unionAdapt(value, value);
  }

  @Override
  public int unionAdapt(IntDomain union) {

    IntDomain result = union(union);

    if (result.getSize() == getSize()) {
      return NONE;
    } else {
      setDomain(result);
      return ANY;
    }
  }

  /**
   * It adds a value to the domain. It adds at the end without checks for the correctness of domain
   * representation.
   *
   * @param i the element to be added as the lase element of the domain
   */
  public void addLastElement(int i) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (bounds[2 * (size - 1) + 1] + 1 == i) {
      put(bounds, size - 1, bounds[2 * (size - 1)], i);
    } else {
      ensureCapacity();
      put(bounds, size, i, i);
      size++;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  private void addDomFromIntervalDomain(IntervalDomain d) {
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (size == 0) {
      if (bounds == null || (bounds.length >> 1) < (d.bounds.length >> 1)) {
        bounds = new int[2 * (d.bounds.length >> 1)];
      }
      System.arraycopy(d.bounds, 2 * 0, bounds, 2 * 0, 2 * d.size);
      size = d.size;
    } else {
      for (int i = 0; i < d.size; i++) {
        unionAdapt(d.bounds[2 * i], d.bounds[2 * i + 1]);
      }
    }
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  private void addDomFromSparse(IntDomain domain) {
    ValueEnumeration enumer = domain.valueEnumeration();
    while (enumer.hasMoreElements()) {
      int next = enumer.nextElement();
      unionAdapt(next, next);
    }
  }

  private void addDomFromIntervalEnumeration(IntDomain domain) {
    IntervalEnumeration enumer = domain.intervalEnumeration();
    while (enumer.hasMoreElements()) {
      Interval next = enumer.nextElement();
      unionAdapt(next.min(), next.max());
    }
  }

  private void addDomForBoundDomain(IntDomain domain) {
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    unionAdapt(domain.min(), domain.max());
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /**
   * {@inheritDoc}
   *
   * <p>The input parameter can not be an empty set.
   */
  @Override
  public void addDom(IntDomain domain) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID || domain.domainId() == SMALL_DENSE_DOMAIN_ID) {
      for (int x = domain.min(); ; x = domain.nextValue(x)) {
        int end = domain.runEnd(x);
        unionAdapt(x, end);
        if (end >= domain.max()) {
          return;
        }
        x = end;
      }
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {
      addDomFromIntervalDomain((IntervalDomain) domain);
      return;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      addDomForBoundDomain(domain);
      return;
    }

    if (domain.isSparseRepresentation()) {
      addDomFromSparse(domain);
    } else {
      addDomFromIntervalEnumeration(domain);
    }
  }

  private boolean isIntersectingSmallDense(SmallDenseDomain input) {
    ValueEnumeration enumer = input.valueEnumeration();
    int i = 0;
    while (enumer.hasMoreElements()) {
      int next = enumer.nextElement();
      while (i < size && bounds[2 * i + 1] < next) {
        i++;
      }
      if (i == size) {
        if (ASSERTS_ENABLED && isIntersecting(input.toIntervalDomain())) {
          throw new IllegalStateException(String.valueOf(IS_INTERSECTING_NOT_IMPLEMENTED));
        }
        return false;
      }
      if (next >= bounds[2 * i]) {
        if (ASSERTS_ENABLED && !isIntersecting(input.toIntervalDomain())) {
          throw new IllegalStateException(String.valueOf(IS_INTERSECTING_NOT_IMPLEMENTED));
        }
        return true;
      }
    }
    if (ASSERTS_ENABLED && isIntersecting(input.toIntervalDomain())) {
      throw new IllegalStateException(String.valueOf(IS_INTERSECTING_NOT_IMPLEMENTED));
    }
    return false;
  }

  @Override
  public boolean isIntersecting(IntDomain domain) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      return isIntersectingRuns(this, domain);
    }

    if (domain.isEmpty()) {
      return false;
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      IntervalDomain intervalDomain = (IntervalDomain) domain;

      int pointer1 = 0;
      int pointer2 = 0;

      int size2 = intervalDomain.size;

      if (size == 0 || size2 == 0) {
        return false;
      }

      int interval1Min = bounds[2 * pointer1];
      int interval1Max = bounds[2 * pointer1 + 1];
      int interval2Min = intervalDomain.bounds[2 * pointer2];
      int interval2Max = intervalDomain.bounds[2 * pointer2 + 1];

      while (true) {
        if (interval1Max < interval2Min) {
          pointer1++;
          if (pointer1 < size) {
            interval1Min = bounds[2 * pointer1];
            interval1Max = bounds[2 * pointer1 + 1];
          } else {
            break;
          }
        } else if (interval2Max < interval1Min) {
          pointer2++;
          if (pointer2 < size2) {
            interval2Min = intervalDomain.bounds[2 * pointer2];
            interval2Max = intervalDomain.bounds[2 * pointer2 + 1];
          } else {
            break;
          }
        } else {
          return true;
        }
      }

      return false;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      // the holes of this domain matter, not only its bounds
      return isIntersecting(domain.min(), domain.max());
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      if (isEmpty()) {
        return false;
      }

      if (input.min() == min() || input.max() == max()) {
        return true;
      }

      if (input.max() < min() || max() < input.min()) {
        return false;
      }

      if (input.getSize() <= 8) {
        return isIntersectingSmallDense(input);
      } else {
        return isIntersectingRuns(this, domain);
      }
    }

    if (domain.isSparseRepresentation()) {

      ValueEnumeration enumer = domain.valueEnumeration();

      while (enumer.hasMoreElements()) {
        if (contains(enumer.nextElement())) {
          return true;
        }
      }

      return false;

    } else {

      IntervalEnumeration enumer = domain.intervalEnumeration();

      while (enumer.hasMoreElements()) {

        Interval next = enumer.nextElement();
        if (this.isIntersecting(next.min(), next.max())) {
          return true;
        }
      }

      return false;
    }
  }

  @Override
  public boolean isIntersecting(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    int i = firstIntervalEndingAtOrAfter(min);

    return i != size && bounds[2 * i] <= max;
  }

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
  public IntervalDomain cloneLight() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain cloned = new IntervalDomain((this.bounds.length >> 1));

    System.arraycopy(bounds, 2 * 0, cloned.bounds, 2 * 0, 2 * size);

    cloned.size = size;

    return cloned;
  }

  @Override
  public IntervalDomain copy() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain cloned = cloneLight();

    cloned.stamp = stamp;
    cloned.previousDomain = previousDomain;

    cloned.searchConstraints = searchConstraints;
    cloned.searchConstraintsToEvaluate = searchConstraintsToEvaluate;

    cloned.modelConstraints = modelConstraints;
    cloned.modelConstraintsToEvaluate = modelConstraintsToEvaluate;

    cloned.searchConstraintsCloned = searchConstraintsCloned;

    return cloned;
  }

  /**
   * {@inheritDoc}
   *
   * <p>It assumes that input parameter does not represent an empty domain.
   */
  @Override
  public boolean contains(IntDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      return containsRuns(this, domain);
    }

    if (isEmpty()) {
      return domain.isEmpty();
    }

    if (domain.isEmpty()) {
      return true;
    }

    if (domain.isSparseRepresentation()) {

      ValueEnumeration enumer = domain.valueEnumeration();

      while (enumer.hasMoreElements()) {
        if (!contains(enumer.nextElement())) {
          return false;
        }
      }

      return true;

    } else {

      int max2 = domain.noIntervals();

      int i1 = 0;
      int i2 = 0;

      if (max2 == 0) {
        return true;
      }

      int interval1Min = bounds[0];
      int interval1Max = bounds[1];
      int interval2Min = domain.leftElement(0);
      int interval2Max = domain.rightElement(0);

      while (true) {

        while (interval2Min > interval1Max) {

          i1++;

          if (i1 == size) {
            return false;
          }

          interval1Min = bounds[2 * i1];
          interval1Max = bounds[2 * i1 + 1];
        }

        if (interval2Min < interval1Min || interval2Max > interval1Max) {
          return false;
        }

        i2++;

        if (i2 == max2) {
          return true;
        }

        interval2Min = domain.leftElement(i2);
        interval2Max = domain.rightElement(i2);
      }
    }
  }

  @Override
  public boolean contains(int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    // binary search algorithm
    int l = 0;
    int r = size - 1;

    while (l <= r) {
      // but shift right by one position does it also and it is faster ;)
      int m = (l + r) >> 1;
      int iMin = bounds[2 * m];
      int iMax = bounds[2 * m + 1];

      if (value > iMax) {
        l = m + 1;
      } else if (value >= iMin) {
        return true;
      } else {
        r = m - 1;
      }
    }

    return false;
  }

  @Override
  public boolean contains(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (min <= max) {
      int m = firstIntervalEndingAtOrAfter(max);
      return m != size && bounds[2 * m] <= min;
    }

    for (int m = 0; m < size; m++) {
      int iMin = bounds[2 * m];
      int iMax = bounds[2 * m + 1];
      if (iMax >= max && min >= iMin) {
        return true;
      }
    }

    return false;
  }

  @Override
  public IntDomain complement() {

    if (size == 0) {
      return new IntervalDomain(MIN_INT, MAX_INT);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain result = new IntervalDomain(size + 1);
    if (min() != MIN_INT) {
      result.appendInterval(MIN_INT, bounds[0] - 1);
    }

    for (int i = 0; i < size - 1; i++) {
      result.appendInterval(bounds[2 * i + 1] + 1, bounds[2 * (i + 1)] - 1);
    }

    if (max() != MAX_INT) {
      result.appendInterval(max() + 1, MAX_INT);
    }

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    return result;
  }

  /**
   * {@inheritDoc}
   *
   * <p>The provided value does not have to belong to the domain.
   */
  @Override
  public int runEnd(int value) {
    return bounds[2 * (firstIntervalEndingAtOrAfter(value)) + 1];
  }

  @Override
  public long bitsFrom(int lo) {
    long hi = (long) lo + 63;
    long result = 0;
    for (int i = firstIntervalEndingAtOrAfter(lo); i < size && bounds[2 * i] <= hi; i++) {
      int from = Math.max(bounds[2 * i], lo);
      int to = (int) Math.min(bounds[2 * i + 1], hi);
      result |= bitRange(from - lo, to - lo);
    }
    return result;
  }

  @Override
  public int nextValue(int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    // the first interval which ends after value
    int m = value == Integer.MAX_VALUE ? size : firstIntervalEndingAtOrAfter(value + 1);
    if (m == size) {
      return value;
    }

    int iMin = bounds[2 * m];
    if (value >= iMin - 1) {
      return value + 1;
    } else {
      return iMin;
    }
  }

  @Override
  public ValueEnumeration valueEnumeration() {
    return new IntervalDomainValueEnumeration(this);
  }

  @Override
  public IntervalEnumeration intervalEnumeration() {
    return new IntervalDomainIntervalEnumeration(this);
  }

  private boolean eqSparse(IntDomain domain) {
    if (this.getSize() != domain.getSize()) {
      return false;
    }
    ValueEnumeration enumer1 = domain.valueEnumeration();
    ValueEnumeration enumer2 = this.valueEnumeration();
    while (enumer1.hasMoreElements()) {
      if (enumer1.nextElement() != enumer2.nextElement()) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean eq(IntDomain domain) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      return getSize() == domain.getSize() && containsRuns(this, domain);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      return domain.eq(this);
    }

    // Uses default dense and sparse assumptions to compute the function as
    // efficiently as possible.

    if (domain.isSparseRepresentation()) {
      return eqSparse(domain);
    } else {

      int n = domain.noIntervals();
      if (size != n) {
        return false;
      }
      for (int i = 0; i < n; i++) {
        if (bounds[2 * i] != domain.leftElement(i) || bounds[2 * i + 1] != domain.rightElement(i)) {
          return false;
        }
      }
      return true;
    }
  }

  @Override
  public int getSize() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    int n = 0;

    for (int i = 0; i < size; i++) {
      n = n + bounds[2 * i + 1] - bounds[2 * i] + 1;
    }

    return n;
  }

  @Override
  public IntDomain intersect(IntDomain domain) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      return intersectRuns(this, domain, 0);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.isEmpty()) {
      return emptyDomain;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      return intersect(domain.min(), domain.max());
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {
      return intersectRuns(this, domain, 0);
    }

    if (domain.isSparseRepresentation()) {
      return intersectFromSparse(domain);
    }

    int inputSize = domain.noIntervals();
    if (size == 0 || inputSize == 0) {
      return new IntervalDomain(size);
    }
    int[] result = new int[2 * (size + inputSize)];
    int out = intersectInto(bounds, 0, size, boundsOf(domain), inputSize, 0, result, 0);
    return new IntervalDomain(result, out);
  }

  @Override
  public IntDomain intersect(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain temp = new IntervalDomain(size);

    if (size == 0) {
      return this;
    }

    int pointer1 = 0;

    int interval1Min = bounds[2 * pointer1];
    int interval1Max = bounds[2 * pointer1 + 1];

    while (true) {
      if (interval1Max < min) {
        pointer1++;
        if (pointer1 < size) {
          interval1Min = bounds[2 * pointer1];
          interval1Max = bounds[2 * pointer1 + 1];
        } else {
          break;
        }
      } else if (max < interval1Min) {
        break;
      } else
      // interval1.max >= interval2.min
      // interval2.max >= interval1.min
      if (interval1Min <= min) {

        if (interval1Max <= max) {

          temp.appendInterval(min, interval1Max);
          pointer1++;
          if (pointer1 < size) {
            interval1Min = bounds[2 * pointer1];
            interval1Max = bounds[2 * pointer1 + 1];
          } else {
            break;
          }
        } else {
          temp.appendInterval(min, max);
          break;
        }

      } else {
        // interval1.max >= interval2.min
        // interval2.max >= interval1.min
        // interval1.min > interval2.min
        if (max <= interval1Max) {
          temp.appendInterval(interval1Min, max);
          // pointer2++;
          break;
        } else {
          temp.appendInterval(interval1Min, interval1Max);
          pointer1++;
          if (pointer1 < size) {
            interval1Min = bounds[2 * pointer1];
            interval1Max = bounds[2 * pointer1 + 1];
          } else {
            break;
          }
        }
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

  @Override
  public boolean isEmpty() {
    return size == 0;
  }

  @Override
  public int max() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == 0) {
      throw new IllegalStateException("max() called on an empty domain");
    }

    return bounds[2 * (size - 1) + 1];
  }

  @Override
  public int min() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && size == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    return bounds[0];
  }

  /**
   * {1..4} * 6 = {6, 12, 18, 24}
   *
   * @param mul the multiplier constant.
   * @return the domain after multiplication.
   */
  public IntDomain multiply(int mul) {

    if (ASSERTS_ENABLED && mul == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    IntervalDomain temp = new IntervalDomain(getSize() * mul);

    if (mul > 0) {

      for (int m = 0; m < size; m++) {
        int i1Min = bounds[2 * m];
        int i1Max = bounds[2 * m + 1];
        for (int i = i1Min; i <= i1Max; i++) {
          int value = i * mul;
          temp.appendInterval(value, value);
        }
      }

    } else {

      for (int m = size - 1; m >= 0; m--) {
        int i1Min = bounds[2 * m];
        int i1Max = bounds[2 * m + 1];
        for (int i = i1Max; i >= i1Min; i--) {
          int value = i * mul;
          temp.appendInterval(value, value);
        }
      }
    }
    if (ASSERTS_ENABLED && temp.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(temp.checkInvariants()));
    }
    return temp;
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
      move(bounds, position, bounds, position + 1);
      position++;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  @Override
  public void setDomain(IntDomain domain) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      clear();
      addDom(domain);
      return;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain intervalDomain = (IntervalDomain) domain;

      size = intervalDomain.size;

      bounds = new int[2 * (intervalDomain.bounds.length >> 1)];
      System.arraycopy(intervalDomain.bounds, 2 * 0, bounds, 2 * 0, 2 * size);

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      return;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {

      size = 1;

      bounds = new int[2 * (1 + ALLOCATION_MARGIN)];
      put(bounds, 0, domain.min(), domain.max());

      return;
    }

    if (domain.isSparseRepresentation()) {

      this.clear();

      ValueEnumeration enumer = domain.valueEnumeration();

      while (enumer.hasMoreElements()) {

        int next = enumer.nextElement();

        if (this.contains(next)) {
          this.unionAdapt(next, next);
        }
      }

    } else {

      this.clear();

      IntervalEnumeration enumer = domain.intervalEnumeration();

      while (enumer.hasMoreElements()) {
        this.unionAdapt(enumer.nextElement());
      }
    }
  }

  @Override
  public void setDomain(int min, int max) {
    size = 1;
    put(bounds, 0, min, max);
  }

  @Override
  public boolean singleton() {
    return size == 1 && bounds[0] == bounds[1];
  }

  @Override
  public boolean singleton(int c) {
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    return size == 1 && bounds[0] == c && c == bounds[1];
  }

  @Override
  public IntDomain subtract(int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain result = cloneLight();

    int pointer1 = 0;

    if (size == 0) {
      return result;
    }

    int interval1Min = bounds[2 * pointer1];
    int interval1Max = bounds[2 * pointer1 + 1];

    while (pointer1 < size && interval1Max < value) {
      pointer1++;
      if (pointer1 < size) {
        interval1Min = bounds[2 * pointer1];
        interval1Max = bounds[2 * pointer1 + 1];
      }
    }

    if (pointer1 < size && interval1Min <= value) {

      if (interval1Min != value) {

        int oldMax = interval1Max;
        // replace min..max with interval1.min..value-1
        put(result.bounds, pointer1, interval1Min, value - 1);
        pointer1++;

        if (value != oldMax) {
          // add domain value+1..oldMax
          result.unionAdapt(value + 1, oldMax);
          pointer1++;
        }

      } else if (interval1Max != value) {
        // replace value..max with value+1..interval1.max
        put(result.bounds, pointer1, value + 1, interval1Max);
        pointer1++;
      } else {
        result.removeInterval(pointer1);
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

  @Override
  public IntDomain subtract(IntDomain domain) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      return subtractRuns(this, domain);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (isEmpty()) {
      return EMPTY;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      if (domain.isEmpty()) {
        return cloneLight();
      }
      return subtract(domain.min(), domain.max());
    }

    if (domain.isSparseRepresentation()) {
      return subtractFromSparse(domain);
    }

    int inputSize = domain.noIntervals();
    if (inputSize == 0) {
      return cloneLight();
    }

    int[] input = boundsOf(domain);
    IntervalDomain result = new IntervalDomain(size + inputSize + ALLOCATION_MARGIN);
    int j = 0;
    for (int i = 0; i < size; i++) {
      j = subtractFrom(result, bounds[2 * i], bounds[2 * i + 1], input, inputSize, j);
    }

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result;
  }

  @Override
  public IntervalDomain subtract(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException("Assertion failed");
    }

    if (size == 0) {
      return emptyDomain;
    }

    // interval under the analysis
    int i1 = 0;
    // place for next interval in subtracted domain
    int currentInterval1Min = bounds[2 * i1];
    int currentInterval1Max = bounds[2 * i1 + 1];

    IntervalDomain result = new IntervalDomain((bounds.length >> 1) + 1);

    while (true) {

      if (currentInterval1Max < min) {
        result.appendInterval(bounds[2 * i1], bounds[2 * i1 + 1]);
        i1++;
        if (i1 == size) {
          break;
        }
        currentInterval1Min = bounds[2 * i1];
        currentInterval1Max = bounds[2 * i1 + 1];
        continue;
      }

      if (max < currentInterval1Min) {
        break;
      }

      if (currentInterval1Min >= min) {

        // currentDomain1.max >= min
        // max >= currentDomain1.min

        if (currentInterval1Max <= max) {
          // Skip current interval of i1 completely
          i1++;
          if (i1 == size) {
            break;
          }
          currentInterval1Min = bounds[2 * i1];
          currentInterval1Max = bounds[2 * i1 + 1];

        } else {

          // interval of dom2 ends before interval of dom1 ends
          // currentDomain2.max+1 .. currentDomain1.max
          // BUT next currentdomain2.min needs to be larger than
          // currentDomain1.max

          result.appendInterval(max + 1, currentInterval1Max);

          i1++;
          break;
        }
      } else {

        if (currentInterval1Max <= max) {

          result.appendInterval(currentInterval1Min, min - 1);

          i1++;

          if (i1 == size) {
            break;
          }
          currentInterval1Min = bounds[2 * i1];
          currentInterval1Max = bounds[2 * i1 + 1];
          // next intervals of the domain may be before max.

        } else {

          // interval of min..max ends before interval of dom1 ends
          // max+1 .. currentDomain1.max

          result.unionAdapt(currentInterval1Min, min - 1);
          result.unionAdapt(max + 1, currentInterval1Max);

          i1++;
          break;
        }
      }
    }

    for (int i = i1; i < size; i++) {
      result.appendInterval(bounds[2 * i], bounds[2 * i + 1]);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    return result;
  }

  private IntDomain subtractFromSparse(IntDomain domain) {
    IntDomain result = this.cloneLight();
    ValueEnumeration enumer = domain.valueEnumeration();
    while (enumer.hasMoreElements()) {
      int next = enumer.nextElement();
      result.subtractAdapt(next);
    }
    if (ASSERTS_ENABLED
        && !(!(domain instanceof SmallDenseDomain denseDomain)
            || result.eq(this.subtract(denseDomain.toIntervalDomain())))) {
      throw new IllegalStateException(
          String.valueOf(
              "Subtract function is not working" + this + "d:" + domain + "r:" + result));
    }
    return result;
  }

  private IntervalDomain unionFromSparse(IntDomain domain) {
    IntervalDomain result = this.cloneLight();
    ValueEnumeration enumer = domain.valueEnumeration();
    while (enumer.hasMoreElements()) {
      int next = enumer.nextElement();
      result.unionAdapt(next, next);
    }
    if (ASSERTS_ENABLED
        && !(!(domain instanceof SmallDenseDomain denseDomain)
            || result.eq(this.union(denseDomain.toIntervalDomain())))) {
      throw new IllegalStateException(
          String.valueOf(
              "Basic union function not working properly "
                  + this
                  + "d: "
                  + domain
                  + "r:"
                  + result));
    }
    return result;
  }

  @Override
  public IntDomain union(IntDomain domain) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      return unionRuns(this, domain);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      if (domain.isEmpty()) {
        return cloneLight();
      }
      return union(domain.min(), domain.max());
    }

    if (domain.isSparseRepresentation()) {
      return unionFromSparse(domain);
    } else {

      if (domain.noIntervals() == 0) {
        return cloneLight();
      }

      if (size == 0) {
        return domain.cloneLight();
      }

      IntervalDomain result = new IntervalDomain(size);

      int i1 = 0;
      int i2 = 0;

      int currentDomain1Min = bounds[2 * i1];
      int currentDomain1Max = bounds[2 * i1 + 1];
      int currentDomain2Min = domain.leftElement(i2);
      int currentDomain2Max = domain.rightElement(i2);

      int max1 = size;

      while (true) {

        if (currentDomain1Max + 1 < currentDomain2Min) {
          result.appendInterval(currentDomain1Min, currentDomain1Max);
          i1++;
          if (i1 == max1) {
            break;
          }
          currentDomain1Min = bounds[2 * i1];
          currentDomain1Max = bounds[2 * i1 + 1];
          continue;
        }

        if (currentDomain2Max + 1 < currentDomain1Min) {
          result.appendInterval(currentDomain2Min, currentDomain2Max);
          i2++;
          if (i2 < domain.noIntervals()) {
            currentDomain2Min = domain.leftElement(i2);
            currentDomain2Max = domain.rightElement(i2);
            continue;
          } else {
            break;
          }
        }

        int min = Math.min(currentDomain1Min, currentDomain2Min);

        while ((currentDomain1Max + 1 >= currentDomain2Min
                && currentDomain1Min <= currentDomain2Min)
            || (currentDomain2Max + 1 >= currentDomain1Min
                && currentDomain2Min <= currentDomain1Min)) {

          if (currentDomain1Max <= currentDomain2Max) {
            i1++;
            if (i1 == max1) {
              break;
            }
            currentDomain1Min = bounds[2 * i1];
            currentDomain1Max = bounds[2 * i1 + 1];
            continue;
          }

          i2++;
          if (i2 < domain.noIntervals()) {
            currentDomain2Min = domain.leftElement(i2);
            currentDomain2Max = domain.rightElement(i2);
          } else {
            break;
          }
        }

        if (i1 == max1) {

          while (currentDomain2Max <= currentDomain1Max) {
            i2++;
            if (i2 < domain.noIntervals()) {
              currentDomain2Min = domain.leftElement(i2);
              currentDomain2Max = domain.rightElement(i2);
            } else {
              break;
            }
          }

          if (currentDomain1Max <= currentDomain2Max
              && currentDomain1Max + 1 >= currentDomain2Min) {
            result.appendInterval(min, currentDomain2Max);
            i2++;
          } else {
            result.appendInterval(min, currentDomain1Max);
          }
          break;
        }

        if (domain.noIntervals() == i2) {

          while (currentDomain1Max <= currentDomain2Max) {
            i1++;
            if (i1 == max1) {
              break;
            }
            currentDomain1Min = bounds[2 * i1];
            currentDomain1Max = bounds[2 * i1 + 1];
          }

          if (currentDomain2Max <= currentDomain1Max
              && currentDomain2Max + 1 >= currentDomain1Min) {
            result.appendInterval(min, currentDomain1Max);
            i1++;
          } else {
            result.appendInterval(min, currentDomain2Max);
          }
          break;
        }

        if (currentDomain1Max < currentDomain2Max) {
          result.appendInterval(min, currentDomain1Max);
          i1++;
          if (i1 == max1) {
            break;
          }
          currentDomain1Min = bounds[2 * i1];
          currentDomain1Max = bounds[2 * i1 + 1];
        } else {
          result.appendInterval(min, currentDomain2Max);
          i2++;
          if (i2 < domain.noIntervals()) {
            currentDomain2Min = domain.leftElement(i2);
            currentDomain2Max = domain.rightElement(i2);
          } else {
            break;
          }
        }
      }

      if (i1 < max1) {
        for (; i1 < max1; i1++) {
          result.appendInterval(bounds[2 * i1], bounds[2 * i1 + 1]);
        }
      }

      for (; i2 < domain.noIntervals(); i2++) {
        result.appendInterval(domain.leftElement(i2), domain.rightElement(i2));
      }

      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      return result;
    }
  }

  @Override
  public IntDomain union(int min, int max) {

    if (size == 0) {
      return new IntervalDomain(min, max);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain result = new IntervalDomain(size + 1);

    int i1 = 0;

    int currentInterval1Min = bounds[2 * i1];
    int currentInterval1Max = bounds[2 * i1 + 1];

    // all intervals before and not glued (min..max) are included
    while (i1 < size && currentInterval1Max + 1 < min) {
      result.appendInterval(currentInterval1Min, currentInterval1Max);
      i1++;
      if (i1 < size) {
        currentInterval1Min = bounds[2 * i1];
        currentInterval1Max = bounds[2 * i1 + 1];
      }
    }

    if (i1 == size) {
      result.appendInterval(min, max);
    } else if (max + 1 < currentInterval1Min) {
      // currentInterval if after and not glued
      result.appendInterval(min, max);
    } else {
      // current interval is glued or intersects with (min..max).

      int tempMin;

      if (currentInterval1Min < min) {
        tempMin = currentInterval1Min;
      } else {
        tempMin = min;
      }

      if (currentInterval1Max > max) {
        result.appendInterval(tempMin, currentInterval1Max);
        i1++;
      } else {

        // (min..max) can cover multiple intervals.
        while (currentInterval1Max <= max) {
          i1++;
          if (i1 == size) {
            result.appendInterval(tempMin, max);
            break;
          }
          currentInterval1Min = bounds[2 * i1];
          currentInterval1Max = bounds[2 * i1 + 1];
        }

        if (i1 < size) {
          // if current interval is glued or intersects with (min..max)
          if (max + 1 >= currentInterval1Min) {
            result.appendInterval(tempMin, currentInterval1Max);
            i1++;
          } else {
            result.appendInterval(tempMin, max);
          }
        }
      }
    }

    if (i1 < size) {
      for (; i1 < size; i1++) {
        result.appendInterval(bounds[2 * i1], bounds[2 * i1 + 1]);
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

  @Override
  public IntDomain union(int value) {

    if (size == 0) {
      return new IntervalDomain(value, value);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain result = new IntervalDomain(size + 1);

    int i1 = 0;

    int currentIntervalMin = bounds[2 * i1];
    int currentIntervalMax = bounds[2 * i1 + 1];

    while (true) {

      if (currentIntervalMax + 1 < value) {
        result.appendInterval(currentIntervalMin, currentIntervalMax);
        i1++;
        if (i1 == size) {
          result.appendInterval(value, value);
          return result;
        }
        currentIntervalMin = bounds[2 * i1];
        currentIntervalMax = bounds[2 * i1 + 1];
      } else {
        break;
      }
    }

    if (value + 1 < currentIntervalMin) {
      result.appendInterval(value, value);
    } else {

      int tempMin = value;
      int tempMax = value;

      if (currentIntervalMin < value) {
        tempMin = currentIntervalMin;
      }

      if (currentIntervalMax > value) {
        tempMax = currentIntervalMax;
      }

      if (i1 + 1 < size && tempMax + 1 == bounds[2 * (i1 + 1)]) {
        tempMax = bounds[2 * (i1 + 1) + 1];
        i1++;
      }

      result.appendInterval(tempMin, tempMax);
      i1++;
    }

    if (i1 < size) {
      for (; i1 < size; i1++) {
        result.appendInterval(bounds[2 * i1], bounds[2 * i1 + 1]);
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

  @Override
  public String toString() {

    StringBuilder s = new StringBuilder();
    appendIntervals(s);
    return s.toString();
  }

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

  @Override
  public String toStringFull() {

    StringBuilder result = new StringBuilder();

    IntDomain domain = this;

    do {
      if (!domain.singleton()) {
        result.append("{");

        for (int e = 0; e < size; e++) {
          result.append(intervalAt(bounds, e));
          if (e + 1 < size) {
            result.append(", ");
          }
        }

        result.append("} ").append("(").append(domain.stamp()).append(") ");
      } else {
        result.append(intervalAt(bounds, 0)).append("(").append(domain.stamp()).append(") ");
      }

      result.append("constraints: ");

      for (Constraint searchConstraint : domain.searchConstraints) {
        result.append(searchConstraint);
      }

      if (domain.domainId() == INTERVAL_DOMAIN_ID) {

        IntervalDomain dom = (IntervalDomain) domain;
        domain = dom.previousDomain;

      } else {
        break;
      }

    } while (domain != null);

    return result.toString();
  }

  @Override
  public void inMin(int storeLevel, Var v, int min) {

    if (ASSERTS_ENABLED && (size == 0 || checkInvariants() != null)) {
      throw new IllegalStateException(
          size == 0 ? "inMin called on an empty domain" : String.valueOf(checkInvariants()));
    }

    if (min > bounds[2 * (size - 1) + 1]) {
      throw failException;
    }

    if (min <= bounds[0]) {
      return;
    }

    int pointer = firstIntervalEndingAtOrAfter(min);

    if (stamp == storeLevel) {
      // the domain already belongs to this level, the intervals are moved in place
      int firstMin = bounds[2 * pointer];
      int firstMax = bounds[2 * pointer + 1];
      int remaining = size - pointer;
      System.arraycopy(bounds, 2 * pointer, bounds, 2 * 0, 2 * remaining);
      if (firstMin < min) {
        put(bounds, 0, min, firstMax);
      }
      clearIntervalsFrom(remaining);
      notifyInPlaceBoundChange(v, MIN_EVENT);
      return;
    }

    int out = 0;
    int p = pointer;
    int ivMin = bounds[2 * p];
    int ivMax = bounds[2 * p + 1];
    int[] copy = new int[2 * (size + ALLOCATION_MARGIN)];
    if (ivMin < min) {
      put(copy, out++, min, ivMax);
      p++;
    } else {
      put(copy, out++, ivMin, ivMax);
      p++;
    }
    while (p < size) {
      move(copy, out++, bounds, p++);
    }

    installArrayResult(copy, out, storeLevel, v, MIN_EVENT);
  }

  @Override
  public void inMax(int storeLevel, Var v, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (max < bounds[0]) {
      throw failException;
    }

    int currentMax = bounds[2 * (size - 1) + 1];

    if (max >= currentMax) {
      return;
    }

    int pointer = firstIntervalStartingAfter(max) - 1;

    if (stamp == storeLevel) {
      // the domain already belongs to this level, the intervals are cut in place
      int lastMin = bounds[2 * pointer];
      int lastMax = bounds[2 * pointer + 1];
      if (lastMax > max) {
        put(bounds, pointer, lastMin, max);
      }
      clearIntervalsFrom(pointer + 1);
      notifyInPlaceBoundChange(v, MAX_EVENT);
      return;
    }

    int out = 0;
    int p = 0;
    int[] copy = new int[2 * (size + ALLOCATION_MARGIN)];
    while (p < pointer) {
      move(copy, out++, bounds, p++);
    }
    int ivMin = bounds[2 * pointer];
    int ivMax = bounds[2 * pointer + 1];
    if (ivMax > max) {
      put(copy, out++, ivMin, max);
    } else {
      put(copy, out++, ivMin, ivMax);
    }

    installArrayResult(copy, out, storeLevel, v, MAX_EVENT);
  }

  @Override
  public void in(int storeLevel, Var v, int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException(
          String.valueOf("Min value greater than max value " + min + " > " + max));
    }

    if (max < bounds[0]) {
      throw failException;
    }

    int currentMax = bounds[2 * (size - 1) + 1];
    if (min > currentMax) {
      throw failException;
    }

    if (min <= bounds[0] && max >= currentMax) {
      return;
    }

    int pointer = 0;

    // pointer is always smaller than size as domains intersect
    pointer = firstIntervalEndingAtOrAfter(min);

    if (bounds[2 * pointer] > max) {
      throw failException;
    }

    int out = 0;
    int p = pointer;

    int a = Math.max(bounds[2 * p], min);
    int b = Math.min(bounds[2 * p + 1], max);
    int[] copy = new int[2 * (size + ALLOCATION_MARGIN)];
    put(copy, out, a, b);
    out++;
    p++;

    while (p < size && bounds[2 * p + 1] <= max) {
      move(copy, out++, bounds, p++);
    }

    if (p < size && bounds[2 * p] <= max) {
      a = Math.max(bounds[2 * p], min);
      b = Math.min(bounds[2 * p + 1], max);
      put(copy, out, a, b);
      out++;
    }

    installArrayResult(copy, out, storeLevel, v, boundEvent(min > bounds[0], max < currentMax));
  }

  /**
   * It keeps the values x of this domain for which x - shift is in the domain, walking the runs of
   * both domains, and reports one event as {@link #in(int, Var, IntDomain)} does.
   */
  private void inRuns(int storeLevel, Var v, IntDomain domain, int shift) {
    if (domain.isEmpty()) {
      throw failException;
    }
    // the intervals the argument covers whole are kept; the result is built from the first one
    // that is not covered
    IntervalDomain result = null;
    for (int k = 0; k < size; k++) {
      int ivMin = bounds[2 * k];
      int ivMax = bounds[2 * k + 1];
      if (domain.contains(ivMin - shift, ivMax - shift)) {
        if (result != null) {
          result.unionAdapt(ivMin, ivMax);
        }
        continue;
      }
      if (result == null) {
        result = new IntervalDomain(size + 1);
        System.arraycopy(bounds, 2 * 0, result.bounds, 2 * 0, 2 * k);
        result.size = k;
      }
      addShiftedRuns(result, domain, shift, ivMin, ivMax);
    }
    if (result == null) {
      return;
    }
    if (result.isEmpty()) {
      throw failException;
    }
    in(storeLevel, v, result);
  }

  /** It adds to result the values x of lo..hi for which x - shift is in domain. */
  private static void addShiftedRuns(
      IntervalDomain result, IntDomain domain, int shift, int lo, int hi) {
    int y = lo - shift;
    if (!domain.contains(y)) {
      int next = domain.nextValue(y);
      if (next <= y) {
        return;
      }
      y = next;
    }
    while (y + shift <= hi) {
      int end = Math.min(domain.runEnd(y) + shift, hi);
      result.unionAdapt(y + shift, end);
      if (end >= hi) {
        return;
      }
      int next = domain.nextValue(end - shift);
      if (next <= end - shift) {
        return;
      }
      y = next;
    }
  }

  @Override
  public void in(int storeLevel, Var v, IntDomain domain) {
    inShift(storeLevel, v, domain, 0);
  }

  @Override
  public void inValue(int storeLevel, IntVar v, int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (singleton(value)) {
      return;
    }

    if (!contains(value)) {
      throw failException;
    }

    if (stamp == storeLevel) {

      if ((bounds.length >> 1) > 0) {
        put(bounds, 0, value, value);
      } else {
        throw new RuntimeException("Internal error in InternalDomain.inValue");
      }
      size = 1;

    } else {

      if (ASSERTS_ENABLED && stamp >= storeLevel) {
        throw new IllegalStateException("Assertion failed");
      }

      IntervalDomain result = new IntervalDomain(1);
      put(result.bounds, 0, value, value);
      result.size = 1;

      installResultDomain(result, storeLevel, v);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    v.domainHasChanged(GROUND);
  }

  @Override
  public int noIntervals() {

    return size;
  }

  /**
   * It specifies the position of the interval which contains specified value. Hybrid: linear check
   * for indices 0–1, then binary search over [2, size-1]. Interval-count frequency (approx.): size
   * 1 ~76%, 2 ~8%, 3 ~4%, 4 ~2%, others ~10%.
   *
   * @param value value for which an interval containing it is searched.
   * @return the position of the interval containing the specified value.
   */
  public int intervalNo(int value) {

    if (size > 0) {
      int i0Min = bounds[0];
      int i0Max = bounds[1];
      if (value >= i0Min && value <= i0Max) {
        return 0;
      }
    }
    if (size > 1) {
      int i1Min = bounds[2 * 1];
      int i1Max = bounds[2 * 1 + 1];
      if (value >= i1Min && value <= i1Max) {
        return 1;
      }
    }
    int lo = 2;
    int hi = size - 1;
    while (lo <= hi) {
      int mid = (lo + hi) >> 1;
      int iMin = bounds[2 * mid];
      int iMax = bounds[2 * mid + 1];
      if (value > iMax) {
        lo = mid + 1;
      } else if (value < iMin) {
        hi = mid - 1;
      } else {
        return mid;
      }
    }
    return -1;
  }

  @Override
  public Interval getInterval(int position) {

    if (ASSERTS_ENABLED && position >= size) {
      throw new IllegalStateException("Assertion failed");
    }

    return intervalAt(bounds, position);
  }

  @Override
  public void inComplement(int storeLevel, Var v, int complement) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    int counter = intervalNo(complement);

    if (counter == -1) {
      return;
    }
    ((IntVar) v).removingValue(complement);

    // a removed bound leaves the other one unchanged, as the domain does not become empty
    int boundEvent = complement == bounds[0] ? MIN_EVENT : MAX_EVENT;

    if (storeLevel == stamp) {

      if (bounds[2 * counter] == complement) {

        if (bounds[2 * counter + 1] != complement) {

          put(bounds, counter, complement + 1, bounds[2 * counter + 1]);

          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          if (singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          if (counter == 0) {
            v.domainHasChanged(boundEvent);
          } else {
            v.domainHasChanged(ANY);
          }
        } else {
          // if domain like this 1..3, 5, 7..10, and 5 being removed.

          if (singleton(complement)) {
            throw failException;
          }

          for (int i = counter; i < size - 1; i++) {
            move(bounds, i, bounds, i + 1);
          }

          size--;

          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          if (singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          // below size, instead of size-1 as size has been
          // just decreased, e.g. domain like 1..3, 5 and 5
          // being removed.

          if (counter == 0 || counter == size) {
            v.domainHasChanged(boundEvent);
          } else {
            v.domainHasChanged(ANY);
          }
        }
        return;
      }

      if (bounds[2 * counter + 1] == complement) {

        // domain like this 1..3, 5, 7..10, and 5 being
        // removed taken care of above.

        put(bounds, counter, bounds[2 * counter], complement - 1);

        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }

        if (singleton()) {
          v.domainHasChanged(GROUND);
          return;
        }

        if (counter == size - 1) {
          v.domainHasChanged(boundEvent);
        } else {
          v.domainHasChanged(ANY);
        }
        return;
      }

      if (size + 1 < (bounds.length >> 1)) {
        for (int i = size; i > counter + 1; i--) {
          move(bounds, i, bounds, i - 1);
        }
      } else {
        int[] updatedIntervals = new int[2 * (size + 1 + ALLOCATION_MARGIN)];
        System.arraycopy(bounds, 2 * 0, updatedIntervals, 2 * 0, 2 * (counter + 1));
        System.arraycopy(
            bounds, 2 * counter, updatedIntervals, 2 * (counter + 1), 2 * (size - counter));
        bounds = updatedIntervals;
      }

      int max = bounds[2 * counter + 1];
      put(bounds, counter, bounds[2 * counter], complement - 1);
      put(bounds, counter + 1, complement + 1, max);

      // One interval has been split, size increased by one.
      size++;

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

    } else {

      if (singleton(complement)) {
        throw failException;
      }

      if (ASSERTS_ENABLED && storeLevel <= stamp) {
        throw new IllegalStateException("Assertion failed");
      }

      IntervalDomain result = new IntervalDomain(this.size + 1);

      // variable obtains new domain, current one (this) becomes
      // previousDomain
      installResultDomain(result, storeLevel, v);

      if (bounds[2 * counter] == complement) {

        if (bounds[2 * counter + 1] != complement) {

          System.arraycopy(bounds, 2 * 0, result.bounds, 2 * 0, 2 * size);

          put(result.bounds, counter, complement + 1, result.bounds[2 * counter + 1]);

          result.size = size;

          if (ASSERTS_ENABLED && result.checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }
          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          if (counter == 0) {
            v.domainHasChanged(boundEvent);
          } else {
            v.domainHasChanged(ANY);
          }
        } else {
          // if domain like this 1..3, 5, 7..10, and 5 being removed.
          System.arraycopy(bounds, 2 * 0, result.bounds, 2 * 0, 2 * counter);

          System.arraycopy(
              bounds, 2 * (counter + 1), result.bounds, 2 * counter, 2 * (size - counter - 1));

          result.size = size - 1;

          if (ASSERTS_ENABLED && result.checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          if (counter == 0 || counter == size - 1) {
            v.domainHasChanged(boundEvent);
          } else {
            v.domainHasChanged(ANY);
          }
        }
        return;
      }

      if (bounds[2 * counter + 1] == complement) {

        // domain like this 1..3, 5, 7..10, and 5 being removed taken
        // care of above.

        System.arraycopy(bounds, 2 * 0, result.bounds, 2 * 0, 2 * size);

        put(result.bounds, counter, result.bounds[2 * counter], complement - 1);

        result.size = size;

        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }
        if (ASSERTS_ENABLED && result.checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(result.checkInvariants()));
        }

        if (result.singleton()) {
          v.domainHasChanged(GROUND);
          return;
        }
        if (counter == size - 1) {
          v.domainHasChanged(boundEvent);
        } else {
          v.domainHasChanged(ANY);
        }
        return;
      }

      // if domain like this 1..3 and value 2 being removed, or
      // 1..3, 5..7, 10..20, and value 6 being removed.

      // length of result is by default one longer than size of this.

      if (size != 1) {
        System.arraycopy(bounds, 2 * 0, result.bounds, 2 * 0, 2 * (counter + 1));
        System.arraycopy(
            bounds, 2 * counter, result.bounds, 2 * (counter + 1), 2 * (size - counter));
      }

      int max = bounds[2 * counter + 1];
      put(result.bounds, counter, bounds[2 * counter], complement - 1);
      put(result.bounds, counter + 1, complement + 1, max);

      result.size = size + 1;

      /*
       * result.modelConstraints = modelConstraints;
       * result.searchConstraints = searchConstraints; result.stamp =
       * storeLevel; result.previousDomain = this;
       * result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
       * result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
       * var.domain = result;
       */

    }
    v.domainHasChanged(ANY);
  }

  @Override
  public void inComplement(int storeLevel, Var v, int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (bounds[0] > max || bounds[2 * (size - 1) + 1] < min) {
      return;
    }

    int counter = firstIntervalEndingAtOrAfter(min);

    if (bounds[2 * counter] > max) {
      return;
    }

    if (min <= min() && max >= max()) {
      throw failException;
    }

    // the removed values do not cover both bounds, so at most one bound changes
    int boundEvent = min <= min() ? MIN_EVENT : MAX_EVENT;

    if (storeLevel == stamp) {

      int noRemoved = 0;

      if (bounds[2 * counter] < min) {
        // intervals[2 * counter]..min-1

        if (bounds[2 * counter + 1] > max) {
          // max+1..max of interval counter
          if (size < (bounds.length >> 1)) {
            // copy elements to make one hole for new interval

            for (int i = size; i > counter; i--) {
              move(bounds, i, bounds, i - 1);
            }

            put(bounds, counter + 1, max + 1, bounds[2 * counter + 1]);
            put(bounds, counter, bounds[2 * counter], min - 1);

          } else {
            // create new array and copy

            int[] oldIntervals = bounds;
            bounds = new int[2 * ((oldIntervals.length >> 1) + 5)];

            if (counter > 0) {
              System.arraycopy(oldIntervals, 2 * 0, bounds, 2 * 0, 2 * counter);
            }

            System.arraycopy(
                oldIntervals,
                2 * (counter + 1),
                bounds,
                2 * (counter + 2),
                2 * (size - counter - 1));

            put(bounds, counter + 1, max + 1, oldIntervals[2 * counter + 1]);
            put(bounds, counter, oldIntervals[2 * counter], min - 1);
          }
          size++;
          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          v.domainHasChanged(ANY);
        } else {
          // intervals[2 * counter + 1] <= max
          // intervals[2 * counter]..min-1

          put(bounds, counter, bounds[2 * counter], min - 1);

          int position = ++counter;

          while (position < size && bounds[2 * position + 1] <= max) {
            position++;
            noRemoved++;
          }

          if (noRemoved > 0) {

            for (int i = counter; i + noRemoved < size; i++) {
              move(bounds, i, bounds, i + noRemoved);
            }
          }

          size -= noRemoved;

          if (counter < size && bounds[2 * counter] <= max) {
            put(bounds, counter, max + 1, bounds[2 * counter + 1]);
          }

          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          if (singleton()) {
            v.domainHasChanged(GROUND);
          } else if (max() < min) {
            v.domainHasChanged(boundEvent);
          } else {
            v.domainHasChanged(ANY);
          }
        }

      } else {
        // intervals[2 * counter] >= min
        if (bounds[2 * counter + 1] > max) {
          // max+1..max of interval counter

          put(bounds, counter, max + 1, bounds[2 * counter + 1]);

        } else {
          // intervalAt(intervals, counter) is removed

          int position = counter;

          while (position < size && bounds[2 * position + 1] <= max) {
            position++;
            noRemoved++;
          }

          for (int i = counter; i + noRemoved < size; i++) {
            move(bounds, i, bounds, i + noRemoved);
          }

          size -= noRemoved;

          if (counter < size && bounds[2 * counter] <= max) {
            put(bounds, counter, max + 1, bounds[2 * counter + 1]);
          }
        }
        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }
        if (singleton()) {
          v.domainHasChanged(GROUND);
          return;
        }
        if (max() < min || max < min()) {
          v.domainHasChanged(boundEvent);
        } else {
          v.domainHasChanged(ANY);
        }
      }

    } else {

      if (ASSERTS_ENABLED && storeLevel <= stamp) {
        throw new IllegalStateException("Assertion failed");
      }

      IntervalDomain result = new IntervalDomain(this.size + 1);

      installResultDomain(result, storeLevel, v);
      result.size = size;

      int noRemoved = 0;

      System.arraycopy(bounds, 2 * 0, result.bounds, 2 * 0, 2 * counter);

      if (bounds[2 * counter] < min) {
        // intervals[2 * counter]..min-1

        if (bounds[2 * counter + 1] > max) {
          // max+1..max of interval counter
          // copy elements to make one hole for new interval

          if (size - counter >= 0) {
            System.arraycopy(
                bounds, 2 * counter, result.bounds, 2 * (counter + 1), 2 * (size - counter));
          }

          put(result.bounds, counter + 1, max + 1, bounds[2 * counter + 1]);
          put(result.bounds, counter, bounds[2 * counter], min - 1);

          result.size++;

          if (ASSERTS_ENABLED && result.checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }
          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          v.domainHasChanged(ANY);

        } else {

          put(result.bounds, counter, bounds[2 * counter], min - 1);

          int position = ++counter;

          while (position < size && bounds[2 * position + 1] <= max) {
            position++;
            noRemoved++;
          }

          for (int i = counter; i + noRemoved < size; i++) {
            move(result.bounds, i, bounds, i + noRemoved);
          }

          if (counter + noRemoved < size && bounds[2 * (counter + noRemoved)] <= max) {
            put(result.bounds, counter, max + 1, bounds[2 * (counter + noRemoved) + 1]);
          }

          result.size -= noRemoved;

          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          if (ASSERTS_ENABLED && result.checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
          } else if (result.max() < min) {
            v.domainHasChanged(boundEvent);
          } else {
            v.domainHasChanged(ANY);
          }
        }

      } else {

        if (bounds[2 * counter + 1] > max) {
          // max+1..max of interval counter

          if (size - (counter + 1) >= 0) {
            System.arraycopy(
                bounds,
                2 * (counter + 1),
                result.bounds,
                2 * (counter + 1),
                2 * (size - (counter + 1)));
          }

          put(result.bounds, counter, max + 1, bounds[2 * counter + 1]);

          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          if (ASSERTS_ENABLED && result.checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          if (result.max() < min || max < result.min()) {
            v.domainHasChanged(boundEvent);
          } else {
            v.domainHasChanged(ANY);
          }

        } else {
          // intervalAt(intervals, counter) is removed

          int position = counter;

          while (position < size && bounds[2 * position + 1] <= max) {
            position++;
            noRemoved++;
          }

          for (int i = counter; i + noRemoved < size; i++) {
            move(result.bounds, i, bounds, i + noRemoved);
          }

          result.size -= noRemoved;

          if (counter + noRemoved < size && bounds[2 * (counter + noRemoved)] <= max) {
            put(result.bounds, counter, max + 1, bounds[2 * (counter + noRemoved) + 1]);
          }

          if (ASSERTS_ENABLED && checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          if (ASSERTS_ENABLED && result.checkInvariants() != null) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
          } else if (result.max() < min || max < result.min()) {
            v.domainHasChanged(boundEvent);
          } else {
            v.domainHasChanged(ANY);
          }
        }
      }
    }
  }

  /**
   * {@inheritDoc}
   *
   * <p>Example: {1..4} + 3 = 4..7
   */
  @Override
  public void inShift(int storeLevel, Var v, IntDomain domain, int shift) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      inRuns(storeLevel, v, domain, shift);
      return;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && this.stamp > storeLevel) {
      throw new IllegalStateException("Assertion failed");
    }

    if (domain.isEmpty()) {
      throw failException;
    }

    if (ASSERTS_ENABLED && size == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      in(storeLevel, v, domain.min() + shift, domain.max() + shift);
      return;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {
      SmallDenseDomain result = ((SmallDenseDomain) domain).intersect(this, -shift);
      result.shift(shift);
      inSmallDense(storeLevel, v, result);
      return;
    }

    int inputSize = domain.noIntervals();
    int[] input = boundsOf(domain);

    int first = firstNotCovered(bounds, size, input, inputSize, shift);
    // no change
    if (first == size) {
      return;
    }

    int[] copy = new int[2 * (size + inputSize + ALLOCATION_MARGIN)];
    System.arraycopy(bounds, 0, copy, 0, 2 * first);
    int out = intersectInto(bounds, first, size, input, inputSize, shift, copy, first);

    if (out == 0) {
      throw failException;
    }

    installArrayResult(copy, out, storeLevel, v, narrowingEvent(copy, out, true));
  }

  @Override
  public int domainId() {
    return INTERVAL_DOMAIN_ID;
  }

  @Override
  public boolean isSparseRepresentation() {
    return false;
  }

  @Override
  public int leftElement(int intervalNo) {

    if (ASSERTS_ENABLED && intervalNo >= size) {
      throw new IllegalStateException("Assertion failed");
    }
    return bounds[2 * intervalNo];
  }

  @Override
  public int rightElement(int intervalNo) {

    if (ASSERTS_ENABLED && intervalNo >= size) {
      throw new IllegalStateException("Assertion failed");
    }
    return bounds[2 * intervalNo + 1];
  }

  /**
   * {@inheritDoc}
   *
   * <p>If domain is represented as a list of domains, the domain pointer within variable will be
   * updated.
   */
  @Override
  public void removeLevel(int level, Var v) {

    if (ASSERTS_ENABLED && this.stamp > level) {
      throw new IllegalStateException("Assertion failed");
    }

    if (this.stamp == level) {

      ((IntVar) v).domain = this.previousDomain;
    }

    if (ASSERTS_ENABLED && ((IntVar) v).domain.stamp >= level) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  @Override
  public IntDomain recentDomainPruning(int storeLevel) {

    if (previousDomain == null) {
      return emptyDomain;
    }

    if (stamp < storeLevel) {
      return emptyDomain;
    }

    return previousDomain.subtract(this);
  }

  @Override
  public int sizeConstraintsOriginal() {
    IntDomain domain = this;

    while (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain dom = (IntervalDomain) domain;

      if (dom.previousDomain != null) {
        domain = dom.previousDomain;
      } else {
        break;
      }
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {
      return Arrays.stream(domain.modelConstraintsToEvaluate).sum();
    } else {
      return domain.sizeConstraintsOriginal();
    }
  }

  @Override
  public int previousValue(int value) {

    // the last interval which starts before value
    int m = value == Integer.MIN_VALUE ? -1 : firstIntervalStartingAfter(value - 1) - 1;
    if (m < 0) {
      return value;
    }

    int iMax = bounds[2 * m + 1];
    if (iMax >= value) {
      return value - 1;
    }
    return iMax;
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

    if (bounds.length < 2 * size) {
      return "size of the domain is not set up properly";
    }

    if (this.bounds[0] > this.bounds[2 * (size - 1) + 1]) {
      return "Min value is larger than max value " + this;
    }

    for (int i = 0; i < size; i++) {
      if (this.bounds[2 * i] > this.bounds[2 * i + 1]) {
        return "One of the bounds not properly build. Min value is larger than max value " + this;
      }
    }

    for (int i = 0; i < size - 1; i++) {
      if (this.bounds[2 * i + 1] + 1 == this.bounds[2 * (i + 1)]) {
        return "Two consequtive bounds should be merged. Improper representation" + this;
      }
    }

    // Fine, all invariants hold.
    return null;
  }

  @Override
  public void subtractAdapt(int value) {

    int counter = intervalNo(value);

    if (counter == -1) {
      return;
    }

    if (bounds[2 * counter] == value) {

      if (bounds[2 * counter + 1] != value) {

        put(bounds, counter, value + 1, bounds[2 * counter + 1]);

        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }

      } else {
        // if domain like this 1..3, 5, 7..10, and 5 being removed.

        for (int i = counter; i < size - 1; i++) {
          move(bounds, i, bounds, i + 1);
        }

        size--;

        // below size, instead of size-1 as size has been
        // just decreased, e.g. domain like 1..3, 5, 7..9 and 5
        // being removed.

      }
      return;
    }

    if (bounds[2 * counter + 1] == value) {

      // domain like this 1..3, 5, 7..10, and 5 being
      // removed taken care of above.

      put(bounds, counter, bounds[2 * counter], value - 1);

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      return;
    }

    if (size + 1 < (bounds.length >> 1)) {
      for (int i = size; i > counter + 1; i--) {
        move(bounds, i, bounds, i - 1);
      }
    } else {
      int[] updatedIntervals = new int[2 * (size + 1 + ALLOCATION_MARGIN)];
      System.arraycopy(bounds, 2 * 0, updatedIntervals, 2 * 0, 2 * (counter + 1));
      System.arraycopy(
          bounds, 2 * counter, updatedIntervals, 2 * (counter + 1), 2 * (size - counter));
      bounds = updatedIntervals;
    }

    int max = bounds[2 * counter + 1];
    put(bounds, counter, bounds[2 * counter], value - 1);
    put(bounds, counter + 1, value + 1, max);

    // One interval has been split, size increased by one.
    size++;

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  @Override
  public void subtractAdapt(int minValue, int maxValue) {

    int current = firstIntervalEndingAtOrAfter(minValue);

    if (current == size) {
      return;
    }

    if (minValue <= bounds[2 * current]) {

      if (maxValue < bounds[2 * current]) {
        return;
      }

      // removing will not create more intervals.
      if (bounds[2 * current + 1] > maxValue) {

        put(bounds, current, maxValue + 1, bounds[2 * current + 1]);

        if (ASSERTS_ENABLED && checkInvariants() != null) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }

      } else {
        // at least one complete interval is being removed.

        int maxCurrent = current;
        while (maxCurrent < size && bounds[2 * maxCurrent + 1] <= maxValue) {
          maxCurrent++;
        }

        if (maxCurrent == size) {
          size = current;
          return;
        }

        if (maxValue >= bounds[2 * maxCurrent]) {
          put(bounds, maxCurrent, maxValue + 1, bounds[2 * maxCurrent + 1]);
        }

        int i = current;
        for (; maxCurrent < size; i++, maxCurrent++) {
          move(bounds, i, bounds, maxCurrent);
        }

        size = i;
      }
    } else {

      // minValue > intervals[2 * current]

      if (maxValue < bounds[2 * current + 1]) {
        // one additional interval is being created.

        if ((bounds.length >> 1) <= size + 1) {
          // not enough space to insert new interval.
          int[] newIntervals = new int[2 * ((bounds.length >> 1) * 2)];
          System.arraycopy(bounds, 2 * 0, newIntervals, 2 * 0, 2 * size);
          bounds = newIntervals;
        }

        for (int i = size; i > current; i--) {
          move(bounds, i, bounds, i - 1);
        }

        put(bounds, current, bounds[2 * current], minValue - 1);
        put(bounds, current + 1, maxValue + 1, bounds[2 * (current + 1) + 1]);

        size++;

      } else {
        // minValue > intervals[2 * current]
        // maxValue >= intervals[2 * current + 1]

        // at least one complete interval is being removed.
        put(bounds, current, bounds[2 * current], minValue - 1);
        current++;

        int maxCurrent = current;
        while (maxCurrent < size && bounds[2 * maxCurrent + 1] <= maxValue) {
          maxCurrent++;
        }

        if (maxCurrent == size) {
          size = current;
          return;
        }

        if (bounds[2 * maxCurrent] <= maxValue) {
          put(bounds, maxCurrent, maxValue + 1, bounds[2 * maxCurrent + 1]);
        }

        int i = current;
        for (; maxCurrent < size; i++, maxCurrent++) {
          move(bounds, i, bounds, maxCurrent);
        }

        size = i;
      }
    }
  }

  @Override
  public int intersectAdapt(IntDomain domain) {

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      return intersectAdapt(intersectRuns(this, domain, 0));
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == 0) {
      return NONE;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      if (input.isEmpty()) {
        size = 0;
        return GROUND;
      }

      if (input.minBound == this.min()
          && input.max() == this.max()
          && input.getSize() == this.getSize()
          && input.minBound + input.getSize() - 1 == input.max()) {
        return NONE;
      }

      IntervalDomain result = new IntervalDomain(this.size);

      int current = input.minBound;
      long bits = input.bits;
      int position = 0;

      while (position < size && bits != 0) {

        if (current < bounds[2 * position]) {
          // a shift by 64 or more would wrap around, all remaining bits are below the interval
          long gap = (long) bounds[2 * position] - current;
          bits = gap >= 64 ? 0 : bits << gap;
          current = bounds[2 * position];
          continue;
        }

        if (bits > 0) {
          bits = bits << 1;
          current++;
          continue;
        }

        if (bounds[2 * position + 1] < current) {
          position++;
          continue;
        }

        int min = current;

        do {
          bits = bits << 1;
          current++;
        } while (bits < 0 && current <= bounds[2 * position + 1]);

        result.unionAdapt(min, current - 1);
      }

      if (ASSERTS_ENABLED && !this.intersect(input.toIntervalDomain()).eq(result)) {
        throw new IllegalStateException(
            String.valueOf("Improper intersection " + this + "d: " + domain + "r: " + result));
      }

      if (result.isEmpty()) {
        size = 0;
        return GROUND;
      }

      if (result.eq(this)) {
        return NONE;
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

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      if (domain.isEmpty()) {
        size = 0;
        return GROUND;
      }
      return intersectAdapt(domain.min(), domain.max());
    }

    if (domain.isEmpty()) {
      size = 0;
      return GROUND;
    }

    int inputSize = domain.noIntervals();
    int[] input = boundsOf(domain);

    int first = firstNotCovered(bounds, size, input, inputSize, 0);
    // no change
    if (first == size) {
      return NONE;
    }

    int[] copy = new int[2 * (size + inputSize + ALLOCATION_MARGIN)];
    System.arraycopy(bounds, 0, copy, 0, 2 * first);
    int out = intersectInto(bounds, first, size, input, inputSize, 0, copy, first);

    if (out == 0) {
      size = 0;
      return GROUND;
    }

    int returnedEvent = narrowingEvent(copy, out, false);
    bounds = copy;
    size = out;

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

    if (max < bounds[0]) {
      size = 0;
      return GROUND;
    }

    int currentMax = bounds[2 * (size - 1) + 1];
    if (min > currentMax) {
      size = 0;
      return GROUND;
    }

    if (min <= bounds[0] && max >= currentMax) {
      return NONE;
    }

    IntervalDomain result = new IntervalDomain(size + 1);
    int pointer = 0;

    // pointer is always smaller than size as domains intersect
    pointer = firstIntervalEndingAtOrAfter(min);

    if (bounds[2 * pointer] > max) {
      size = 0;
      return GROUND;
    }

    if (bounds[2 * pointer] >= min) {
      if (bounds[2 * pointer + 1] <= max) {
        result.appendInterval(bounds[2 * pointer], bounds[2 * pointer + 1]);
      } else {
        result.appendInterval(bounds[2 * pointer], max);
      }
    } else if (bounds[2 * pointer + 1] <= max) {
      result.appendInterval(min, bounds[2 * pointer + 1]);
    } else {
      result.appendInterval(min, max);
    }

    pointer++;

    while (pointer < size) {
      if (bounds[2 * pointer + 1] <= max) {
        result.appendInterval(bounds[2 * pointer], bounds[2 * pointer + 1]);
        pointer++;
      } else {
        break;
      }
    }

    if (pointer < size && bounds[2 * pointer] <= max) {
      result.appendInterval(bounds[2 * pointer], max);
    }

    adoptIntervalsFrom(result);

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result.singleton() ? GROUND : BOUND;
  }

  private int sizeOfIntersectionSparse(IntDomain domain) {
    int count = 0;
    ValueEnumeration enumer = domain.valueEnumeration();
    while (enumer.hasMoreElements()) {
      if (this.contains(enumer.nextElement())) {
        count++;
      }
    }
    return count;
  }

  @Override
  public int sizeOfIntersection(IntDomain domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.domainId() == LAZY_BIT_SET_DOMAIN_ID) {
      return intersectRuns(this, domain, 0).getSize();
    }

    if (domain.isEmpty()) {
      return 0;
    }

    if (domain.isSparseRepresentation()) {
      return sizeOfIntersectionSparse(domain);
    }

    int inputSize = domain.noIntervals();
    int[] input = boundsOf(domain);
    int count = 0;
    int j = 0;
    for (int i = 0; i < size && j < inputSize; ) {
      int lo = Math.max(bounds[2 * i], input[2 * j]);
      int hi = Math.min(bounds[2 * i + 1], input[2 * j + 1]);
      count += Math.max(0, hi - lo + 1);
      int step = Integer.compare(bounds[2 * i + 1], input[2 * j + 1]);
      i += step <= 0 ? 1 : 0;
      j += step >= 0 ? 1 : 0;
    }
    return count;
  }

  @Override
  public int getElementAt(int index) {

    if (ASSERTS_ENABLED && index < 0) {
      throw new IllegalStateException(String.valueOf("The index can not be negative"));
    }
    if (ASSERTS_ENABLED && index >= this.getSize()) {
      throw new IllegalStateException(
          String.valueOf(
              "The domain does not have so many elements as specified by the index equal to "
                  + index));
    }

    int counter = 0;

    int currentRange = bounds[2 * counter + 1] - bounds[2 * counter];

    while (index > currentRange) {
      index -= currentRange + 1;
      counter++;
      if (counter < size) {
        currentRange = bounds[2 * counter + 1] - bounds[2 * counter];
      } else {
        throw new RuntimeException(
            "The domain does not have an element as specified by the index " + index);
      }
    }

    return bounds[2 * counter] + index;
  }

  @Override
  public int getRandomValue() {

    int min = min();
    int size = max() - min();

    if (size == 0) {
      return min;
    }

    int value = min + Store.getRandom().nextInt(size);
    int domainSize = noIntervals();
    if (domainSize == 1) {
      return value;
    }

    for (int i = 0; i < domainSize; i++) {

      int currentMin = leftElement(i);
      int currentMax = rightElement(i);

      if (value >= currentMin) {
        if (value <= currentMax) {
          return value;
        }
      } else if (currentMin - value < value - rightElement(i - 1)) {
        return currentMin;
      } else {
        return rightElement(i - 1);
      }
    }

    if (ASSERTS_ENABLED) {
      throw new IllegalStateException(
          String.valueOf("Error in IndomainRandom. " + "Domain " + this + " value " + value));
    }
    // Only to satisfy java compiler, should not be reached
    return Integer.MAX_VALUE;
  }
}
