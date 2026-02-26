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
   * Extra capacity added to size-based Interval[] allocations for headroom and fewer resizes. Helps
   * to reduce the resize operations by 75%. Used in all in / inMin / inMax / inValue /
   * in(IntDomain) / inComplement propagation methods. Not used for length-based allocations (e.g.
   * intervals.length + 5) to avoid unbounded growth.
   */
  private static final int ALLOCATION_MARGIN = 1;

  /** The values of the domain are encoded as a list of intervals. */
  public Interval[] intervals;

  /** It specifies number of intervals needed to encode the domain. */
  public int size;

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
    if (source.size <= intervals.length) {
      System.arraycopy(source.intervals, 0, intervals, 0, source.size);
    } else {
      intervals = new Interval[source.size + ALLOCATION_MARGIN];
      System.arraycopy(source.intervals, 0, intervals, 0, source.size);
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
    if (size >= intervals.length) {
      Interval[] old = intervals;
      intervals = new Interval[old.length + 5];
      System.arraycopy(old, 0, intervals, 0, size);
    }
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
        sb.append(intervals[e]);
        if (e + 1 < size) {
          sb.append(", ");
        }
      }
      sb.append("}");
    } else {
      sb.append(intervals[0]);
    }
  }

  /**
   * Installs a computed interval array as the new domain on a variable, handling both the in-place
   * (stamp==storeLevel) and copy-on-write cases. Fires a GROUND or BOUND event as appropriate.
   *
   * @param copy the new intervals array
   * @param out the number of valid intervals in copy
   * @param storeLevel the current store level
   * @param v the variable to update
   */
  private void installArrayResult(Interval[] copy, int out, int storeLevel, Var v) {
    IntervalDomain result = null;
    if (stamp == storeLevel) {
      intervals = copy;
      size = out;
    } else {
      result = new IntervalDomain(copy, out);
      installResultDomain(result, storeLevel, v);
    }
    IntervalDomain effective = stamp == storeLevel ? this : result;
    if (ASSERTS_ENABLED && !(effective.checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(effective.checkInvariants()));
    }
    v.domainHasChanged(effective.singleton() ? GROUND : BOUND);
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
    intervals = new Interval[size + ALLOCATION_MARGIN];
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

    if (ASSERTS_ENABLED && !(min <= max)) {
      throw new IllegalStateException(
          String.valueOf("Min value can not be greater than max value"));
    }

    intervals = new Interval[5 + ALLOCATION_MARGIN];
    searchConstraints = null;
    searchConstraintsToEvaluate = 0;
    previousDomain = null;
    searchConstraintsCloned = false;
    intervals[0] = new Interval(min, max);
    this.size = 1;
  }

  /**
   * Creates a domain that takes ownership of the given intervals array. The array must hold sorted,
   * disjoint intervals in {@code [0..size-1]}; slots at {@code size} and beyond are ignored.
   *
   * @param intervals array of intervals (caller transfers ownership)
   * @param size number of valid intervals
   */
  public IntervalDomain(Interval[] intervals, int size) {
    this.intervals = intervals;
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    ensureCapacity();

    intervals[size++] = i;

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  @Override
  public void unionAdapt(int min, int max) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == 0) {

      intervals = new Interval[1 + ALLOCATION_MARGIN];
      intervals[size++] = new Interval(min, max);

    } else {

      int i = 0;
      for (; i < size; i++) {
        // i - position of the interval which touches with or intersects with min..max
        if ((max + 1 >= intervals[i].min() && max <= intervals[i].max() + 1)
            || (min + 1 >= intervals[i].min() && min <= intervals[i].max() + 1)
            || (min <= intervals[i].min() && intervals[i].max() <= max)) {
          break;
        }
        if (max + 1 < intervals[i].min()) {
          // interval is inserted at position i

          ensureCapacity();

          // empty intervals are available
          Interval temp = intervals[i];
          intervals[i] = new Interval(min, max);

          int t = size;
          while (t > i) {
            intervals[t] = intervals[t - 1];
            t--;
          }
          intervals[i + 1] = temp;
          size++;

          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          if (ASSERTS_ENABLED && !(contains(min))) {
            throw new IllegalStateException(String.valueOf(ASSERT_MIN_ADDED));
          }
          if (ASSERTS_ENABLED && !(contains(max))) {
            throw new IllegalStateException(String.valueOf(ASSERT_MAX_ADDED));
          }

          return;
        }
      }

      if (i == size) {

        ensureCapacity();

        intervals[size] = new Interval(min, max);
        size++;

        if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }
        if (ASSERTS_ENABLED && !(contains(min))) {
          throw new IllegalStateException(String.valueOf(ASSERT_MIN_ADDED));
        }
        if (ASSERTS_ENABLED && !(contains(max))) {
          throw new IllegalStateException(String.valueOf(ASSERT_MAX_ADDED));
        }

        return;
      }

      int newMin;
      // interval(min, max) intersects with current domain
      if (min < intervals[i].min()) {
        newMin = min;
      } else {
        newMin = intervals[i].min();
      }

      int target = i;
      int newMax;

      while (target < size && max >= intervals[target].max()) {
        target++;
      }

      if (target == size) {
        newMax = max;
      } else if (intervals[target].min() > max + 1) {
        newMax = max;
      } else {
        newMax = intervals[target].max();
        target++;
      }

      intervals[i] = new Interval(newMin, newMax);

      while (target < size) {
        intervals[++i] = intervals[target++];
      }

      while (size > i + 1) {
        intervals[--size] = null;
      }
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(contains(min))) {
      throw new IllegalStateException(String.valueOf(ASSERT_MIN_ADDED));
    }
    if (ASSERTS_ENABLED && !(contains(max))) {
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (intervals[size - 1].max() + 1 == i) {
      intervals[size - 1] = new Interval(intervals[size - 1].min(), i);
    } else {
      ensureCapacity();
      intervals[size] = new Interval(i, i);
      size++;
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  private void addDomFromIntervalDomain(IntervalDomain d) {
    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (size == 0) {
      if (intervals == null || intervals.length < d.intervals.length) {
        intervals = new Interval[d.intervals.length];
      }
      System.arraycopy(d.intervals, 0, intervals, 0, d.size);
      size = d.size;
    } else {
      for (int i = 0; i < d.size; i++) {
        unionAdapt(d.intervals[i].min(), d.intervals[i].max());
      }
    }
    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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
    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    unionAdapt(domain.min(), domain.max());
    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {
      addDomFromIntervalDomain((IntervalDomain) domain);
      return;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      addDomForBoundDomain(domain);
      return;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {
      this.addDom(((SmallDenseDomain) domain).toIntervalDomain());
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
      while (i < size && intervals[i].max() < next) {
        i++;
      }
      if (i == size) {
        if (ASSERTS_ENABLED && !(!isIntersecting(input.toIntervalDomain()))) {
          throw new IllegalStateException(String.valueOf(IS_INTERSECTING_NOT_IMPLEMENTED));
        }
        return false;
      }
      if (next >= intervals[i].min()) {
        if (ASSERTS_ENABLED && !(isIntersecting(input.toIntervalDomain()))) {
          throw new IllegalStateException(String.valueOf(IS_INTERSECTING_NOT_IMPLEMENTED));
        }
        return true;
      }
    }
    if (ASSERTS_ENABLED && !(!isIntersecting(input.toIntervalDomain()))) {
      throw new IllegalStateException(String.valueOf(IS_INTERSECTING_NOT_IMPLEMENTED));
    }
    return false;
  }

  @Override
  public boolean isIntersecting(IntDomain domain) {

    if (domain.isEmpty()) {
      return false;
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      IntervalDomain intervalDomain = (IntervalDomain) domain;

      int pointer1 = 0;
      int pointer2 = 0;

      int size2 = intervalDomain.size;

      if (size == 0 || size2 == 0) {
        return false;
      }

      Interval interval1 = intervals[pointer1];
      Interval interval2 = intervalDomain.intervals[pointer2];

      while (true) {
        if (interval1.max() < interval2.min()) {
          pointer1++;
          if (pointer1 < size) {
            interval1 = intervals[pointer1];
          } else {
            break;
          }
        } else if (interval2.max() < interval1.min()) {
          pointer2++;
          if (pointer2 < size2) {
            interval2 = intervalDomain.intervals[pointer2];
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

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      return max() >= domain.min() && domain.max() >= min();
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
        return isIntersecting(((SmallDenseDomain) domain).toIntervalDomain());
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    int i = 0;
    while (i < size && intervals[i].max() < min) {
      i++;
    }

    return i != size && intervals[i].min() <= max;
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain cloned = new IntervalDomain(this.intervals.length);

    System.arraycopy(intervals, 0, cloned.intervals, 0, size);

    cloned.size = size;

    return cloned;
  }

  @Override
  public IntervalDomain copy() {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
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

      Interval interval1 = intervals[0];
      Interval interval2 = domain.getInterval(0);

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

        interval2 = domain.getInterval(i2);
      }
    }
  }

  @Override
  public boolean contains(int value) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    // binary search algorithm
    int l = 0;
    int r = size - 1;

    while (l <= r) {
      // but shift right by one position does it also and it is faster ;)
      int m = (l + r) >> 1;
      Interval i = intervals[m];

      if (value > i.max()) {
        l = m + 1;
      } else if (value >= i.min()) {
        return true;
      } else {
        r = m - 1;
      }
    }

    return false;
  }

  @Override
  public boolean contains(int min, int max) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    for (int m = 0; m < size; m++) {
      Interval i = intervals[m];
      if (i.max() >= max && min >= i.min()) {
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain result = new IntervalDomain(size + 1);
    if (min() != MIN_INT) {
      result.unionAdapt(new Interval(MIN_INT, intervals[0].min() - 1));
    }

    for (int i = 0; i < size - 1; i++) {
      result.unionAdapt(new Interval(intervals[i].max() + 1, intervals[i + 1].min() - 1));
    }

    if (max() != MAX_INT) {
      result.unionAdapt(new Interval(max() + 1, MAX_INT));
    }

    if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
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
  public int nextValue(int value) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    for (int m = 0; m < size; m++) {
      Interval i = intervals[m];
      if (i.max() > value) {
        if (value >= i.min() - 1) {
          return value + 1;
        } else {
          return i.min();
        }
      }
    }

    return value;
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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
        if (!intervals[i].eq(domain.getInterval(i))) {
          return false;
        }
      }
      return true;
    }
  }

  @Override
  public int getSize() {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    int n = 0;

    for (int i = 0; i < size; i++) {
      n = n + intervals[i].max() - intervals[i].min() + 1;
    }

    return n;
  }

  @Override
  public IntDomain intersect(IntDomain domain) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.isEmpty()) {
      return emptyDomain;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      return intersect(domain.min(), domain.max());
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      return this.intersect(input.toIntervalDomain());
    }

    if (domain.isSparseRepresentation()) {
      return intersectFromSparse(domain);
    } else {

      IntervalDomain temp = new IntervalDomain(size);

      int pointer1 = 0;
      int pointer2 = 0;

      int size1 = size;

      if (size1 == 0 || domain.noIntervals() == 0) {
        return temp;
      }

      Interval interval1 = intervals[pointer1];
      Interval interval2 = domain.getInterval(pointer2);

      while (true) {
        if (interval1.max() < interval2.min()) {
          pointer1++;
          if (pointer1 < size1) {
            interval1 = intervals[pointer1];
          } else {
            break;
          }
        } else if (interval2.max() < interval1.min()) {
          pointer2++;
          if (pointer2 < domain.noIntervals()) {
            interval2 = domain.getInterval(pointer2);
          } else {
            break;
          }
        } else
        // interval1.max >= interval2.min
        // interval2.max >= interval1.min
        if (interval1.min() <= interval2.min()) {

          if (interval1.max() <= interval2.max()) {

            temp.unionAdapt(interval2.min(), interval1.max());
            pointer1++;
            if (pointer1 < size1) {
              interval1 = intervals[pointer1];
            } else {
              break;
            }
          } else {
            temp.unionAdapt(interval2.min(), interval2.max());
            pointer2++;
            if (pointer2 < domain.noIntervals()) {
              interval2 = domain.getInterval(pointer2);
            } else {
              break;
            }
          }

        } else {
          // interval1.max >= interval2.min
          // interval2.max >= interval1.min
          // interval1.min > interval2.min
          if (interval2.max() <= interval1.max()) {
            temp.unionAdapt(interval1.min(), interval2.max());
            pointer2++;
            if (pointer2 < domain.noIntervals()) {
              interval2 = domain.getInterval(pointer2);
            } else {
              break;
            }
          } else {
            temp.unionAdapt(interval1.min(), interval1.max());
            pointer1++;
            if (pointer1 < size1) {
              interval1 = intervals[pointer1];
            } else {
              break;
            }
          }
        }
      }

      return temp;
    }
  }

  @Override
  public IntDomain intersect(int min, int max) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain temp = new IntervalDomain(size);

    if (size == 0) {
      return this;
    }

    int pointer1 = 0;

    Interval interval1 = intervals[pointer1];

    while (true) {
      if (interval1.max() < min) {
        pointer1++;
        if (pointer1 < size) {
          interval1 = intervals[pointer1];
        } else {
          break;
        }
      } else if (max < interval1.min()) {
        break;
      } else
      // interval1.max >= interval2.min
      // interval2.max >= interval1.min
      if (interval1.min() <= min) {

        if (interval1.max() <= max) {

          temp.unionAdapt(new Interval(min, interval1.max()));
          pointer1++;
          if (pointer1 < size) {
            interval1 = intervals[pointer1];
          } else {
            break;
          }
        } else {
          temp.unionAdapt(new Interval(min, max));
          break;
        }

      } else {
        // interval1.max >= interval2.min
        // interval2.max >= interval1.min
        // interval1.min > interval2.min
        if (max <= interval1.max()) {
          temp.unionAdapt(new Interval(interval1.min(), max));
          // pointer2++;
          break;
        } else {
          temp.unionAdapt(new Interval(interval1.min(), interval1.max()));
          pointer1++;
          if (pointer1 < size) {
            interval1 = intervals[pointer1];
          } else {
            break;
          }
        }
      }
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(temp.checkInvariants() == null)) {
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && !(size != 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    return intervals[size - 1].max();
  }

  @Override
  public int min() {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && !(size != 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    return intervals[0].min();
  }

  /**
   * {1..4} * 6 = {6, 12, 18, 24}
   *
   * @param mul the multiplier constant.
   * @return the domain after multiplication.
   */
  public IntDomain multiply(int mul) {

    if (ASSERTS_ENABLED && !(mul != 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    IntervalDomain temp = new IntervalDomain(getSize() * mul);

    if (mul > 0) {

      for (int m = 0; m < size; m++) {
        Interval i1 = intervals[m];
        for (int i = i1.min(); i <= i1.max(); i++) {
          int value = i * mul;
          temp.unionAdapt(new Interval(value, value));
        }
      }

    } else {

      for (int m = size - 1; m >= 0; m--) {
        Interval i1 = intervals[m];
        for (int i = i1.max(); i >= i1.min(); i--) {
          int value = i * mul;
          temp.unionAdapt(new Interval(value, value));
        }
      }
    }
    if (ASSERTS_ENABLED && !(temp.checkInvariants() == null)) {
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && !(position < size)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(position >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    size--;

    while (position < size) {
      intervals[position] = intervals[position + 1];
      position++;
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  @Override
  public void setDomain(IntDomain domain) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain intervalDomain = (IntervalDomain) domain;

      size = intervalDomain.size;

      intervals = new Interval[intervalDomain.intervals.length];
      System.arraycopy(intervalDomain.intervals, 0, intervals, 0, size);

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      return;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {

      size = 1;

      intervals = new Interval[1 + ALLOCATION_MARGIN];
      intervals[0] = new Interval(domain.min(), domain.max());

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
    intervals[0] = new Interval(min, max);
  }

  @Override
  public boolean singleton() {
    return size == 1 && intervals[0].min() == intervals[0].max();
  }

  @Override
  public boolean singleton(int c) {
    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    return size == 1 && intervals[0].min() == c && c == intervals[0].max();
  }

  @Override
  public IntDomain subtract(int value) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain result = cloneLight();

    int pointer1 = 0;

    if (size == 0) {
      return result;
    }

    Interval interval1 = intervals[pointer1];

    while (pointer1 < size && interval1.max() < value) {
      pointer1++;
      if (pointer1 < size) {
        interval1 = intervals[pointer1];
      }
    }

    if (pointer1 < size && interval1.min() <= value) {

      if (interval1.min() != value) {

        int oldMax = interval1.max();
        // replace min..max with interval1.min..value-1
        result.intervals[pointer1] = new Interval(interval1.min(), value - 1);
        pointer1++;

        if (value != oldMax) {
          // add domain value+1..oldMax
          result.unionAdapt(value + 1, oldMax);
          pointer1++;
        }

      } else if (interval1.max() != value) {
        // replace value..max with value+1..interval1.max
        result.intervals[pointer1] = new Interval(value + 1, interval1.max());
        pointer1++;
      } else {
        result.removeInterval(pointer1);
      }
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
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

  @Override
  public IntDomain subtract(IntDomain domain) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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
    } else {

      if (domain.noIntervals() == 0) {
        return cloneLight();
      }

      IntervalDomain result = new IntervalDomain();

      result.intervals = new Interval[size + 1 + ALLOCATION_MARGIN];

      int i1 = 0;
      int i2 = 0;

      Interval currentDomain1 = intervals[i1];
      Interval currentDomain2 = domain.getInterval(i2);

      boolean minIncluded = false;

      int max2 = domain.noIntervals();

      while (true) {

        if (currentDomain1.max() < currentDomain2.min()) {
          result.unionAdapt(currentDomain1);
          i1++;
          if (i1 == size) {
            break;
          }
          currentDomain1 = intervals[i1];
          minIncluded = false;
          continue;
        }

        if (currentDomain2.max() < currentDomain1.min()) {
          i2++;
          if (i2 == max2) {
            break;
          }
          currentDomain2 = domain.getInterval(i2);
          continue;
        }

        if (currentDomain1.min() >= currentDomain2.min()) {

          if (currentDomain1.max() <= currentDomain2.max()) {
            // Skip current interval of i1 completely
            i1++;
            if (i1 == size) {
              break;
            }
            currentDomain1 = intervals[i1];
            minIncluded = false;
          } else {

            // interval of dom2 ends before interval of dom1 ends
            // currentDomain2.max+1 .. currentDomain1.max
            // BUT next currentdomain2.min needs to be larger than
            // currentDomain1.max

            int oldMax = currentDomain2.max();
            i2++;
            if (i2 != max2) {
              currentDomain2 = domain.getInterval(i2);
            }

            if (i2 == max2 || currentDomain2.min() > currentDomain1.max()) {
              result.unionAdapt(new Interval(oldMax + 1, currentDomain1.max()));
              i1++;
              if (i1 == size) {
                break;
              }
              currentDomain1 = intervals[i1];
              minIncluded = false;

              if (i2 == max2) {
                break;
              }
            } else {

              result.unionAdapt(new Interval(oldMax + 1, currentDomain2.min() - 1));
              minIncluded = true;
            }
          }

        } else { // currentDomain1.min < currentDomain2.min)

          if (currentDomain1.max() <= currentDomain2.max()) {

            if (!minIncluded) {
              if (currentDomain1.max() >= currentDomain2.min()) {
                result.unionAdapt(new Interval(currentDomain1.min(), currentDomain2.min() - 1));
              } else {
                result.unionAdapt(new Interval(currentDomain1.min(), currentDomain1.max()));
              }
            }

            i1++;
            if (i1 == size) {
              break;
            }
            currentDomain1 = intervals[i1];
            minIncluded = false;
          } else {

            // interval of dom2 ends before interval of dom1 ends
            // currentDomain2.max+1 .. currentDomain1.max
            // BUT next currentdomain2.min needs to be larger than
            // currentDomain1.max

            if (!minIncluded) {
              result.unionAdapt(new Interval(currentDomain1.min(), currentDomain2.min() - 1));
              minIncluded = true;
            }

            int oldMax = currentDomain2.max();
            i2++;
            if (i2 != max2) {
              currentDomain2 = domain.getInterval(i2);
            }

            if (i2 == max2 || currentDomain2.min() > currentDomain1.max()) {
              result.unionAdapt(new Interval(oldMax + 1, currentDomain1.max()));
              i1++;
              if (i1 == size) {
                break;
              }
              currentDomain1 = intervals[i1];
              minIncluded = false;

              if (i2 == max2) {
                break;
              }
            } else {

              result.unionAdapt(new Interval(oldMax + 1, currentDomain2.min() - 1));
            }
          }
        }
      }

      while (i1 < size) {
        result.unionAdapt(intervals[i1]);
        i1++;
      }

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      return result;
    }
  }

  @Override
  public IntervalDomain subtract(int min, int max) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && !(min <= max)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (size == 0) {
      return emptyDomain;
    }

    // interval under the analysis
    int i1 = 0;
    // place for next interval in subtracted domain
    Interval currentInterval1 = intervals[i1];

    IntervalDomain result = new IntervalDomain(intervals.length + 1);

    while (true) {

      if (currentInterval1.max() < min) {
        result.unionAdapt(intervals[i1]);
        i1++;
        if (i1 == size) {
          break;
        }
        currentInterval1 = intervals[i1];
        continue;
      }

      if (max < currentInterval1.min()) {
        break;
      }

      if (currentInterval1.min() >= min) {

        // currentDomain1.max >= min
        // max >= currentDomain1.min

        if (currentInterval1.max() <= max) {
          // Skip current interval of i1 completely
          i1++;
          if (i1 == size) {
            break;
          }
          currentInterval1 = intervals[i1];

        } else {

          // interval of dom2 ends before interval of dom1 ends
          // currentDomain2.max+1 .. currentDomain1.max
          // BUT next currentdomain2.min needs to be larger than
          // currentDomain1.max

          result.unionAdapt(new Interval(max + 1, currentInterval1.max()));

          i1++;
          break;
        }
      } else {

        if (currentInterval1.max() <= max) {

          result.unionAdapt(new Interval(currentInterval1.min(), min - 1));

          i1++;

          if (i1 == size) {
            break;
          }
          currentInterval1 = intervals[i1];
          // next intervals of the domain may be before max.

        } else {

          // interval of min..max ends before interval of dom1 ends
          // max+1 .. currentDomain1.max

          result.unionAdapt(currentInterval1.min(), min - 1);
          result.unionAdapt(max + 1, currentInterval1.max());

          i1++;
          break;
        }
      }
    }

    for (int i = i1; i < size; i++) {
      result.unionAdapt(intervals[i]);
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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

      Interval currentDomain1 = intervals[i1];
      Interval currentDomain2 = domain.getInterval(i2);

      int max1 = size;

      while (true) {

        if (currentDomain1.max() + 1 < currentDomain2.min()) {
          result.unionAdapt(new Interval(currentDomain1.min(), currentDomain1.max()));
          i1++;
          if (i1 == max1) {
            break;
          }
          currentDomain1 = intervals[i1];
          continue;
        }

        if (currentDomain2.max() + 1 < currentDomain1.min()) {
          result.unionAdapt(new Interval(currentDomain2.min(), currentDomain2.max()));
          i2++;
          if (i2 < domain.noIntervals()) {
            currentDomain2 = domain.getInterval(i2);
            continue;
          } else {
            break;
          }
        }

        // currentDomain2.max > currentDomain1.min) {

        int min = Math.min(currentDomain1.min(), currentDomain2.min());

        while ((currentDomain1.max() + 1 >= currentDomain2.min()
                && currentDomain1.min() <= currentDomain2.min())
            || (currentDomain2.max() + 1 >= currentDomain1.min()
                && currentDomain2.min() <= currentDomain1.min())) {

          if (currentDomain1.max() <= currentDomain2.max()) {
            i1++;
            if (i1 == max1) {
              break;
            }
            currentDomain1 = intervals[i1];
            continue;
          }

          i2++;
          if (i2 < domain.noIntervals()) {
            currentDomain2 = domain.getInterval(i2);
          } else {
            break;
          }
        }

        if (i1 == max1) {

          while (currentDomain2.max() <= currentDomain1.max()) {
            i2++;
            if (i2 < domain.noIntervals()) {
              currentDomain2 = domain.getInterval(i2);
            } else {
              break;
            }
          }

          if (currentDomain1.max() <= currentDomain2.max()
              && currentDomain1.max() + 1 >= currentDomain2.min()) {
            result.unionAdapt(new Interval(min, currentDomain2.max()));
            i2++;
          } else {
            result.unionAdapt(new Interval(min, currentDomain1.max()));
          }
          break;
        }

        if (domain.noIntervals() == i2) {

          while (currentDomain1.max() <= currentDomain2.max()) {
            i1++;
            if (i1 == max1) {
              break;
            }
            currentDomain1 = intervals[i1];
          }

          if (currentDomain2.max() <= currentDomain1.max()
              && currentDomain2.max() + 1 >= currentDomain1.min()) {
            result.unionAdapt(new Interval(min, currentDomain1.max()));
            i1++;
          } else {
            result.unionAdapt(new Interval(min, currentDomain2.max()));
          }
          break;
        }

        if (currentDomain1.max() < currentDomain2.max()) {
          result.unionAdapt(new Interval(min, currentDomain1.max()));
          i1++;
          if (i1 == max1) {
            break;
          }
          currentDomain1 = intervals[i1];
        } else {
          result.unionAdapt(new Interval(min, currentDomain2.max()));
          i2++;
          if (i2 < domain.noIntervals()) {
            currentDomain2 = domain.getInterval(i2);
          } else {
            break;
          }
        }
      }

      if (i1 < max1) {
        for (; i1 < max1; i1++) {
          result.unionAdapt(intervals[i1]);
        }
      }

      for (; i2 < domain.noIntervals(); i2++) {
        result.unionAdapt(domain.getInterval(i2));
      }

      if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain result = new IntervalDomain(size + 1);

    int i1 = 0;

    Interval currentInterval1 = intervals[i1];

    // all intervals before and not glued (min..max) are included
    while (i1 < size && currentInterval1.max() + 1 < min) {
      result.unionAdapt(currentInterval1);
      i1++;
      if (i1 < size) {
        currentInterval1 = intervals[i1];
      }
    }

    if (i1 == size) {
      result.unionAdapt(new Interval(min, max));
    } else if (max + 1 < currentInterval1.min()) {
      // currentInterval if after and not glued
      result.unionAdapt(new Interval(min, max));
    } else {
      // current interval is glued or intersects with (min..max).

      int tempMin;

      if (currentInterval1.min() < min) {
        tempMin = currentInterval1.min();
      } else {
        tempMin = min;
      }

      if (currentInterval1.max() > max) {
        result.unionAdapt(new Interval(tempMin, currentInterval1.max()));
        i1++;
      } else {

        // (min..max) can cover multiple intervals.
        while (currentInterval1.max() <= max) {
          i1++;
          if (i1 == size) {
            result.unionAdapt(new Interval(tempMin, max));
            break;
          }
          currentInterval1 = intervals[i1];
        }

        // if current interval is glued or intersects with (min..max)
        if (max + 1 >= currentInterval1.min()) {
          result.unionAdapt(new Interval(tempMin, currentInterval1.max()));
          i1++;
        } else {
          result.unionAdapt(new Interval(tempMin, max));
        }
      }
    }

    if (i1 < size) {
      for (; i1 < size; i1++) {
        result.unionAdapt(intervals[i1]);
      }
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    return result;
  }

  @Override
  public IntDomain union(int value) {

    if (size == 0) {
      return new IntervalDomain(value, value);
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    IntervalDomain result = new IntervalDomain(size + 1);

    int i1 = 0;

    Interval currentInterval = intervals[i1];

    while (true) {

      if (currentInterval.max() + 1 < value) {
        result.unionAdapt(currentInterval);
        i1++;
        if (i1 == size) {
          result.unionAdapt(new Interval(value, value));
          return result;
        }
        currentInterval = intervals[i1];
      } else {
        break;
      }
    }

    if (value + 1 < currentInterval.min()) {
      result.unionAdapt(new Interval(value, value));
    } else {

      int tempMin = value;
      int tempMax = value;

      if (currentInterval.min() < value) {
        tempMin = currentInterval.min();
      }

      if (currentInterval.max() > value) {
        tempMax = currentInterval.max();
      }

      if (i1 + 1 < size && tempMax + 1 == intervals[i1 + 1].min()) {
        tempMax = intervals[i1 + 1].max();
        i1++;
      }

      result.unionAdapt(new Interval(tempMin, tempMax));
      i1++;
    }

    if (i1 < size) {
      for (; i1 < size; i1++) {
        result.unionAdapt(intervals[i1]);
      }
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (min > intervals[size - 1].max()) {
      throw failException;
    }

    if (min <= intervals[0].min()) {
      return;
    }

    int pointer = 0;
    while (intervals[pointer].max() < min) {
      pointer++;
    }

    int out = 0;
    int p = pointer;
    Interval iv = intervals[p];
    Interval[] copy = new Interval[size + ALLOCATION_MARGIN];
    if (iv.min() < min) {
      copy[out++] = new Interval(min, iv.max());
      p++;
    } else {
      copy[out++] = iv;
      p++;
    }
    while (p < size) {
      copy[out++] = intervals[p++];
    }

    installArrayResult(copy, out, storeLevel, v);
  }

  @Override
  public void inMax(int storeLevel, Var v, int max) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (max < intervals[0].min()) {
      throw failException;
    }

    int currentMax = intervals[size - 1].max();

    if (max >= currentMax) {
      return;
    }

    int pointer = size - 1;
    while (intervals[pointer].min() > max) {
      pointer--;
    }

    int out = 0;
    int p = 0;
    Interval[] copy = new Interval[size + ALLOCATION_MARGIN];
    while (p < pointer) {
      copy[out++] = intervals[p++];
    }
    Interval iv = intervals[pointer];
    if (iv.max() > max) {
      copy[out++] = new Interval(iv.min(), max);
    } else {
      copy[out++] = iv;
    }

    installArrayResult(copy, out, storeLevel, v);
  }

  @Override
  public void in(int storeLevel, Var v, int min, int max) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && !(min <= max)) {
      throw new IllegalStateException(
          String.valueOf("Min value greater than max value " + min + " > " + max));
    }

    if (max < intervals[0].min()) {
      throw failException;
    }

    int currentMax = intervals[size - 1].max();
    if (min > currentMax) {
      throw failException;
    }

    if (min <= intervals[0].min() && max >= currentMax) {
      return;
    }

    int pointer = 0;

    // pointer is always smaller than size as domains intersect
    while (intervals[pointer].max() < min) {
      pointer++;
    }

    if (intervals[pointer].min() > max) {
      throw failException;
    }

    int out = 0;
    int p = pointer;

    Interval iv = intervals[p];
    int a = Math.max(iv.min(), min);
    int b = Math.min(iv.max(), max);
    Interval[] copy = new Interval[size + ALLOCATION_MARGIN];
    copy[out] = (a == iv.min() && b == iv.max()) ? iv : new Interval(a, b);
    out++;
    p++;

    while (p < size && intervals[p].max() <= max) {
      copy[out++] = intervals[p++];
    }

    if (p < size && intervals[p].min() <= max) {
      iv = intervals[p];
      a = Math.max(iv.min(), min);
      b = Math.min(iv.max(), max);
      copy[out] = (a == iv.min() && b == iv.max()) ? iv : new Interval(a, b);
      out++;
    }

    installArrayResult(copy, out, storeLevel, v);
  }

  @Override
  public void in(int storeLevel, Var v, IntDomain domain) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && !(this.stamp <= storeLevel)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain input = (IntervalDomain) domain;

      if (ASSERTS_ENABLED && !(input.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(input.checkInvariants()));
      }

      if (input.size == 0) {
        throw failException;
      }

      if (ASSERTS_ENABLED && !(size != 0)) {
        throw new IllegalStateException("Assertion failed");
      }

      int pointer1 = 0;
      int pointer2 = 0;

      Interval[] inputIntervals = input.intervals;
      int inputSize = input.size;
      // Chance for no event
      while (pointer2 < inputSize && inputIntervals[pointer2].max() < intervals[pointer1].min()) {
        pointer2++;
      }

      if (pointer2 == inputSize) {
        throw failException;
      }

      // traverse within while loop until certain that change will occur
      while (intervals[pointer1].min() >= inputIntervals[pointer2].min()
          && intervals[pointer1].max() <= inputIntervals[pointer2].max()
          && ++pointer1 < size) {

        while (intervals[pointer1].max() > inputIntervals[pointer2].max()) {
          pointer2++;
          if (pointer2 >= inputSize) {
            break;
          }
        }

        if (pointer2 == inputSize) {
          break;
        }
      }

      // no change
      if (pointer1 == size) {
        return;
      }

      Interval[] copy = new Interval[size + inputSize + ALLOCATION_MARGIN];
      int out = 0;

      for (int t = 0; t < pointer1; t++) {
        copy[out++] = intervals[t];
      }

      pointer2 = 0;

      int interval1Min = intervals[pointer1].min();
      int interval1Max = intervals[pointer1].max();
      int interval2Min = inputIntervals[pointer2].min();
      int interval2Max = inputIntervals[pointer2].max();

      while (true) {

        if (interval1Max < interval2Min) {
          pointer1++;
          if (pointer1 < size) {
            interval1Min = intervals[pointer1].min();
            interval1Max = intervals[pointer1].max();
          } else {
            break;
          }
        } else if (interval2Max < interval1Min) {
          pointer2++;
          if (pointer2 < inputSize) {
            interval2Min = inputIntervals[pointer2].min();
            interval2Max = inputIntervals[pointer2].max();
          } else {
            break;
          }
        } else if (interval1Min <= interval2Min) {

          if (interval1Max <= interval2Max) {
            copy[out++] = new Interval(interval2Min, interval1Max);

            pointer1++;
            if (pointer1 < size) {
              interval1Min = intervals[pointer1].min();
              interval1Max = intervals[pointer1].max();
            } else {
              break;
            }
          } else {
            copy[out++] = inputIntervals[pointer2];
            pointer2++;

            if (pointer2 < inputSize) {
              interval2Min = inputIntervals[pointer2].min();
              interval2Max = inputIntervals[pointer2].max();
            } else {
              break;
            }
          }

        } else {

          if (interval2Max <= interval1Max) {
            copy[out++] = new Interval(interval1Min, interval2Max);

            if (interval2Max >= interval1Max) {
              pointer1++;
              if (pointer1 < size) {
                interval1Min = intervals[pointer1].min();
                interval1Max = intervals[pointer1].max();
              } else {
                break;
              }
            }

            pointer2++;
            if (pointer2 < inputSize) {
              interval2Min = inputIntervals[pointer2].min();
              interval2Max = inputIntervals[pointer2].max();
            } else {
              break;
            }
          } else {
            copy[out++] = intervals[pointer1];
            pointer1++;
            if (pointer1 < size) {
              interval1Min = intervals[pointer1].min();
              interval1Max = intervals[pointer1].max();
            } else {
              break;
            }
          }
        }
      }

      if (out == 0) {
        throw failException;
      }

      int returnedEvent = ANY;
      if (out == 1 && copy[0].min() == copy[0].max()) {
        returnedEvent = GROUND;
      } else if (copy[0].min() > min() || copy[out - 1].max() < max()) {
        returnedEvent = BOUND;
      }

      IntervalDomain result = null;
      if (stamp == storeLevel) {
        intervals = copy;
        size = out;
      } else {
        result = new IntervalDomain(copy, out);
        installResultDomain(result, storeLevel, v);
      }

      IntervalDomain effective = stamp == storeLevel ? this : result;
      if (ASSERTS_ENABLED && !(effective.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(effective.checkInvariants()));
      }

      v.domainHasChanged(returnedEvent);
      return;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {

      if (domain.isEmpty()) {
        throw failException;
      }

      if (ASSERTS_ENABLED && !(size != 0)) {
        throw new IllegalStateException("Assertion failed");
      }

      in(storeLevel, v, domain.min(), domain.max());

      return;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      SmallDenseDomain result = input.intersect(this, 0);

      if (result.isEmpty()) {
        throw Store.failException;
      }

      if (result.eq(this)) {
        return;
      }

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      int returnedEvent = computeEvent(result);

      result.modelConstraints = modelConstraints;
      result.searchConstraints = searchConstraints;
      result.stamp = storeLevel;
      result.previousDomain = stamp == storeLevel ? previousDomain : this;
      result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
      result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
      ((IntVar) v).domain = result;

      if (ASSERTS_ENABLED && !(result.eq(this.intersect(input.toIntervalDomain())))) {
        throw new IllegalStateException(
            String.valueOf("In function improperly implemented." + result + "d " + input));
      }

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      v.domainHasChanged(returnedEvent);
      return;
    }

    // Dense intersection using two-pointer traversal over intervals.
    // Handles both sparse and non-sparse representations uniformly.
    if (domain.getSize() == 0) {
      throw failException;
    }

    if (ASSERTS_ENABLED && !(size != 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    int pointer1 = 0;
    int pointer2 = 0;

    int inputSize = domain.noIntervals();

    // Chance for no event
    while (pointer2 < inputSize && domain.getInterval(pointer2).max() < intervals[pointer1].min()) {
      pointer2++;
    }

    if (pointer2 == inputSize) {
      throw failException;
    }

    // traverse within while loop until certain that change will occur
    while (intervals[pointer1].min() >= domain.getInterval(pointer2).min()
        && intervals[pointer1].max() <= domain.getInterval(pointer2).max()
        && ++pointer1 < size) {

      while (intervals[pointer1].max() > domain.getInterval(pointer2).max()) {
        pointer2++;
        if (pointer2 >= inputSize) {
          break;
        }
      }

      if (pointer2 == inputSize) {
        break;
      }
    }

    // no change
    if (pointer1 == size) {
      return;
    }

    IntervalDomain result = new IntervalDomain(this.size);
    int temp = 0;
    // add all common intervals to result as indicated by progress of
    // the previous loop
    while (temp < pointer1) {
      result.unionAdapt(intervals[temp++]);
    }

    pointer2 = 0;

    int interval1Min = intervals[pointer1].min();
    int interval1Max = intervals[pointer1].max();
    int interval2Min = domain.getInterval(pointer2).min();
    int interval2Max = domain.getInterval(pointer2).max();

    while (true) {

      if (interval1Max < interval2Min) {
        pointer1++;
        if (pointer1 < size) {
          interval1Min = intervals[pointer1].min();
          interval1Max = intervals[pointer1].max();
        } else {
          break;
        }
      } else if (interval2Max < interval1Min) {
        pointer2++;
        if (pointer2 < inputSize) {
          interval2Min = domain.getInterval(pointer2).min();
          interval2Max = domain.getInterval(pointer2).max();
        } else {
          break;
        }
      } else
      // interval1Max >= interval2Min
      // interval2Max >= interval1Min
      if (interval1Min <= interval2Min) {

        if (interval1Max <= interval2Max) {
          result.unionAdapt(new Interval(interval2Min, interval1Max));

          pointer1++;
          if (pointer1 < size) {
            interval1Min = intervals[pointer1].min();
            interval1Max = intervals[pointer1].max();
          } else {
            break;
          }
        } else {
          result.unionAdapt(new Interval(interval2Min, interval2Max));
          pointer2++;

          if (pointer2 < inputSize) {
            interval2Min = domain.getInterval(pointer2).min();
            interval2Max = domain.getInterval(pointer2).max();
          } else {
            break;
          }
        }

      } else {
        // interval1Max >= interval2Min
        // interval2Max >= interval1Min
        // interval1Min > interval2Min
        if (interval2Max <= interval1Max) {

          result.unionAdapt(new Interval(interval1Min, interval2Max));

          if (interval2Max == interval1Max) {
            pointer1++;
            if (pointer1 < size) {
              interval1Min = intervals[pointer1].min();
              interval1Max = intervals[pointer1].max();
            } else {
              break;
            }
          }

          pointer2++;
          if (pointer2 < inputSize) {
            interval2Min = domain.getInterval(pointer2).min();
            interval2Max = domain.getInterval(pointer2).max();
          } else {
            break;
          }

        } else {
          result.unionAdapt(intervals[pointer1]);
          pointer1++;
          if (pointer1 < size) {
            interval1Min = intervals[pointer1].min();
            interval1Max = intervals[pointer1].max();
          } else {
            break;
          }
        }
      }
    }

    if (result.isEmpty()) {
      throw failException;
    }

    int returnedEvent = computeEvent(result);

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    if (stamp == storeLevel) {
      adoptIntervalsFrom(result);
    } else {
      if (ASSERTS_ENABLED && !(stamp < storeLevel)) {
        throw new IllegalStateException("Assertion failed");
      }
      installResultDomain(result, storeLevel, v);
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    v.domainHasChanged(returnedEvent);
  }

  @Override
  public void inValue(int storeLevel, IntVar v, int value) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (singleton(value)) {
      return;
    }

    if (!contains(value)) {
      throw failException;
    }

    if (stamp == storeLevel) {

      if (intervals.length > 0) {
        intervals[0] = new Interval(value, value);
      } else {
        throw new RuntimeException("Internal error in InternalDomain.inValue");
      }
      size = 1;

    } else {

      if (ASSERTS_ENABLED && !(stamp < storeLevel)) {
        throw new IllegalStateException("Assertion failed");
      }

      IntervalDomain result = new IntervalDomain(1);
      result.intervals[0] = new Interval(value, value);
      result.size = 1;

      installResultDomain(result, storeLevel, v);
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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
      Interval i0 = intervals[0];
      if (value >= i0.min() && value <= i0.max()) {
        return 0;
      }
    }
    if (size > 1) {
      Interval i1 = intervals[1];
      if (value >= i1.min() && value <= i1.max()) {
        return 1;
      }
    }
    int lo = 2;
    int hi = size - 1;
    while (lo <= hi) {
      int mid = (lo + hi) >> 1;
      Interval i = intervals[mid];
      if (value > i.max()) {
        lo = mid + 1;
      } else if (value < i.min()) {
        hi = mid - 1;
      } else {
        return mid;
      }
    }
    return -1;
  }

  @Override
  public Interval getInterval(int position) {

    if (ASSERTS_ENABLED && !(position < size)) {
      throw new IllegalStateException("Assertion failed");
    }

    return intervals[position];
  }

  @Override
  public void inComplement(int storeLevel, Var v, int complement) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    int counter = intervalNo(complement);

    if (counter == -1) {
      return;
    }

    if (storeLevel == stamp) {

      if (intervals[counter].min() == complement) {

        if (intervals[counter].max() != complement) {

          intervals[counter] = new Interval(complement + 1, intervals[counter].max());

          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          if (singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          if (counter == 0) {
            v.domainHasChanged(BOUND);
          } else {
            v.domainHasChanged(ANY);
          }
        } else {
          // if domain like this 1..3, 5, 7..10, and 5 being removed.

          if (singleton(complement)) {
            throw failException;
          }

          for (int i = counter; i < size - 1; i++) {
            intervals[i] = intervals[i + 1];
          }

          size--;

          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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
            v.domainHasChanged(BOUND);
          } else {
            v.domainHasChanged(ANY);
          }
        }
        return;
      }

      if (intervals[counter].max() == complement) {

        // domain like this 1..3, 5, 7..10, and 5 being
        // removed taken care of above.

        intervals[counter] = new Interval(intervals[counter].min(), complement - 1);

        if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }

        if (singleton()) {
          v.domainHasChanged(GROUND);
          return;
        }

        if (counter == size - 1) {
          v.domainHasChanged(BOUND);
        } else {
          v.domainHasChanged(ANY);
        }
        return;
      }

      if (size + 1 < intervals.length) {
        for (int i = size; i > counter + 1; i--) {
          intervals[i] = intervals[i - 1];
        }
      } else {
        Interval[] updatedIntervals = new Interval[size + 1 + ALLOCATION_MARGIN];
        System.arraycopy(intervals, 0, updatedIntervals, 0, counter + 1);
        System.arraycopy(intervals, counter, updatedIntervals, counter + 1, size - counter);
        intervals = updatedIntervals;
      }

      int max = intervals[counter].max();
      intervals[counter] = new Interval(intervals[counter].min(), complement - 1);
      intervals[counter + 1] = new Interval(complement + 1, max);

      // One interval has been split, size increased by one.
      size++;

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

    } else {

      if (singleton(complement)) {
        throw failException;
      }

      if (ASSERTS_ENABLED && !(storeLevel > stamp)) {
        throw new IllegalStateException("Assertion failed");
      }

      IntervalDomain result = new IntervalDomain(this.size + 1);

      // variable obtains new domain, current one (this) becomes
      // previousDomain
      installResultDomain(result, storeLevel, v);

      if (intervals[counter].min() == complement) {

        if (intervals[counter].max() != complement) {

          System.arraycopy(intervals, 0, result.intervals, 0, size);

          result.intervals[counter] = new Interval(complement + 1, result.intervals[counter].max());

          result.size = size;

          if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }
          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          if (counter == 0) {
            v.domainHasChanged(BOUND);
          } else {
            v.domainHasChanged(ANY);
          }
        } else {
          // if domain like this 1..3, 5, 7..10, and 5 being removed.
          System.arraycopy(intervals, 0, result.intervals, 0, counter);

          System.arraycopy(intervals, counter + 1, result.intervals, counter, size - counter - 1);

          result.size = size - 1;

          if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          if (counter == 0 || counter == size - 1) {
            v.domainHasChanged(BOUND);
          } else {
            v.domainHasChanged(ANY);
          }
        }
        return;
      }

      if (intervals[counter].max() == complement) {

        // domain like this 1..3, 5, 7..10, and 5 being removed taken
        // care of above.

        System.arraycopy(intervals, 0, result.intervals, 0, size);

        result.intervals[counter] = new Interval(result.intervals[counter].min(), complement - 1);

        result.size = size;

        if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }
        if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
          throw new IllegalStateException(String.valueOf(result.checkInvariants()));
        }

        if (result.singleton()) {
          v.domainHasChanged(GROUND);
          return;
        }
        if (counter == size - 1) {
          v.domainHasChanged(BOUND);
        } else {
          v.domainHasChanged(ANY);
        }
        return;
      }

      // if domain like this 1..3 and value 2 being removed, or
      // 1..3, 5..7, 10..20, and value 6 being removed.

      // length of result is by default one longer than size of this.

      if (size != 1) {
        System.arraycopy(intervals, 0, result.intervals, 0, counter + 1);
        System.arraycopy(intervals, counter, result.intervals, counter + 1, size - counter);
      }

      int max = intervals[counter].max();
      result.intervals[counter] = new Interval(intervals[counter].min(), complement - 1);
      result.intervals[counter + 1] = new Interval(complement + 1, max);

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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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

      int noRemoved = 0;

      if (intervals[counter].min() < min) {
        // intervals[counter].min..min-1

        if (intervals[counter].max() > max) {
          // max+1..intervals[counter].max
          if (size < intervals.length) {
            // copy elements to make one hole for new interval

            for (int i = size; i > counter; i--) {
              intervals[i] = intervals[i - 1];
            }

            intervals[counter + 1] = new Interval(max + 1, intervals[counter].max());
            intervals[counter] = new Interval(intervals[counter].min(), min - 1);

          } else {
            // create new array and copy

            Interval[] oldIntervals = intervals;
            intervals = new Interval[oldIntervals.length + 5];

            if (counter > 0) {
              System.arraycopy(oldIntervals, 0, intervals, 0, counter);
            }

            System.arraycopy(oldIntervals, counter + 1, intervals, counter + 2, size - counter - 1);

            intervals[counter + 1] = new Interval(max + 1, oldIntervals[counter].max());
            intervals[counter] = new Interval(oldIntervals[counter].min(), min - 1);
          }
          size++;
          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          v.domainHasChanged(ANY);
        } else {
          // intervals[counter].max <= max
          // intervals[counter].min..min-1

          intervals[counter] = new Interval(intervals[counter].min(), min - 1);

          int position = ++counter;

          while (position < size && intervals[position].max() <= max) {
            position++;
            noRemoved++;
          }

          if (noRemoved > 0) {

            for (int i = counter; i + noRemoved < size; i++) {
              intervals[i] = intervals[i + noRemoved];
            }
          }

          size -= noRemoved;

          if (counter < size && intervals[counter].min() <= max) {
            intervals[counter] = new Interval(max + 1, intervals[counter].max());
          }

          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          if (singleton()) {
            v.domainHasChanged(GROUND);
          } else if (max() < min) {
            v.domainHasChanged(BOUND);
          } else {
            v.domainHasChanged(ANY);
          }
        }

      } else {
        // intervals[counter].min >= min
        if (intervals[counter].max() > max) {
          // max+1..intervals[counter].max

          intervals[counter] = new Interval(max + 1, intervals[counter].max());

        } else {
          // intervals[counter] is removed

          int position = counter;

          while (position < size && intervals[position].max() <= max) {
            position++;
            noRemoved++;
          }

          for (int i = counter; i + noRemoved < size; i++) {
            intervals[i] = intervals[i + noRemoved];
          }

          size -= noRemoved;

          if (counter < size && intervals[counter].min() <= max) {
            intervals[counter] = new Interval(max + 1, intervals[counter].max());
          }
        }
        if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }
        if (singleton()) {
          v.domainHasChanged(GROUND);
          return;
        }
        if (max() < min || max < min()) {
          v.domainHasChanged(BOUND);
        } else {
          v.domainHasChanged(ANY);
        }
      }

    } else {

      if (ASSERTS_ENABLED && !(storeLevel > stamp)) {
        throw new IllegalStateException("Assertion failed");
      }

      IntervalDomain result = new IntervalDomain(this.size + 1);

      installResultDomain(result, storeLevel, v);
      result.size = size;

      int noRemoved = 0;

      System.arraycopy(intervals, 0, result.intervals, 0, counter);

      if (intervals[counter].min() < min) {
        // intervals[counter].min..min-1

        if (intervals[counter].max() > max) {
          // max+1..intervals[counter].max
          // copy elements to make one hole for new interval

          if (size - counter >= 0) {
            System.arraycopy(intervals, counter, result.intervals, counter + 1, size - counter);
          }

          result.intervals[counter + 1] = new Interval(max + 1, intervals[counter].max());
          result.intervals[counter] = new Interval(intervals[counter].min(), min - 1);

          result.size++;

          if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }
          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }

          v.domainHasChanged(ANY);

        } else {

          result.intervals[counter] = new Interval(intervals[counter].min(), min - 1);

          int position = ++counter;

          while (position < size && intervals[position].max() <= max) {
            position++;
            noRemoved++;
          }

          for (int i = counter; i + noRemoved < size; i++) {
            result.intervals[i] = intervals[i + noRemoved];
          }

          if (counter + noRemoved < size && intervals[counter + noRemoved].min() <= max) {
            result.intervals[counter] = new Interval(max + 1, intervals[counter + noRemoved].max());
          }

          result.size -= noRemoved;

          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
          } else if (result.max() < min) {
            v.domainHasChanged(BOUND);
          } else {
            v.domainHasChanged(ANY);
          }
        }

      } else {

        if (intervals[counter].max() > max) {
          // max+1..intervals[counter].max

          if (size - (counter + 1) >= 0) {
            System.arraycopy(
                intervals, counter + 1, result.intervals, counter + 1, size - (counter + 1));
          }

          result.intervals[counter] = new Interval(max + 1, intervals[counter].max());

          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
            return;
          }

          if (result.max() < min || max < result.min()) {
            v.domainHasChanged(BOUND);
          } else {
            v.domainHasChanged(ANY);
          }

        } else {
          // intervals[counter] is removed

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
            result.intervals[counter] = new Interval(max + 1, intervals[counter + noRemoved].max());
          }

          if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(checkInvariants()));
          }
          if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
            throw new IllegalStateException(String.valueOf(result.checkInvariants()));
          }

          if (result.singleton()) {
            v.domainHasChanged(GROUND);
          } else if (result.max() < min || max < result.min()) {
            v.domainHasChanged(BOUND);
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(this.stamp <= storeLevel)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain input = (IntervalDomain) domain;

      if (input.size == 0) {
        throw failException;
      }

      if (ASSERTS_ENABLED && !(size != 0)) {
        throw new IllegalStateException("Assertion failed");
      }

      int pointer1 = 0;
      int pointer2 = 0;
      int inputSize = input.size;

      Interval[] inputIntervals = input.intervals;

      // Chance for no event
      // traverse within while loop until certain that change will occur

      while (pointer2 < inputSize
          && inputIntervals[pointer2].max() + shift < intervals[pointer1].min()) {
        pointer2++;
      }

      if (pointer2 == inputSize) {
        throw failException;
      }

      while (intervals[pointer1].min() >= inputIntervals[pointer2].min() + shift
          && intervals[pointer1].max() <= inputIntervals[pointer2].max() + shift
          && ++pointer1 < size) {

        while (intervals[pointer1].max() > inputIntervals[pointer2].max() + shift) {
          pointer2++;
          if (pointer2 >= input.size) {
            break;
          }
        }

        if (pointer2 == input.size) {
          break;
        }
      }

      // no change
      if (pointer1 == size) {
        return;
      }

      IntervalDomain result = new IntervalDomain(size);
      pointer2 = 0;

      // add all common intervals to result as indicated by progress of
      // the previous loop
      while (pointer2 < pointer1) {
        result.unionAdapt(intervals[pointer2++]);
      }

      pointer2 = 0;

      int interval1Min = intervals[pointer1].min();
      int interval1Max = intervals[pointer1].max();
      int interval2Min = inputIntervals[pointer2].min() + shift;
      int interval2Max = inputIntervals[pointer2].max() + shift;
      while (true) {

        if (interval1Max < interval2Min) {
          pointer1++;
          if (pointer1 < size) {
            interval1Min = intervals[pointer1].min();
            interval1Max = intervals[pointer1].max();
          } else {
            break;
          }
        } else if (interval2Max < interval1Min) {
          pointer2++;
          if (pointer2 < inputSize) {
            interval2Min = inputIntervals[pointer2].min() + shift;
            interval2Max = inputIntervals[pointer2].max() + shift;
          } else {
            break;
          }
        } else
        // interval1Max >= interval2Min
        // interval2Max >= interval1Min
        if (interval1Min <= interval2Min) {

          if (interval1Max <= interval2Max) {
            result.unionAdapt(new Interval(interval2Min, interval1Max));

            pointer1++;
            if (pointer1 < size) {
              interval1Min = intervals[pointer1].min();
              interval1Max = intervals[pointer1].max();
            } else {
              break;
            }
          } else {
            result.unionAdapt(
                new Interval(
                    inputIntervals[pointer2].min() + shift,
                    inputIntervals[pointer2].max() + shift));

            pointer2++;

            if (pointer2 < inputSize) {
              interval2Min = inputIntervals[pointer2].min() + shift;
              interval2Max = inputIntervals[pointer2].max() + shift;
            } else {
              break;
            }
          }

        } else {
          // interval1Max >= interval2Min
          // interval2Max >= interval1Min
          // interval1Min > interval2Min
          if (interval2Max <= interval1Max) {
            result.unionAdapt(new Interval(interval1Min, interval2Max));

            if (interval2Max >= interval1Max) {
              pointer1++;
              if (pointer1 < size) {
                // shift has been removed.
                interval1Min = intervals[pointer1].min();
                interval1Max = intervals[pointer1].max();
              } else {
                break;
              }
            }

            pointer2++;
            if (pointer2 < inputSize) {
              interval2Min = inputIntervals[pointer2].min() + shift;
              interval2Max = inputIntervals[pointer2].max() + shift;
            } else {
              break;
            }
          } else {
            result.unionAdapt(intervals[pointer1]);
            pointer1++;
            if (pointer1 < size) {
              interval1Min = intervals[pointer1].min();
              interval1Max = intervals[pointer1].max();
            } else {
              break;
            }
          }
        }
      }

      if (result.isEmpty()) {
        throw failException;
      }

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      int returnedEvent = computeEvent(result);

      if (stamp == storeLevel) {
        adoptIntervalsFrom(result);
      } else {
        if (ASSERTS_ENABLED && !(stamp < storeLevel)) {
          throw new IllegalStateException("Assertion failed");
        }
        installResultDomain(result, storeLevel, v);
      }

      v.domainHasChanged(returnedEvent);
      return;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {

      if (domain.isEmpty()) {
        throw failException;
      }

      in(storeLevel, v, domain.min() + shift, domain.max() + shift);
      return;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      SmallDenseDomain result = input.intersect(this, -shift);
      result.shift(shift);

      if (result.isEmpty()) {
        throw Store.failException;
      }

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      int returnedEvent = computeEvent(result);

      result.modelConstraints = modelConstraints;
      result.searchConstraints = searchConstraints;
      result.stamp = storeLevel;
      result.previousDomain = stamp == storeLevel ? previousDomain : this;
      result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
      result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
      ((IntVar) v).domain = result;

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      v.domainHasChanged(returnedEvent);
      return;
    }

    // Dense intersection with shift using two-pointer traversal over intervals.
    if (domain.getSize() == 0) {
      throw failException;
    }

    if (ASSERTS_ENABLED && !(size != 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    int pointer1 = 0;
    int pointer2 = 0;

    int inputSize = domain.noIntervals();

    // Chance for no event
    while (pointer2 < inputSize
        && domain.getInterval(pointer2).max() + shift < intervals[pointer1].min()) {
      pointer2++;
    }

    if (pointer2 == inputSize) {
      throw failException;
    }

    // traverse within while loop until certain that change will occur
    while (intervals[pointer1].min() >= domain.getInterval(pointer2).min() + shift
        && intervals[pointer1].max() <= domain.getInterval(pointer2).max() + shift
        && ++pointer1 < size) {

      while (intervals[pointer1].max() > domain.getInterval(pointer2).max() + shift) {
        pointer2++;
        if (pointer2 >= inputSize) {
          break;
        }
      }

      if (pointer2 == inputSize) {
        break;
      }
    }

    // no change
    if (pointer1 == size) {
      return;
    }

    IntervalDomain result = new IntervalDomain(this.size);
    int temp = 0;
    // add all common intervals to result as indicated by progress of
    // the previous loop
    while (temp < pointer1) {
      result.unionAdapt(intervals[temp++]);
    }

    pointer2 = 0;

    int interval1Min = intervals[pointer1].min();
    int interval1Max = intervals[pointer1].max();
    int interval2Min = domain.getInterval(pointer2).min() + shift;
    int interval2Max = domain.getInterval(pointer2).max() + shift;

    while (true) {

      if (interval1Max < interval2Min) {
        pointer1++;
        if (pointer1 < size) {
          interval1Min = intervals[pointer1].min();
          interval1Max = intervals[pointer1].max();
        } else {
          break;
        }
      } else if (interval2Max < interval1Min) {
        pointer2++;
        if (pointer2 < inputSize) {
          interval2Min = domain.getInterval(pointer2).min() + shift;
          interval2Max = domain.getInterval(pointer2).max() + shift;
        } else {
          break;
        }
      } else
      // interval1Max >= interval2Min
      // interval2Max >= interval1Min
      if (interval1Min <= interval2Min) {

        if (interval1Max <= interval2Max) {
          result.unionAdapt(new Interval(interval2Min, interval1Max));

          pointer1++;
          if (pointer1 < size) {
            interval1Min = intervals[pointer1].min();
            interval1Max = intervals[pointer1].max();
          } else {
            break;
          }
        } else {
          result.unionAdapt(new Interval(interval2Min, interval2Max));
          pointer2++;

          if (pointer2 < inputSize) {
            interval2Min = domain.getInterval(pointer2).min() + shift;
            interval2Max = domain.getInterval(pointer2).max() + shift;
          } else {
            break;
          }
        }

      } else {
        // interval1Max >= interval2Min
        // interval2Max >= interval1Min
        // interval1Min > interval2Min
        if (interval2Max <= interval1Max) {
          result.unionAdapt(new Interval(interval1Min, interval2Max));

          if (interval2Max == interval1Max) {
            pointer1++;
            if (pointer1 < size) {
              interval1Min = intervals[pointer1].min();
              interval1Max = intervals[pointer1].max();
            } else {
              break;
            }
          }

          pointer2++;
          if (pointer2 < inputSize) {
            interval2Min = domain.getInterval(pointer2).min() + shift;
            interval2Max = domain.getInterval(pointer2).max() + shift;
          } else {
            break;
          }
        } else {
          result.unionAdapt(intervals[pointer1]);
          pointer1++;
          if (pointer1 < size) {
            interval1Min = intervals[pointer1].min();
            interval1Max = intervals[pointer1].max();
          } else {
            break;
          }
        }
      }
    }

    if (result.isEmpty()) {
      throw failException;
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    int returnedEvent = computeEvent(result);

    if (stamp == storeLevel) {
      adoptIntervalsFrom(result);
    } else {
      if (ASSERTS_ENABLED && !(stamp < storeLevel)) {
        throw new IllegalStateException("Assertion failed");
      }
      installResultDomain(result, storeLevel, v);
    }

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    v.domainHasChanged(returnedEvent);
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
  public boolean isNumeric() {
    return true;
  }

  @Override
  public int leftElement(int intervalNo) {

    if (ASSERTS_ENABLED && !(intervalNo < size)) {
      throw new IllegalStateException("Assertion failed");
    }
    return intervals[intervalNo].min();
  }

  @Override
  public int rightElement(int intervalNo) {

    if (ASSERTS_ENABLED && !(intervalNo < size)) {
      throw new IllegalStateException("Assertion failed");
    }
    return intervals[intervalNo].max();
  }

  /**
   * {@inheritDoc}
   *
   * <p>If domain is represented as a list of domains, the domain pointer within variable will be
   * updated.
   */
  @Override
  public void removeLevel(int level, Var v) {

    if (ASSERTS_ENABLED && !(this.stamp <= level)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (this.stamp == level) {

      ((IntVar) v).domain = this.previousDomain;
    }

    if (ASSERTS_ENABLED && !(((IntVar) v).domain.stamp < level)) {
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
      return domain.modelConstraintsToEvaluate[0]
          + domain.modelConstraintsToEvaluate[1]
          + domain.modelConstraintsToEvaluate[2];
    } else {
      return domain.sizeConstraintsOriginal();
    }
  }

  @Override
  public int previousValue(int value) {

    for (int m = size - 1; m >= 0; m--) {

      Interval i = intervals[m];

      // the max of previous interval is the seeked value.
      if (i.min() < value) {
        if (i.max() >= value) {
          return value - 1;
        }
        // the value is equal
        return i.max();
      }
    }

    return value;
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

    for (int i = 0; i < size; i++) {
      if (this.intervals[i] == null) {
        return "size of the domain is not set up properly";
      }
    }

    if (this.intervals[0].min() > this.intervals[size - 1].max()) {
      return "Min value is larger than max value " + this;
    }

    for (int i = 0; i < size; i++) {
      if (this.intervals[i].min() > this.intervals[i].max()) {
        return "One of the intervals not properly build. Min value is larger than max value "
            + this;
      }
    }

    for (int i = 0; i < size - 1; i++) {
      if (this.intervals[i].max() + 1 == this.intervals[i + 1].min()) {
        return "Two consequtive intervals should be merged. Improper representation" + this;
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

    if (intervals[counter].min() == value) {

      if (intervals[counter].max() != value) {

        intervals[counter] = new Interval(value + 1, intervals[counter].max());

        if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
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

      intervals[counter] = new Interval(intervals[counter].min(), value - 1);

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      return;
    }

    if (size + 1 < intervals.length) {
      for (int i = size; i > counter + 1; i--) {
        intervals[i] = intervals[i - 1];
      }
    } else {
      Interval[] updatedIntervals = new Interval[size + 1 + ALLOCATION_MARGIN];
      System.arraycopy(intervals, 0, updatedIntervals, 0, counter + 1);
      System.arraycopy(intervals, counter, updatedIntervals, counter + 1, size - counter);
      intervals = updatedIntervals;
    }

    int max = intervals[counter].max();
    intervals[counter] = new Interval(intervals[counter].min(), value - 1);
    intervals[counter + 1] = new Interval(value + 1, max);

    // One interval has been split, size increased by one.
    size++;

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  @Override
  public void subtractAdapt(int minValue, int maxValue) {

    int current = 0;
    while (current < size && intervals[current].max() < minValue) {
      current++;
    }

    if (current == size) {
      return;
    }

    if (minValue <= intervals[current].min()) {

      if (maxValue < intervals[current].min()) {
        return;
      }

      // removing will not create more intervals.
      if (intervals[current].max() > maxValue) {

        intervals[current] = new Interval(maxValue + 1, intervals[current].max());

        if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
          throw new IllegalStateException(String.valueOf(checkInvariants()));
        }

      } else {
        // at least one complete interval is being removed.

        int maxCurrent = current;
        while (maxCurrent < size && intervals[maxCurrent].max() <= maxValue) {
          maxCurrent++;
        }

        if (maxCurrent == size) {
          size = current;
          return;
        }

        if (maxValue >= intervals[maxCurrent].min()) {
          intervals[maxCurrent] = new Interval(maxValue + 1, intervals[maxCurrent].max());
        }

        int i = current;
        for (; maxCurrent < size; i++, maxCurrent++) {
          intervals[i] = intervals[maxCurrent];
        }

        size = i;
      }
    } else {

      // minValue > intervals[current].min

      if (maxValue < intervals[current].max()) {
        // one additional interval is being created.

        if (intervals.length == size + 1) {
          // not enough space to insert new interval.
          Interval[] newIntervals = new Interval[intervals.length * 2];
          System.arraycopy(intervals, 0, newIntervals, 0, size);
          intervals = newIntervals;
        }

        for (int i = size; i > current; i--) {
          intervals[i] = intervals[i - 1];
        }

        intervals[current] = new Interval(intervals[current].min(), minValue - 1);
        intervals[current + 1] = new Interval(maxValue + 1, intervals[current + 1].max());

        size++;

      } else {
        // minValue > intervals[current].min
        // maxValue >= intervals[current].max

        // at least one complete interval is being removed.
        intervals[current] = new Interval(intervals[current].min(), minValue - 1);
        current++;

        int maxCurrent = current;
        while (maxCurrent < size && intervals[maxCurrent].max() <= maxValue) {
          maxCurrent++;
        }

        if (maxCurrent == size) {
          size = current;
          return;
        }

        if (intervals[maxCurrent].min() <= maxValue) {
          intervals[maxCurrent] = new Interval(maxValue + 1, intervals[maxCurrent].max());
        }

        int i = current;
        for (; maxCurrent < size; i++, maxCurrent++) {
          intervals[i] = intervals[maxCurrent];
          intervals[maxCurrent] = null;
        }

        size = i;
      }
    }
  }

  @Override
  public int intersectAdapt(IntDomain domain) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (size == 0) {
      return NONE;
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain input = (IntervalDomain) domain;

      if (ASSERTS_ENABLED && !(input.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(input.checkInvariants()));
      }

      if (input.size == 0) {
        size = 0;
        return GROUND;
      }

      int pointer1 = 0;
      int pointer2 = 0;

      Interval[] inputIntervals = input.intervals;
      int inputSize = input.size;
      // Chance for no event
      while (pointer2 < inputSize && inputIntervals[pointer2].max() < intervals[pointer1].min()) {
        pointer2++;
      }

      if (pointer2 == inputSize) {
        size = 0;
        return GROUND;
      }

      // traverse within while loop until certain that change will occur
      while (intervals[pointer1].min() >= inputIntervals[pointer2].min()
          && intervals[pointer1].max() <= inputIntervals[pointer2].max()
          && ++pointer1 < size) {

        while (intervals[pointer1].max() > inputIntervals[pointer2].max()) {
          pointer2++;
          if (pointer2 >= inputSize) {
            break;
          }
        }

        if (pointer2 == inputSize) {
          break;
        }
      }

      // no change
      if (pointer1 == size) {
        return NONE;
      }

      IntervalDomain result = new IntervalDomain(this.size);
      int temp = 0;
      // add all common intervals to result as indicated by progress of
      // the previous loop
      while (temp < pointer1) {
        result.unionAdapt(intervals[temp++]);
      }

      pointer2 = 0;

      int interval1Min = intervals[pointer1].min();
      int interval1Max = intervals[pointer1].max();
      int interval2Min = inputIntervals[pointer2].min();
      int interval2Max = inputIntervals[pointer2].max();

      while (true) {

        if (interval1Max < interval2Min) {
          pointer1++;
          if (pointer1 < size) {
            interval1Min = intervals[pointer1].min();
            interval1Max = intervals[pointer1].max();
          } else {
            break;
          }
        } else if (interval2Max < interval1Min) {
          pointer2++;
          if (pointer2 < inputSize) {
            interval2Min = inputIntervals[pointer2].min();
            interval2Max = inputIntervals[pointer2].max();
          } else {
            break;
          }
        } else
        // interval1Max >= interval2Min
        // interval2Max >= interval1Min
        if (interval1Min <= interval2Min) {

          if (interval1Max <= interval2Max) {
            result.unionAdapt(new Interval(interval2Min, interval1Max));

            pointer1++;
            if (pointer1 < size) {
              interval1Min = intervals[pointer1].min();
              interval1Max = intervals[pointer1].max();
            } else {
              break;
            }
          } else {
            result.unionAdapt(inputIntervals[pointer2]);
            pointer2++;

            if (pointer2 < inputSize) {
              interval2Min = inputIntervals[pointer2].min();
              interval2Max = inputIntervals[pointer2].max();
            } else {
              break;
            }
          }

        } else {
          // interval1Max >= interval2Min
          // interval2Max >= interval1Min
          // interval1Min > interval2Min
          if (interval2Max <= interval1Max) {
            result.unionAdapt(new Interval(interval1Min, interval2Max));

            if (interval2Max >= interval1Max) {
              pointer1++;
              if (pointer1 < size) {
                interval1Min = intervals[pointer1].min();
                interval1Max = intervals[pointer1].max();
              } else {
                break;
              }
            }

            pointer2++;
            if (pointer2 < inputSize) {
              interval2Min = inputIntervals[pointer2].min();
              interval2Max = inputIntervals[pointer2].max();
            } else {
              break;
            }
          } else {
            result.unionAdapt(intervals[pointer1]);
            pointer1++;
            if (pointer1 < size) {
              interval1Min = intervals[pointer1].min();
              interval1Max = intervals[pointer1].max();
            } else {
              break;
            }
          }
        }
      }

      if (result.isEmpty()) {
        size = 0;
        return GROUND;
      }

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      int returnedEvent = computeEvent(result);
      adoptIntervalsFrom(result);

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      return returnedEvent;
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

        if (current < intervals[position].min()) {
          bits = bits << (intervals[position].min() - current);
          current = intervals[position].min();
          continue;
        }

        if (bits > 0) {
          bits = bits << 1;
          current++;
          continue;
        }

        if (intervals[position].max() < current) {
          position++;
          continue;
        }

        int min = current;

        do {
          bits = bits << 1;
          current++;
        } while (bits < 0 && current <= intervals[position].max());

        result.unionAdapt(min, current - 1);
      }

      if (ASSERTS_ENABLED && !(this.intersect(input.toIntervalDomain()).eq(result))) {
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

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      int returnedEvent = computeEvent(result);
      adoptIntervalsFrom(result);

      if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      return returnedEvent;
    }

    if (ASSERTS_ENABLED && !(false)) {
      throw new IllegalStateException(
          String.valueOf("Not implemented for other domain type " + domain.getClass()));
    }

    // Only to satisfy the compiler.
    return NONE;
  }

  @Override
  public int intersectAdapt(int min, int max) {

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (ASSERTS_ENABLED && !(min <= max)) {
      throw new IllegalStateException(
          String.valueOf("Min value greater than max value " + min + " > " + max));
    }

    if (max < intervals[0].min()) {
      size = 0;
      return GROUND;
    }

    int currentMax = intervals[size - 1].max();
    if (min > currentMax) {
      size = 0;
      return GROUND;
    }

    if (min <= intervals[0].min() && max >= currentMax) {
      return NONE;
    }

    IntervalDomain result = new IntervalDomain(size + 1);
    int pointer = 0;

    // pointer is always smaller than size as domains intersect
    while (intervals[pointer].max() < min) {
      pointer++;
    }

    if (intervals[pointer].min() > max) {
      size = 0;
      return GROUND;
    }

    if (intervals[pointer].min() >= min) {
      if (intervals[pointer].max() <= max) {
        result.unionAdapt(intervals[pointer]);
      } else {
        result.unionAdapt(new Interval(intervals[pointer].min(), max));
      }
    } else if (intervals[pointer].max() <= max) {
      result.unionAdapt(new Interval(min, intervals[pointer].max()));
    } else {
      result.unionAdapt(new Interval(min, max));
    }

    pointer++;

    while (pointer < size) {
      if (intervals[pointer].max() <= max) {
        result.unionAdapt(intervals[pointer++]);
      } else {
        break;
      }
    }

    if (pointer < size && intervals[pointer].min() <= max) {
      result.unionAdapt(new Interval(intervals[pointer].min(), max));
    }

    adoptIntervalsFrom(result);

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && !(result.checkInvariants() == null)) {
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

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.isEmpty()) {
      return 0;
    }

    if (domain.isSparseRepresentation()) {
      return sizeOfIntersectionSparse(domain);
    } else {

      int temp = 0;

      int pointer1 = 0;
      int pointer2 = 0;

      int size1 = size;

      if (size1 == 0 || domain.noIntervals() == 0) {
        return 0;
      }

      Interval interval1 = intervals[pointer1];
      Interval interval2 = domain.getInterval(pointer2);

      while (true) {
        if (interval1.max() < interval2.min()) {
          pointer1++;
          if (pointer1 < size1) {
            interval1 = intervals[pointer1];
          } else {
            break;
          }
        } else if (interval2.max() < interval1.min()) {
          pointer2++;
          if (pointer2 < domain.noIntervals()) {
            interval2 = domain.getInterval(pointer2);
          } else {
            break;
          }
        } else
        // interval1.max >= interval2.min
        // interval2.max >= interval1.min
        if (interval1.min() <= interval2.min()) {

          if (interval1.max() <= interval2.max()) {
            temp += interval1.max() - interval2.min() + 1;
            pointer1++;
            if (pointer1 < size1) {
              interval1 = intervals[pointer1];
            } else {
              break;
            }
          } else {
            temp += interval2.max() - interval2.min() + 1;
            pointer2++;
            if (pointer2 < domain.noIntervals()) {
              interval2 = domain.getInterval(pointer2);
            } else {
              break;
            }
          }

        } else {
          // interval1.max >= interval2.min
          // interval2.max >= interval1.min
          // interval1.min > interval2.min
          if (interval2.max() <= interval1.max()) {
            temp += interval2.max() - interval1.min() + 1;
            pointer2++;
            if (pointer2 < domain.noIntervals()) {
              interval2 = domain.getInterval(pointer2);
            } else {
              break;
            }
          } else {
            temp += interval1.max() - interval1.min() + 1;
            pointer1++;
            if (pointer1 < size1) {
              interval1 = intervals[pointer1];
            } else {
              break;
            }
          }
        }
      }

      return temp;
    }
  }

  @Override
  public int getElementAt(int index) {

    if (ASSERTS_ENABLED && !(index >= 0)) {
      throw new IllegalStateException(String.valueOf("The index can not be negative"));
    }
    if (ASSERTS_ENABLED && !(index < this.getSize())) {
      throw new IllegalStateException(
          String.valueOf(
              "The domain does not have so many elements as specified by the index equal to "
                  + index));
    }

    int counter = 0;

    int currentRange = intervals[counter].max() - intervals[counter].min();

    while (index > currentRange) {
      index -= currentRange + 1;
      counter++;
      if (counter < size) {
        currentRange = intervals[counter].max() - intervals[counter].min();
      } else {
        throw new RuntimeException(
            "The domain does not have an element as specified by the index " + index);
      }
    }

    return intervals[counter].min() + index;
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

    if (ASSERTS_ENABLED && !(false)) {
      throw new IllegalStateException(
          String.valueOf("Error in IndomainRandom. " + "Domain " + this + " value " + value));
    }
    // Only to satisfy java compiler, should not be reached
    return Integer.MAX_VALUE;
  }
}
