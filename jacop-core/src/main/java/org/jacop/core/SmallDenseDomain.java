/*
 * SmallDenseDomain.java
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

import lombok.extern.slf4j.Slf4j;

/**
 * Defines small dense domain based on bits within a long number.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class SmallDenseDomain extends IntDomain {

  /**
   * It is an empty domain returned by default when empty domain becomes a result of any function.
   */
  public static final SmallDenseDomain emptyDomain = new SmallDenseDomain(1, 0L);

  private static final String DOMAIN_UPDATE_INCORRECT = "Domain update incorrect.";
  private static final String INCORRECT_IN_OPERATION = "Incorrect in operation";

  private static final long[] TWO_N_ARRAY =
      new long[] {
        0x1L,
        0x2L,
        0x4L,
        0x8L,
        0x10L,
        0x20L,
        0x40L,
        0x80L,
        0x100L,
        0x200L,
        0x400L,
        0x800L,
        0x1000L,
        0x2000L,
        0x4000L,
        0x8000L,
        0x10000L,
        0x20000L,
        0x40000L,
        0x80000L,
        0x100000L,
        0x200000L,
        0x400000L,
        0x800000L,
        0x1000000L,
        0x2000000L,
        0x4000000L,
        0x8000000L,
        0x10000000L,
        0x20000000L,
        0x40000000L,
        0x80000000L,
        0x100000000L,
        0x200000000L,
        0x400000000L,
        0x800000000L,
        0x1000000000L,
        0x2000000000L,
        0x4000000000L,
        0x8000000000L,
        0x10000000000L,
        0x20000000000L,
        0x40000000000L,
        0x80000000000L,
        0x100000000000L,
        0x200000000000L,
        0x400000000000L,
        0x800000000000L,
        0x1000000000000L,
        0x2000000000000L,
        0x4000000000000L,
        0x8000000000000L,
        0x10000000000000L,
        0x20000000000000L,
        0x40000000000000L,
        0x80000000000000L,
        0x100000000000000L,
        0x200000000000000L,
        0x400000000000000L,
        0x800000000000000L,
        0x1000000000000000L,
        0x2000000000000000L,
        0x4000000000000000L,
        0x8000000000000000L
      };
  private static final long[] SEQ_ARRAY = new long[64];

  static {
    SEQ_ARRAY[0] = 1L;

    for (int i = 1; i < 64; i++) {
      SEQ_ARRAY[i] = (SEQ_ARRAY[i - 1] << 1) + 1;
    }
  }

  final long first8 = 255L << 56;

  /**
   * The minimal value present in this domain encoding. The domain can only encode small domains
   * within a range [minBound .. minBound + 63].
   */
  public int minBound;

  /**
   * It stores information about presence of the elements in the domain. If the least significant
   * bit is set then min + 63 is present. The most significant bit is always set as this domain
   * maintains invariant that minimum value always belongs to the domain.
   */
  public long bits;

  private boolean singleton;
  private int size;
  private int max;

  /**
   * Finds the index of the first interval in the input domain that overlaps with this domain.
   *
   * @param input the IntervalDomain to search
   * @param shift the shift applied to interval boundaries
   * @return the index of the first overlapping interval, or input.size if none found
   */
  private int findFirstOverlappingInterval(IntervalDomain input, int shift) {
    int i = 0;
    for (; i < input.size; i++) {
      if (input.intervals[i].max() + shift >= this.minBound) {
        break;
      }
    }
    return i;
  }

  /**
   * Converts an IntervalDomain into a bit representation aligned with this domain. Assumes the
   * caller has found the first overlapping interval and computed its length.
   *
   * @param input the IntervalDomain to convert
   * @param shift the shift to apply to interval boundaries
   * @param startIndex the index of the first overlapping interval
   * @param length the length of the overlap with the first interval
   * @return the bit representation of the overlapping intervals
   */
  private long convertIntervalsToBits(IntervalDomain input, int shift, int startIndex, int length) {
    long inBits = SEQ_ARRAY[length];

    int i = startIndex + 1;

    Interval next = null;
    for (; i < input.size; i++) {
      next = input.intervals[i];
      if (next.max() + shift > this.max) {
        break;
      }
      inBits = inBits << (next.max() - input.intervals[i - 1].max());
      inBits = inBits | SEQ_ARRAY[next.max() - next.min()];
    }

    inBits = inBits << Math.max(this.max - (input.intervals[i - 1].max() + shift), 0);

    if (i < input.size && next != null && next.min() + shift <= this.max) {
      inBits = inBits | SEQ_ARRAY[this.max - (next.min() + shift)];
    }

    inBits = inBits << (this.minBound + 63 - this.max);

    return inBits;
  }

  /**
   * Aligns the bits of another SmallDenseDomain to this domain's minBound. This shifts the input
   * domain's bits so they are positioned relative to this domain's minBound for bitwise operations.
   *
   * @param input the other SmallDenseDomain whose bits should be aligned
   * @return the aligned bits
   */
  private long alignBits(SmallDenseDomain input) {
    if (minBound <= input.minBound) {
      int shift = input.minBound - minBound;
      return shift < 64 ? input.bits >>> shift : 0;
    } else {
      int shift = minBound - input.minBound;
      return shift < 64 ? input.bits << shift : 0;
    }
  }

  /**
   * Copies metadata from this domain into the result domain and installs it on the variable. Sets
   * previousDomain to this.
   */
  private void installResultDomain(SmallDenseDomain result, int storeLevel, Var v) {
    result.modelConstraints = modelConstraints;
    result.searchConstraints = searchConstraints;
    result.stamp = storeLevel;
    result.previousDomain = this;
    result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
    result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
    ((IntVar) v).domain = result;
  }

  /**
   * Updates domain fields and notifies variable of domain change. Used when stamp == storeLevel.
   *
   * @param bitsResult the new bits value
   * @param newSize the new size
   * @param v the variable to notify
   */
  private void updateDomainInPlace(long bitsResult, int newSize, Var v) {
    bits = bitsResult;
    size = newSize;
    if (newSize == 1) {
      singleton = true;
    }
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (singleton) {
      v.domainHasChanged(GROUND);
    } else {
      v.domainHasChanged(BOUND);
    }
  }

  /**
   * Updates domain fields and notifies variable of domain change with event type detection. Used
   * when stamp == storeLevel.
   *
   * @param bitsResult the new bits value
   * @param newSize the new size
   * @param previousMin the previous minimum value
   * @param previousMax the previous maximum value
   * @param v the variable to notify
   */
  private void updateDomainInPlaceWithEvent(
      long bitsResult, int newSize, int previousMin, int previousMax, Var v) {
    bits = bitsResult;
    size = newSize;
    if (newSize == 1) {
      singleton = true;
    }
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (singleton) {
      v.domainHasChanged(GROUND);
    } else {
      if (previousMin != minBound || previousMax != max) {
        v.domainHasChanged(BOUND);
      } else {
        v.domainHasChanged(ANY);
      }
    }
  }

  /**
   * Creates a new domain result and installs it, then notifies variable. Used when stamp <
   * storeLevel.
   *
   * @param result the new domain result
   * @param storeLevel the store level
   * @param v the variable to update
   */
  private void installAndNotify(SmallDenseDomain result, int storeLevel, Var v) {
    if (ASSERTS_ENABLED && stamp >= storeLevel) {
      throw new IllegalStateException("Assertion failed");
    }
    installResultDomain(result, storeLevel, v);
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    if (result.singleton()) {
      v.domainHasChanged(GROUND);
    } else {
      v.domainHasChanged(BOUND);
    }
  }

  /**
   * Creates a new domain result and installs it, then notifies variable with event type detection.
   * Used when stamp < storeLevel.
   *
   * @param result the new domain result
   * @param storeLevel the store level
   * @param previousMin the previous minimum value
   * @param previousMax the previous maximum value
   * @param v the variable to update
   */
  private void installAndNotifyWithEvent(
      SmallDenseDomain result, int storeLevel, int previousMin, int previousMax, Var v) {
    if (ASSERTS_ENABLED && stamp >= storeLevel) {
      throw new IllegalStateException("Assertion failed");
    }
    installResultDomain(result, storeLevel, v);
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }
    if (result.singleton()) {
      v.domainHasChanged(GROUND);
    } else {
      if (previousMin != result.minBound || previousMax != result.max) {
        v.domainHasChanged(BOUND);
      } else {
        v.domainHasChanged(ANY);
      }
    }
  }

  /**
   * Notifies the variable of a domain change using the appropriate event type.
   *
   * @param isSingleton true if the domain is now a singleton.
   * @param boundEvent true if a bound (min or max) has changed.
   * @param v the variable to notify.
   */
  private static void notifyEvent(boolean isSingleton, boolean boundEvent, Var v) {
    if (isSingleton) {
      v.domainHasChanged(GROUND);
    } else {
      if (boundEvent) {
        v.domainHasChanged(BOUND);
      } else {
        v.domainHasChanged(ANY);
      }
    }
  }

  /**
   * Computes the event type based on whether the domain is a singleton or whether bounds changed.
   *
   * @param isSingleton true if the domain is now a singleton.
   * @param previousMin the previous minimum value.
   * @param currentMin the current minimum value.
   * @param previousMax the previous maximum value.
   * @param currentMax the current maximum value.
   * @return the event type (GROUND, BOUND, or ANY).
   */
  private static int computeEventType(
      boolean isSingleton, int previousMin, int currentMin, int previousMax, int currentMax) {
    if (isSingleton) {
      return GROUND;
    } else {
      if (previousMin != currentMin || previousMax != currentMax) {
        return BOUND;
      } else {
        return ANY;
      }
    }
  }

  /**
   * Applies complement operation when stamp == storeLevel. Modifies this domain in place and
   * notifies the variable.
   *
   * @param bitsResult the resulting bits after complement operation.
   * @param newSize the new domain size.
   * @param complementMin the minimum of the complement range.
   * @param complementMax the maximum of the complement range.
   * @param previousMin the previous minimum value.
   * @param previousMax the previous maximum value.
   * @param v the variable to notify.
   */
  private void applyComplementInPlace(
      long bitsResult,
      int newSize,
      int complementMin,
      int complementMax,
      int previousMin,
      int previousMax,
      Var v) {
    bits = bitsResult;
    size = newSize;
    if (newSize == 1) {
      singleton = true;
    }

    boolean boundEvent = false;
    if (this.minBound == complementMin) {
      boundEvent = true;
      adaptMin();
    }
    if (this.max == complementMax) {
      this.max = previousValue(complementMax);
      boundEvent = true;
    }

    if (ASSERTS_ENABLED && max > previousMax) {
      throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
    }
    if (ASSERTS_ENABLED && minBound < previousMin) {
      throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
    }
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    notifyEvent(singleton, boundEvent, v);
  }

  /**
   * Applies complement operation when stamp != storeLevel. Creates a new result domain, installs
   * it, and notifies the variable.
   *
   * @param bitsResult the resulting bits after complement operation.
   * @param newSize the new domain size.
   * @param complementMin the minimum of the complement range.
   * @param complementMax the maximum of the complement range.
   * @param storeLevel the current store level.
   * @param v the variable to notify.
   */
  private void applyComplementNewLevel(
      long bitsResult, int newSize, int complementMin, int complementMax, int storeLevel, Var v) {
    SmallDenseDomain result = new SmallDenseDomain(minBound, bitsResult);

    boolean boundEvent = false;
    if (this.minBound == complementMin) {
      result.adaptMin();
      boundEvent = true;
    }

    if (this.max == complementMax) {
      result.max = result.previousValue(max);
      boundEvent = true;
    }

    if (newSize == 1) {
      result.singleton = true;
    }

    if (ASSERTS_ENABLED && result.max > max) {
      throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
    }
    if (ASSERTS_ENABLED && result.minBound < minBound) {
      throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
    }

    installResultDomain(result, storeLevel, v);

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    notifyEvent(result.singleton(), boundEvent, v);
  }

  /** It creates an empty domain. */
  public SmallDenseDomain() {

    bits = 0;
    size = 0;
    singleton = false;
    minBound = Integer.MAX_VALUE;
    max = Integer.MIN_VALUE;
  }

  /**
   * It creates a domain of type small dense.
   *
   * @param min the minimum value present in this domain.
   * @param bits the bits representing presence of any value from the range [ min .. min + 63].
   */
  public SmallDenseDomain(int min, long bits) {

    if (bits != 0) {

      this.minBound = min;
      this.bits = bits;

      adaptMin();
      this.size = getSize(bits);

      this.singleton = size == 1;

      this.max = min + 63;
      this.max = previousValue(this.minBound + 64);

    } else {

      size = 0;
      singleton = false;
      max = Integer.MIN_VALUE;
    }
  }

  /**
   * It creates a domain with values between min and max inclusive.
   *
   * @param min min element in the domain
   * @param max max element in the domain
   */
  public SmallDenseDomain(int min, int max) {

    if (min <= max) {

      this.minBound = min;

      this.bits = -1;
      this.bits = this.bits << (63 - (max - min));
      this.size = getSize(bits);

      this.singleton = size == 1;

      this.max = max;

    } else {

      bits = 0;
      size = 0;
      singleton = false;
    }
  }

  /** {@inheritDoc} */
  @Override
  public IntDomain complement() {

    IntDomain intervalBasedRepresentation = this.toIntervalDomain();

    return intervalBasedRepresentation.complement();
  }

  /**
   * Returns the previous domain state before the last modification.
   *
   * @return the previous domain
   */
  public IntDomain getPreviousDomain() {
    return previousDomain;
  }

  @Override
  public boolean contains(IntDomain domain) {

    if (domain.isEmpty()) {
      return true;
    }

    if (isEmpty()) {
      return false;
    }

    if (domain.min() < this.minBound || domain.max() > this.max) {
      return false;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      // no problem with shift modulo 64 as it is always lower than 64.
      long bitsResult = this.bits | (input.bits >>> (input.minBound - this.minBound));

      return bitsResult == this.bits;
    }

    if (size < domain.getSize()) {
      return false;
    }

    boolean result = super.contains(domain);

    if (ASSERTS_ENABLED && !(result == this.toIntervalDomain().contains(domain))) {
      throw new IllegalStateException(
          String.valueOf("Improper implementation of function contains " + this + "d" + domain));
    }

    return result;
  }

  @Override
  public boolean contains(int value) {

    return value >= minBound
        && value <= minBound + 63
        && (bits & TWO_N_ARRAY[63 - (value - minBound)]) != 0;
  }

  @Override
  public boolean contains(int min, int max) {

    if (min < this.minBound) {
      return false;
    }

    if (max > this.max) {
      return false;
    }

    long result = bits;

    result = result << min - this.minBound;
    result = result >>> (min - this.minBound);
    result = result >>> (this.minBound + 63 - max);

    return max - min + 1 == this.getSize(result);
  }

  @Override
  public boolean eq(IntDomain domain) {

    if (this.isEmpty()) {
      return domain.isEmpty();
    } else if (domain.isEmpty()) {
      return false;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      return input.minBound == this.minBound && input.bits == this.bits;
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain input = (IntervalDomain) domain;

      if (input.min() != this.minBound || input.max() != this.max || input.getSize() != this.size) {
        if (ASSERTS_ENABLED && super.eq(domain)) {
          throw new IllegalStateException("Assertion failed");
        }
        return false;
      }

      for (int i = input.size - 1; i > 0; i--) {
        if (isIntersecting(input.intervals[i - 1].max() + 1, input.intervals[i].min() - 1)) {
          if (ASSERTS_ENABLED && super.eq(domain)) {
            throw new IllegalStateException("Assertion failed");
          }
          return false;
        }
      }

      if (ASSERTS_ENABLED && !(super.eq(domain))) {
        throw new IllegalStateException(
            String.valueOf("Incorrect implementation for IntervalDomain and SmallDenseDomain."));
      }

      return true;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    return super.eq(domain);
  }

  private int getElementAtFromBits(long bitsVal, int startValue, int index) {
    long result = bitsVal;
    int value = startValue;
    while (index > 0) {
      if (result < 0) {
        index--;
      }
      result = result << 1;
      value++;
    }
    while (result > 0) {
      result = result << 1;
      value++;
    }
    return value;
  }

  @Override
  public int getElementAt(int index) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (index >= getSize()) {
      throw new IllegalArgumentException("The domain has less elements then index.");
    }

    return getElementAtFromBits(bits, minBound, index);
  }

  @Override
  public Interval getInterval(int position) {

    int no = 0;
    int shift = 0;
    long result = bits;
    boolean inInterval = false;
    int begin = Integer.MIN_VALUE;

    while (result != 0) {
      if (!inInterval && result < 0) {
        inInterval = true;
        if (no == position) {
          begin = minBound + shift;
        }
        no++;
        result = result << 1;
        shift++;
      }
      if (!inInterval) {
        result = result << 1;
        shift++;
      }
      if (inInterval && result < 0) {
        result = result << 1;
        shift++;
      }
      if (inInterval && result >= 0) {
        if (no - 1 == position) {
          return new Interval(begin, minBound + shift - 1);
        }
        inInterval = false;
        result = result << 1;
        shift++;
      }
    }

    if (ASSERTS_ENABLED) {
      throw new IllegalStateException(
          String.valueOf("Interval with a given number does not exist."));
    }
    return null;
  }

  @Override
  public int getSize() {

    if (ASSERTS_ENABLED && !(size == getSize(bits))) {
      throw new IllegalStateException(
          String.valueOf("size cache was not updated before correctly"));
    }

    return size;
  }

  /**
   * It computes the number of 1's in the binary representation of the number given in the field
   * input.
   *
   * @param input the 64bits for which calculation of number of 1's takes place.
   * @return the number of 1's.
   */
  public int getSize(long input) {

    long xDown = input & 0xffffffffL;
    xDown = xDown - ((xDown >>> 1) & 0x55555555);
    xDown = (xDown & 0x33333333) + ((xDown >>> 2) & 0x33333333);
    xDown = (xDown + (xDown >>> 4)) & 0x0f0f0f0f;
    xDown = xDown + (xDown >>> 8);
    xDown = xDown + (xDown >>> 16);

    long xUp = input >>> 32;
    xUp = xUp - ((xUp >>> 1) & 0x55555555);
    xUp = (xUp & 0x33333333) + ((xUp >>> 2) & 0x33333333);
    xUp = (xUp + (xUp >>> 4)) & 0x0f0f0f0f;
    xUp = xUp + (xUp >>> 8);
    xUp = xUp + (xUp >>> 16);

    return ((int) xDown & 0x0000003f) + ((int) xUp & 0x0000003f);
  }

  @Override
  public void inValue(int storeLevel, IntVar v, int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (singleton && value == minBound) { // singleton(c)
      return;
    }

    if (!contains(value)) {
      throw failException;
    }

    // Pruning has occurred.

    if (stamp == storeLevel) {

      bits = 1L << 63;
      minBound = value;
      max = value;
      singleton = true;
      size = 1;

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      v.domainHasChanged(GROUND);

    } else {

      SmallDenseDomain result = new SmallDenseDomain();
      result.bits = 1L << 63;
      result.minBound = value;
      result.max = value;
      result.singleton = true;
      result.size = 1;

      installAndNotify(result, storeLevel, v);
    }
  }

  /** Computes pruned bits for in(min, max); returns null if no pruning or early return. */
  private long computeInBitsResult(int min, int max) {
    if (max < this.minBound || min > this.max) {
      throw failException;
    }
    if (min <= this.minBound && max >= this.max || singleton) {
      return -1; // sentinel: no change
    }
    long bitsResult = bits;
    if (this.max - max > 0) {
      int thisMax = this.minBound + 63;
      bitsResult = bitsResult >>> (thisMax - max);
      if (min - this.minBound > 0) {
        bitsResult = bitsResult << (min - this.minBound + thisMax - max);
        bitsResult = bitsResult >>> (min - this.minBound);
      } else {
        bitsResult = bitsResult << (thisMax - max);
      }
    } else {
      if (min - this.minBound > 0) {
        bitsResult = bitsResult << (min - this.minBound);
        bitsResult = bitsResult >>> (min - this.minBound);
      } else {
        return -1; // nothing to prune
      }
    }
    return bitsResult;
  }

  /** {@inheritDoc} */
  @Override
  public void in(int storeLevel, Var v, int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException(
          String.valueOf("Min value greater than max value " + min + " > " + max));
    }

    long bitsResult = computeInBitsResult(min, max);
    if (bitsResult == -1) {
      return;
    }

    int newSize = getSize(bitsResult);
    if (newSize == 0) {
      throw failException;
    }
    if (ASSERTS_ENABLED && newSize >= size) {
      throw new IllegalStateException(String.valueOf(INCORRECT_IN_OPERATION));
    }

    if (stamp == storeLevel) {
      bits = bitsResult;
      size = newSize;
      if (newSize == 1) {
        singleton = true;
      }
      if (this.minBound < min) {
        bits = bits << (min - this.minBound);
        this.minBound = min;
        adaptMin();
      }
      if (this.max > max) {
        this.max = previousValue(max + 1);
      }
      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }
      v.domainHasChanged(singleton ? GROUND : BOUND);
      return;
    }

    if (ASSERTS_ENABLED && stamp >= storeLevel) {
      throw new IllegalStateException("Assertion failed");
    }
    SmallDenseDomain result =
        this.minBound < min
            ? new SmallDenseDomain(min, bitsResult << (min - this.minBound))
            : new SmallDenseDomain(this.minBound, bitsResult);
    if (this.minBound < min) {
      result.adaptMin();
    }
    if (newSize == 1) {
      result.singleton = true;
    }
    if (this.max > max) {
      result.max = result.previousValue(max + 1);
    }
    if (ASSERTS_ENABLED && result.max > max) {
      throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
    }
    if (ASSERTS_ENABLED && result.minBound < min) {
      throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
    }
    installAndNotify(result, storeLevel, v);
  }

  /**
   * Restricts the domain to the intersection with the given bit representation.
   *
   * @param storeLevel the level of the store
   * @param v the variable to update
   * @param domain the bit representation of the domain to intersect with
   */
  public void in(int storeLevel, Var v, long domain) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    long bitsResult = bits & domain;

    if (bitsResult == bits) {
      return;
    }

    int newSize = getSize(bitsResult);

    if (newSize == 0) {
      throw failException;
    }

    // Pruning has occurred.

    int previousMin = minBound;
    int previousMax = max;

    if (stamp == storeLevel) {

      bits = bitsResult;
      size = newSize;
      if (newSize == 1) {
        singleton = true;
      }

      adaptMin();
      max = previousValue(max + 1);

      if (ASSERTS_ENABLED && max > previousMax) {
        throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
      }
      if (ASSERTS_ENABLED && minBound < previousMin) {
        throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
      }

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      notifyEvent(singleton, previousMin != minBound || previousMax != max, v);

    } else {

      SmallDenseDomain result = new SmallDenseDomain(minBound, bitsResult);

      if (ASSERTS_ENABLED && result.max > previousMax) {
        throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
      }
      if (ASSERTS_ENABLED && result.minBound < previousMin) {
        throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
      }

      installAndNotifyWithEvent(result, storeLevel, previousMin, previousMax, v);
    }
  }

  @Override
  public void in(int storeLevel, Var v, IntDomain domain) {

    if (domain.singleton()) {
      in(storeLevel, v, domain.value(), domain.value());
      return;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      long inBits = alignBits(input);

      in(storeLevel, v, inBits);
      return;
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain input = (IntervalDomain) domain;

      int i = findFirstOverlappingInterval(input, 0);

      if (i == input.size) {
        throw Store.failException;
      }

      Interval first = input.intervals[i];
      int length = Math.min(first.max(), this.max) - Math.max(this.minBound, first.min());

      if (length == this.max - this.minBound) {
        return;
      }

      if (length < 0) {
        throw Store.failException;
      }

      long inBits = convertIntervalsToBits(input, 0, i, length);

      in(storeLevel, v, inBits);

      if (ASSERTS_ENABLED && domain.complement().isIntersecting((IntDomain) v.dom())) {
        throw new IllegalStateException(String.valueOf("Error either in in or isIntersecting."));
      }

      return;
    }

    if (ASSERTS_ENABLED && !(domain.max() - domain.min() + 1 == domain.getSize())) {
      throw new IllegalStateException(String.valueOf("Loosing propagation" + domain));
    }

    in(storeLevel, v, domain.min(), domain.max());
  }

  private void adaptMin() {

    if (ASSERTS_ENABLED && !(bits != 0)) {
      throw new IllegalStateException(String.valueOf("Empty domain, min can not be adapted."));
    }

    while ((bits & first8) == 0) {
      minBound += 8;
      bits = bits << 8;
    }

    while ((bits & TWO_N_ARRAY[63]) == 0) {
      minBound++;
      bits = bits << 1;
    }
  }

  @Override
  public void inComplement(int storeLevel, Var v, int complement) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (complement < minBound) {
      return;
    }
    if (complement > minBound + 63) {
      return;
    }

    long bitsResult = bits & ~TWO_N_ARRAY[63 - (complement - minBound)];

    if (bitsResult == bits) {
      return; // no change in the domain; ADDED BY KKU
    }
    int newSize = getSize(bitsResult);

    if (newSize == 0) {
      throw failException;
    }

    if (ASSERTS_ENABLED && newSize > size) {
      throw new IllegalStateException(String.valueOf(INCORRECT_IN_OPERATION));
    }

    if (newSize == size) {
      return;
    }

    // Pruning has occurred.

    if (stamp == storeLevel) {
      applyComplementInPlace(bitsResult, newSize, complement, complement, minBound, max, v);
    } else {
      applyComplementNewLevel(bitsResult, newSize, complement, complement, storeLevel, v);
    }
  }

  @Override
  public void inComplement(int storeLevel, Var v, int minComplement, int maxComplement) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (maxComplement < minBound) {
      return;
    }

    if (minComplement > max) {
      return;
    }

    if (minComplement < minBound) {
      minComplement = minBound;
    }

    if (maxComplement > max) {
      maxComplement = max;
    }

    long bitsResult =
        bits & ~(SEQ_ARRAY[maxComplement - minComplement] << (minBound + 63 - maxComplement));

    if (bitsResult == bits) {
      return;
    }

    int newSize = getSize(bitsResult);

    if (newSize == 0) {
      throw failException;
    }

    if (ASSERTS_ENABLED && newSize > size) {
      throw new IllegalStateException(String.valueOf(INCORRECT_IN_OPERATION));
    }

    if (newSize == size) {
      return;
    }

    // Pruning has occurred.

    if (stamp == storeLevel) {
      applyComplementInPlace(bitsResult, newSize, minComplement, maxComplement, minBound, max, v);
    } else {
      applyComplementNewLevel(bitsResult, newSize, minComplement, maxComplement, storeLevel, v);
    }
  }

  @Override
  public void inMax(int storeLevel, Var v, int max) {

    if (max < minBound) {
      throw Store.failException;
    }

    in(storeLevel, v, minBound, max);
  }

  @Override
  public void inMin(int storeLevel, Var v, int min) {

    if (max < min) {
      throw Store.failException;
    }

    in(storeLevel, v, min, max);
  }

  private long computeInShiftBitsForSmallDense(SmallDenseDomain input, int shift) {
    if (minBound <= input.minBound + shift) {
      int internalShift = input.minBound + shift - minBound;
      return internalShift < 64 ? input.bits >>> internalShift : 0L;
    }
    int internalShift = minBound - input.minBound - shift;
    return internalShift < 64 ? input.bits << internalShift : 0L;
  }

  private void applyInShiftForIntervalDomain(
      int storeLevel, Var v, IntervalDomain input, int shift) {
    int i = findFirstOverlappingInterval(input, shift);
    if (i == input.size) {
      throw Store.failException;
    }
    Interval first = input.intervals[i];
    int length =
        Math.min(first.max() + shift, this.max) - Math.max(this.minBound, first.min() + shift);
    if (length == this.max - this.minBound) {
      return;
    }
    if (length < 0) {
      throw Store.failException;
    }
    long inBits = convertIntervalsToBits(input, shift, i, length);
    in(storeLevel, v, inBits);
  }

  @Override
  public void inShift(int storeLevel, Var v, IntDomain domain, int shift) {

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {
      SmallDenseDomain input = (SmallDenseDomain) domain;
      in(storeLevel, v, computeInShiftBitsForSmallDense(input, shift));
      return;
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {
      applyInShiftForIntervalDomain(storeLevel, v, (IntervalDomain) domain, shift);
      return;
    }

    if (ASSERTS_ENABLED && !(domain.max() - domain.min() + 1 == domain.getSize())) {
      throw new IllegalStateException(String.valueOf("Loosing propagation" + domain));
    }

    in(storeLevel, v, domain.min() + shift, domain.max() + shift);
  }

  /**
   * It computes the intersection of this domain with an interval domain applying a shift.
   *
   * @param input the interval domain to intersect with.
   * @param shift the shift value to apply.
   * @return the resulting small dense domain after intersection.
   */
  public SmallDenseDomain intersect(IntervalDomain input, int shift) {

    // as normal domains (constraints).
    if (isEmpty()) {
      return emptyDomain;
    }

    long inBits = 0;

    int i = findFirstOverlappingInterval(input, shift);

    if (i == input.size) {
      return emptyDomain;
    }

    Interval first = input.intervals[i];
    int length =
        Math.min(first.max() + shift, this.max) - Math.max(this.minBound, first.min() + shift);

    if (length == this.max - this.minBound) {
      return this.cloneLight();
    }

    if (length < 0) {
      return emptyDomain;
    }

    inBits = convertIntervalsToBits(input, shift, i, length) & bits;

    return new SmallDenseDomain(this.minBound, inBits);
  }

  @Override
  public IntDomain intersect(IntDomain domain) {

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      if (input.bits == 0) {
        return IntervalDomain.EMPTY;
      }

      long inBits = alignBits(input);

      SmallDenseDomain result = new SmallDenseDomain(minBound, inBits & bits);

      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      return result;
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain input = (IntervalDomain) domain;

      SmallDenseDomain result = intersect(input, 0);

      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      return result;
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {

      IntervalDomain input = new IntervalDomain(domain.min(), domain.max());

      SmallDenseDomain result = intersect(input, 0);

      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      return result;
    }

    if (ASSERTS_ENABLED) {
      throw new IllegalStateException(
          String.valueOf("Not implemented for class " + domain.getClass()));
    }

    return null;
  }

  @Override
  public IntDomain intersect(int min, int max) {

    IntDomain result = this.cloneLight();

    result.intersectAdapt(min, max);

    return result;
  }

  @Override
  public int intersectAdapt(IntDomain domain) {

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      long inBits = alignBits(input);

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      long bitsResult = bits & inBits;

      if (bitsResult == bits) {
        return NONE;
      }

      int newSize = getSize(bitsResult);

      if (newSize == 0) {
        clear();
        return GROUND;
      }

      // Pruning has occurred.

      final int previousMin = minBound;
      final int previousMax = max;

      bits = bitsResult;
      size = newSize;
      if (newSize == 1) {
        singleton = true;
      }

      adaptMin();
      max = previousValue(max + 1);

      if (ASSERTS_ENABLED && max > previousMax) {
        throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
      }
      if (ASSERTS_ENABLED && minBound < previousMin) {
        throw new IllegalStateException(String.valueOf(DOMAIN_UPDATE_INCORRECT));
      }

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      return computeEventType(singleton, previousMin, minBound, previousMax, max);
    }

    if (domain.domainId() == INTERVAL_DOMAIN_ID) {

      IntervalDomain input = (IntervalDomain) domain;

      SmallDenseDomain result = this.intersect(input, 0);

      if (ASSERTS_ENABLED && !(result.eq(this.toIntervalDomain().intersect(input)))) {
        throw new IllegalStateException(
            String.valueOf(
                "Intersection not properly computed." + this + "i" + input + "r" + result));
      }

      if (ASSERTS_ENABLED && result.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(result.checkInvariants()));
      }

      final int previousMin = minBound;
      final int previousMax = max;

      setDomain(result);

      if (isEmpty()) {
        return GROUND;
      }

      return computeEventType(singleton, previousMin, minBound, previousMax, max);
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {

      BoundDomain input = (BoundDomain) domain;

      final int previousMin = minBound;
      final int previousMax = max;

      intersectAdapt(input.min(), input.max());

      if (isEmpty()) {
        return GROUND;
      }

      return computeEventType(singleton, previousMin, minBound, previousMax, max);
    }

    if (ASSERTS_ENABLED) {
      throw new IllegalStateException(
          String.valueOf("Not implemented for class " + domain.getClass()));
    }
    return -1;
  }

  @Override
  public int intersectAdapt(int min, int max) {

    if (isEmpty()) {
      return NONE;
    }

    if (min <= this.minBound && max >= this.max) {
      return NONE;
    }

    if (this.max < min || this.minBound > max) {
      clear();
      return GROUND;
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    min = Math.max(min, this.minBound);
    max = Math.min(max, this.max);

    long result = SEQ_ARRAY[max - min] << (63 - (max - min));

    bits = (bits << min - this.minBound) & result;

    this.minBound = min;
    this.max = max;
    this.size = getSize(bits);
    this.singleton = this.size == 1;

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (!singleton) {
      return BOUND;
    } else {
      return GROUND;
    }
  }

  @Override
  public IntervalEnumeration intervalEnumeration() {

    return new SmallDenseDomainIntervalEnumeration(this);
  }

  @Override
  public boolean isIntersecting(IntDomain domain) {

    if (domain.isEmpty() || isEmpty()) {
      return false;
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      long inBits = alignBits(input) & bits;

      if (inBits != 0) {
        if (ASSERTS_ENABLED && !(super.isIntersecting(domain))) {
          throw new IllegalStateException(
              String.valueOf("isIntersecting not properly implemented"));
        }
        return true;
      } else {
        if (ASSERTS_ENABLED && super.isIntersecting(domain)) {
          throw new IllegalStateException(
              String.valueOf("isIntersecting not properly implemented"));
        }
        return false;
      }
    }

    boolean result = super.isIntersecting(domain);

    if (ASSERTS_ENABLED && !(result == this.toIntervalDomain().isIntersecting(domain))) {
      throw new IllegalStateException(
          String.valueOf(
              "isIntersecting not properly implemented."
                  + this
                  + "d"
                  + domain
                  + "result "
                  + result));
    }

    return result;
  }

  @Override
  public boolean isIntersecting(int min, int max) {

    if (ASSERTS_ENABLED && min > max) {
      throw new IllegalStateException(String.valueOf("Illegal arguments min is greater than max"));
    }

    if (this.max < min || this.minBound > max) {
      return false;
    }

    long result = bits;

    int shiftLeft = min - this.minBound;

    if (shiftLeft > 0) {
      result = result << shiftLeft;
    }

    if (result < 0) {
      return true;
    }

    if (shiftLeft > 0) {
      result = result >>> shiftLeft;
    }
    result = result >>> Math.max(0, 63 + this.minBound - max);

    return result != 0;

    // Used in AbsXeqY, Regular.
  }

  @Override
  public int max() {

    if (ASSERTS_ENABLED && !(bits != 0)) {
      throw new IllegalStateException(String.valueOf("max function called for an empty domain"));
    }

    return max;
  }

  @Override
  public int min() {

    if (ASSERTS_ENABLED && !((bits & TWO_N_ARRAY[63]) != 0)) {
      throw new IllegalStateException(
          String.valueOf("Inconsistent field min when compared to bits." + this));
    }

    return minBound;
  }

  @Override
  public int nextValue(int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    long temp = bits;

    if (value < minBound) {
      return minBound;
    }

    int shift = value - this.minBound + 1;

    if (shift < 64) {
      temp = temp << shift;
    } else {
      temp = 0;
    }

    if (temp == 0) {
      return value;
    }

    while (true) {

      long sequence8 = temp & first8;

      if (sequence8 == 0) {
        temp = temp << 8;
        shift += 8;
      } else {
        return nextValueInByte(temp, shift);
      }
    }
  }

  /**
   * Scans the high 8 bits of temp for the next set bit and returns the corresponding value.
   *
   * @param temp the shifted bit vector (high 8 bits are scanned).
   * @param shift current shift amount (0-based position from minBound).
   * @return minBound + shift for the first set bit in the high byte.
   */
  private int nextValueInByte(long temp, int shift) {

    for (int i = 7; i >= 0; i--) {
      if (temp < 0) {
        return minBound + shift;
      }
      temp = temp << 1;
      shift++;
    }

    if (ASSERTS_ENABLED) {
      throw new IllegalStateException(String.valueOf("It should not be here."));
    }
    return minBound + shift;
  }

  @Override
  public int noIntervals() {

    int no = 0;
    long result = bits;
    boolean inInterval = false;

    while (result != 0) {
      if (!inInterval && result < 0) {
        inInterval = true;
        no++;
        result = result << 1;
      }
      if (inInterval && result > 0) {
        inInterval = false;
        result = result << 1;
      }
      if (inInterval && result < 0) {
        result = result << 1;
      }
      if (!inInterval && result > 0) {
        result = result << 1;
      }
    }

    return no;
  }

  @Override
  public int previousValue(int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    long temp = bits;
    int shift = this.minBound + 63 - Math.min(max, value - 1);

    if (shift < 64) {
      temp = temp >>> shift;
    } else {
      temp = 0;
    }

    if (temp == 0) {
      return value;
    }

    while (true) {

      long sequence8 = temp & 255;

      if (sequence8 == 0) {
        temp = temp >>> 8;
        shift += 8;
      } else {
        for (int i = 7; i >= 0; i--) {
          if ((temp & 0x1) != 0) {
            return minBound + 63 - shift;
          } else {
            temp = temp >>> 1;
            shift++;
          }
        }

        if (ASSERTS_ENABLED) {
          throw new IllegalStateException(String.valueOf("It should not be here."));
        }
      }
    }
  }

  @Override
  public IntDomain recentDomainPruning(int storeLevel) {

    if (previousDomain == null) {
      return IntervalDomain.emptyDomain;
    }

    if (stamp < storeLevel) {
      return IntervalDomain.emptyDomain;
    }

    IntDomain previous = this.previousDomain;
    while (previous.stamp > storeLevel) {
      if (previous.domainId() == SMALL_DENSE_DOMAIN_ID) {
        previous = previous.previousDomain;
      } else if (previous.domainId() == INTERVAL_DOMAIN_ID) {
        previous = previous.previousDomain;
      }
    }

    if (previous.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain _previous = (SmallDenseDomain) previous;
      long result = _previous.bits;
      long current = this.bits >>> (this.minBound - _previous.minBound);

      return new SmallDenseDomain(_previous.minBound, result ^ current);
    }

    return previous.subtract(this);
  }

  @Override
  public void setDomain(IntDomain domain) {

    if (domain.isEmpty()) {
      clear();
      return;
    }

    if (domain.max() - domain.min() > 63) {
      throw new IllegalArgumentException(
          "The resulting domain can not be handled properly by " + this.getClass());
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain smallDomain = (SmallDenseDomain) domain;

      this.bits = smallDomain.bits;
      this.minBound = smallDomain.minBound;
      this.max = smallDomain.max;
      this.size = smallDomain.size;
      this.singleton = smallDomain.singleton;

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

    this.minBound = min;

    this.bits = -1;
    this.bits = this.bits << (63 - (max - min));
    this.size = getSize(bits);
    this.singleton = size == 1;

    this.max = max;
  }

  @Override
  public boolean singleton(int c) {

    // It is used by Lex in set package.

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    return size == 1 && c == minBound;
  }

  @Override
  public boolean singleton() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    return singleton;
  }

  @Override
  public IntDomain subtract(int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    // Used in set package, BoundSetDomain.
    IntDomain result = subtract(value, value);

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result;
  }

  @Override
  public IntDomain subtract(IntDomain domain) {

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      long negBits;

      if (input.minBound >= this.minBound) {
        int shift = input.minBound - this.minBound;
        if (shift < 64) {
          negBits = input.bits >>> shift;
        } else {
          negBits = 0;
        }
      } else {
        int shift = this.minBound - input.minBound;
        if (shift < 64) {
          negBits = input.bits << shift;
        } else {
          negBits = 0;
        }
      }

      long result = this.bits & (~negBits);

      if (result != 0) {
        return new SmallDenseDomain(this.minBound, result);
      } else {
        return IntervalDomain.EMPTY;
      }
    }

    IntDomain result = super.subtract(domain);

    if (ASSERTS_ENABLED && !(result.eq(this.toIntervalDomain().subtract(domain)))) {
      throw new IllegalStateException(
          String.valueOf(
              "Subtraction not properly implemented " + this + "d " + domain + "res" + result));
    }

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result;
  }

  @Override
  public IntDomain subtract(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (min > this.max || max < this.minBound) {
      return this.cloneLight();
    }

    min = Math.max(min, this.minBound);
    max = Math.min(max, this.max);

    long result = this.bits & ~(SEQ_ARRAY[max - min] << (63 - (max - min) - (min - this.minBound)));

    if (result == 0) {
      return IntervalDomain.EMPTY;
    } else {
      SmallDenseDomain returnObj = new SmallDenseDomain(this.minBound, result);
      if (ASSERTS_ENABLED && returnObj.checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(returnObj.checkInvariants()));
      }

      return returnObj;
    }
  }

  @Override
  public void subtractAdapt(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (min > this.max || max < this.minBound) {
      return;
    }

    min = Math.max(min, this.minBound);
    max = Math.min(max, this.max);

    bits = bits & ~(SEQ_ARRAY[max - min] << (63 - (max - min) - (min - this.minBound)));

    if (bits == 0) {
      // it became empty.
      size = 0;
      singleton = false;
      return;
    }

    this.size = getSize(bits);
    this.singleton = this.size == 1;

    if (min <= this.minBound) {

      if (max < this.max) {

        // min <= this.minBound
        // max < this.max
        adaptMin();
      }

    } else {
      // min > this.minBound

      // when max < this.max, no changes to min and max are needed
      if (max >= this.max) {
        this.max = previousValue(min);
      }
    }
  }

  @Override
  public void subtractAdapt(int value) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    if (!contains(value)) {
      return;
    }

    if (singleton) {
      clear();
      return;
    }

    bits = bits & ~TWO_N_ARRAY[minBound - value + 63];

    size--;

    if (size == 1) {
      singleton = true;
    }

    if (value == minBound) {
      adaptMin();
    }

    if (value == max) {
      max = previousValue(value);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  @Override
  public IntDomain union(IntDomain domain) {

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain input = (SmallDenseDomain) domain;

      int newMax = Math.max(this.max, input.max);

      if (this.minBound <= input.minBound) {

        if (ASSERTS_ENABLED && this.minBound + 63 < newMax) {
          throw new IllegalStateException(
              String.valueOf("Union of two SmallDenseDomain does not fit in SmallDenseDomain"));
        }

        long bitsResult = this.bits | (input.bits >>> (input.minBound - this.minBound));

        return new SmallDenseDomain(this.minBound, bitsResult);

      } else {

        if (ASSERTS_ENABLED && input.minBound + 63 < newMax) {
          throw new IllegalStateException(
              String.valueOf("Union of two SmallDenseDomain does not fit in SmallDenseDomain"));
        }

        long bitsResult = input.bits | (this.bits >>> (this.minBound - input.minBound));

        return new SmallDenseDomain(input.minBound, bitsResult);
      }
    }

    IntDomain result = super.union(domain);

    if (ASSERTS_ENABLED && !(result.eq(this.toIntervalDomain().union(domain)))) {
      throw new IllegalStateException(
          String.valueOf("Union not properly implemented " + this + "d" + domain + "res" + result));
    }

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result;
  }

  @Override
  public IntDomain union(int min, int max) {

    IntDomain result = this.cloneLight();

    result.unionAdapt(min, max);

    return result;
  }

  @Override
  public IntDomain union(int value) {

    IntDomain result = union(value, value);

    if (ASSERTS_ENABLED && result.checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(result.checkInvariants()));
    }

    return result;
  }

  @Override
  public void unionAdapt(Interval i) {

    unionAdapt(i.min(), i.max());
  }

  @Override
  public void unionAdapt(int min, int max) {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    long result = SEQ_ARRAY[max - min] << (63 - (max - min));

    if (isEmpty()) {

      this.bits = result;
      this.minBound = min;
      this.max = max;
      this.size = max - min + 1;
      this.singleton = this.size == 1;

      if (ASSERTS_ENABLED && checkInvariants() != null) {
        throw new IllegalStateException(String.valueOf(checkInvariants()));
      }

      return;
    }

    int newMax = Math.max(this.max, max);
    int newMin = Math.min(this.minBound, min);

    if (newMax - newMin > 63) {
      throw new IllegalArgumentException(
          "The resulting domain can not be handled properly by " + this.getClass());
    }

    result = result >>> Math.max(min - newMin, 0) | (bits >>> Math.max(this.minBound - newMin, 0));

    this.bits = result;
    this.minBound = newMin;
    this.max = newMax;
    this.size = getSize(result);
    this.singleton = this.size == 1;

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  @Override
  public void unionAdapt(int value) {

    unionAdapt(value, value);
  }

  @Override
  public ValueEnumeration valueEnumeration() {

    return new SmallDenseDomainValueEnumeration(this);
  }

  @Override
  public String checkInvariants() {

    if (ASSERTS_ENABLED && !(singleton || getSize(bits) != 1)) {
      throw new IllegalStateException(String.valueOf("Singleton value was not recognized"));
    }

    if (bits != 0) {
      min();
    }

    return null;
  }

  @Override
  public void clear() {

    bits = 0;
    size = 0;
    singleton = false;
    minBound = Integer.MAX_VALUE;
    max = Integer.MIN_VALUE;
  }

  @Override
  public SmallDenseDomain copy() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    SmallDenseDomain cloned = new SmallDenseDomain(minBound, bits);

    cloned.stamp = stamp;
    cloned.previousDomain = previousDomain;

    cloned.searchConstraints = searchConstraints;
    cloned.searchConstraintsToEvaluate = searchConstraintsToEvaluate;

    cloned.modelConstraints = modelConstraints;
    cloned.modelConstraintsToEvaluate = modelConstraintsToEvaluate;

    cloned.searchConstraintsCloned = searchConstraintsCloned;

    return cloned;
  }

  @Override
  public int domainId() {

    return SMALL_DENSE_DOMAIN_ID;
  }

  @Override
  public boolean isEmpty() {

    return bits == 0;
  }

  @Override
  public boolean isNumeric() {

    return true;
  }

  @Override
  public boolean isSparseRepresentation() {

    // (e.g. it should return false for dense domains).
    return true;
  }

  /**
   * It clones the domain object, only data responsible for encoding domain values is cloned. All
   * other fields must be set separately.
   *
   * @return It returns a clone of this domain.
   */
  public SmallDenseDomain cloneLight() {

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }

    return new SmallDenseDomain(this.minBound, this.bits);
  }

  @Override
  public void removeLevel(int level, Var v) {

    if (ASSERTS_ENABLED && this.stamp > level) {
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
  public int sizeConstraintsOriginal() {

    IntDomain domain = this;

    while (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {

      SmallDenseDomain dom = (SmallDenseDomain) domain;

      if (dom.previousDomain != null) {
        domain = dom.previousDomain;
      } else {
        break;
      }
    }

    if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {
      return domain.modelConstraintsToEvaluate[0]
          + domain.modelConstraintsToEvaluate[1]
          + domain.modelConstraintsToEvaluate[2];
    } else {
      return domain.sizeConstraintsOriginal();
    }
  }

  @Override
  public String toString() {

    return this.toIntervalDomain().toString();
  }

  @Override
  public String toStringConstraints() {

    return toString();
  }

  @Override
  public String toStringFull() {

    return toString();
  }

  @Override
  public int getRandomValue() {

    int number = Store.getRandom().nextInt(size);
    int pos = 0;
    long temp = bits;
    while (number >= 0) {
      if (temp < 0) {
        if (number == 0) {
          return minBound + pos;
        }
        number--;
      }
      temp = temp << 1;
      pos++;
    }

    if (ASSERTS_ENABLED) {
      throw new IllegalStateException("Assertion failed");
    }
    return minBound;
  }

  /**
   * It shifts the domain.
   *
   * @param shift how much should the domain be shifted.
   */
  public void shift(int shift) {

    minBound += shift;
    max += shift;
  }

  /**
   * Converts this small dense domain to an equivalent interval domain representation.
   *
   * @return a new IntervalDomain containing the same values as this domain.
   */
  public IntervalDomain toIntervalDomain() {

    int noIntervals = this.noIntervals();
    IntervalDomain result = new IntervalDomain(noIntervals);

    for (int i = 0; i < noIntervals; i++) {
      result.intervals[i] = this.getInterval(i);
    }

    result.size = noIntervals;

    return result;
  }
}
