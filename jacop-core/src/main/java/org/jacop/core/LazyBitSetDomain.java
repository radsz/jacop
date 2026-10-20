/*
 * LazyBitSetDomain.java
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

import java.util.ArrayList;
import java.util.List;
import org.jacop.constraints.Constraint;

/**
 * A variable domain kept as bounds plus a bit set that is created only when the first hole appears,
 * after the domain variables of OR-Tools' constraint solver.
 *
 * <p>Unlike the other domains, which install a new domain object the first time a variable changes
 * at a search level, this domain is changed in place and keeps its own trail. The first change at a
 * level saves the bounds, the size, the stamp and the constraint lists; a word of the bit set is
 * saved the first time it changes at a level. Bounds are kept in fields and never touch the bit
 * set, so bits outside the bounds may be stale and every query is limited to the bounds.
 * Backtracking pops the trail entries of the removed levels.
 *
 * <p>A value enumeration works on a snapshot taken when it is created, as an enumeration of a
 * copied domain would: the bit set is copied on the next change instead of when the enumeration is
 * created.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class LazyBitSetDomain extends IntDomain {

  /** The largest number of values (max - min + 1) for which a variable gets this domain. */
  public static final int MAX_SPAN = 1 << 16;

  private static final int LEVEL_ENTRY = -1;

  private static final int INT_FIELDS = 6;

  private static final int OBJECT_FIELDS = 3;

  private int min;

  private int max;

  private int size;

  /** Bits of values base, base + 1, ...; null while the domain is an interval. */
  private long[] bits;

  private int base;

  /** The level at which each word was last saved. */
  private int[] wordStamp;

  /** Set when an enumeration may hold the bits array, which then must be copied before a change. */
  private boolean bitsShared;

  private int trailSize;

  /**
   * Per entry: kind (LEVEL_ENTRY or a word index), level, and for a level entry the old min, max,
   * size and stamp, for a word entry the old word stamp.
   */
  private int[] trailInts = new int[INT_FIELDS * 4];

  /** Per entry: the old word, or for a level entry whether bits were null and search data. */
  private long[] trailLongs = new long[4];

  /** Per level entry: old model constraints, old model constraint counts, old search list. */
  private Object[] trailObjects = new Object[OBJECT_FIELDS * 4];

  /**
   * It creates a domain with values between min and max inclusive.
   *
   * @param min the minimum value of the domain.
   * @param max the maximum value of the domain.
   */
  public LazyBitSetDomain(int min, int max) {
    if (min > max) {
      throw new IllegalArgumentException("Empty domain " + min + ".." + max);
    }
    this.min = min;
    this.max = max;
    this.size = max - min + 1;
    this.searchConstraints = new ArrayList<>();
  }

  // ---------- bit set helpers ----------

  private boolean present(int value) {
    if (bits == null) {
      return true;
    }
    int index = value - base;
    return (bits[index >>> 6] & (1L << index)) != 0;
  }

  /** The smallest value of the domain that is at least value, or max + 1. */
  private int nextPresent(int value) {
    if (value > max) {
      return max + 1;
    }
    if (value < min) {
      value = min;
    }
    if (bits == null) {
      return value;
    }
    int index = value - base;
    int word = index >>> 6;
    int lastWord = (max - base) >>> 6;
    long w = bits[word] & (-1L << index);
    while (w == 0) {
      if (++word > lastWord) {
        return max + 1;
      }
      w = bits[word];
    }
    int result = base + (word << 6) + Long.numberOfTrailingZeros(w);
    return result > max ? max + 1 : result;
  }

  /** The largest value of the domain that is at most value, or min - 1. */
  private int previousPresent(int value) {
    if (value < min) {
      return min - 1;
    }
    if (value > max) {
      value = max;
    }
    if (bits == null) {
      return value;
    }
    int index = value - base;
    int word = index >>> 6;
    int firstWord = (min - base) >>> 6;
    long w = bits[word] & (-1L >>> (63 - (index & 63)));
    while (w == 0) {
      if (--word < firstWord) {
        return min - 1;
      }
      w = bits[word];
    }
    int result = base + (word << 6) + 63 - Long.numberOfLeadingZeros(w);
    return result < min ? min - 1 : result;
  }

  /** The number of values of the domain in lo..hi, which must be within the bounds. */
  private int count(int lo, int hi) {
    if (lo > hi) {
      return 0;
    }
    if (bits == null) {
      return hi - lo + 1;
    }
    int from = lo - base;
    int to = hi - base;
    int firstWord = from >>> 6;
    int lastWord = to >>> 6;
    long firstMask = -1L << from;
    long lastMask = -1L >>> (63 - (to & 63));
    if (firstWord == lastWord) {
      return Long.bitCount(bits[firstWord] & firstMask & lastMask);
    }
    int result = Long.bitCount(bits[firstWord] & firstMask);
    for (int i = firstWord + 1; i < lastWord; i++) {
      result += Long.bitCount(bits[i]);
    }
    return result + Long.bitCount(bits[lastWord] & lastMask);
  }

  private void createBits(int storeLevel) {
    base = min;
    int words = ((max - min) >>> 6) + 1;
    bits = new long[words];
    wordStamp = new int[words];
    java.util.Arrays.fill(bits, -1L);
    // the level entry restores bits to null, so the words need no saving at this level
    java.util.Arrays.fill(wordStamp, storeLevel);
    bitsShared = false;
  }

  /**
   * Clears the values lo..hi, which must lie strictly inside the bounds, and returns how many
   * values were removed. The level must have been saved already.
   */
  private int clear(int storeLevel, int lo, int hi) {
    if (bits == null) {
      createBits(storeLevel);
    } else if (bitsShared) {
      bits = bits.clone();
      bitsShared = false;
    }
    int from = lo - base;
    int to = hi - base;
    int firstWord = from >>> 6;
    int lastWord = to >>> 6;
    int removed = 0;
    for (int i = firstWord; i <= lastWord; i++) {
      long mask = -1L;
      if (i == firstWord) {
        mask &= -1L << from;
      }
      if (i == lastWord) {
        mask &= -1L >>> (63 - (to & 63));
      }
      long old = bits[i];
      long cleared = old & mask;
      if (cleared != 0) {
        if (wordStamp[i] < storeLevel) {
          pushWord(i, storeLevel, old);
        }
        bits[i] = old & ~mask;
        removed += Long.bitCount(cleared);
      }
    }
    size -= removed;
    return removed;
  }

  // ---------- trail ----------

  private void ensureTrailCapacity() {
    if (trailSize == trailLongs.length) {
      int capacity = trailSize * 2;
      trailInts = java.util.Arrays.copyOf(trailInts, capacity * INT_FIELDS);
      trailLongs = java.util.Arrays.copyOf(trailLongs, capacity);
      trailObjects = java.util.Arrays.copyOf(trailObjects, capacity * OBJECT_FIELDS);
    }
  }

  private void pushWord(int word, int storeLevel, long old) {
    ensureTrailCapacity();
    int i = trailSize * INT_FIELDS;
    trailInts[i] = word;
    trailInts[i + 1] = storeLevel;
    trailInts[i + 2] = wordStamp[word];
    trailLongs[trailSize] = old;
    trailSize++;
    wordStamp[word] = storeLevel;
  }

  /**
   * Saves the state before the first change at storeLevel, as the other domains do by creating a
   * new domain object, and records the variable in the store's trail.
   */
  private void saveLevel(int storeLevel, Var v) {
    if (stamp >= storeLevel) {
      return;
    }
    ensureTrailCapacity();
    int i = trailSize * INT_FIELDS;
    trailInts[i] = LEVEL_ENTRY;
    trailInts[i + 1] = storeLevel;
    trailInts[i + 2] = min;
    trailInts[i + 3] = max;
    trailInts[i + 4] = size;
    trailInts[i + 5] = stamp;
    trailLongs[trailSize] =
        ((long) searchConstraintsToEvaluate << 2)
            | (searchConstraintsCloned ? 2L : 0L)
            | (bits == null ? 1L : 0L);
    int o = trailSize * OBJECT_FIELDS;
    trailObjects[o] = modelConstraints;
    trailObjects[o + 1] = modelConstraintsToEvaluate;
    trailObjects[o + 2] = searchConstraints;
    trailSize++;
    stamp = storeLevel;
    // a domain object created for a new level does not own the search constraint list
    searchConstraintsCloned = false;
    v.getStore().recordChange(v);
  }

  @Override
  @SuppressWarnings("unchecked")
  public void removeLevel(int level, Var v) {
    while (trailSize > 0 && trailInts[(trailSize - 1) * INT_FIELDS + 1] >= level) {
      trailSize--;
      int i = trailSize * INT_FIELDS;
      int kind = trailInts[i];
      if (kind == LEVEL_ENTRY) {
        min = trailInts[i + 2];
        max = trailInts[i + 3];
        size = trailInts[i + 4];
        stamp = trailInts[i + 5];
        long flags = trailLongs[trailSize];
        if ((flags & 1L) != 0) {
          bits = null;
          wordStamp = null;
        }
        searchConstraintsCloned = (flags & 2L) != 0;
        searchConstraintsToEvaluate = (int) (flags >>> 2);
        int o = trailSize * OBJECT_FIELDS;
        modelConstraints = (Constraint[][]) trailObjects[o];
        modelConstraintsToEvaluate = (int[]) trailObjects[o + 1];
        searchConstraints = (List<Constraint>) trailObjects[o + 2];
        trailObjects[o] = null;
        trailObjects[o + 1] = null;
        trailObjects[o + 2] = null;
      } else {
        if (bitsShared) {
          bits = bits.clone();
          bitsShared = false;
        }
        bits[kind] = trailLongs[trailSize];
        wordStamp[kind] = trailInts[i + 2];
      }
    }
  }

  /** It returns the position of the level entry of the most recent level, or -1. */
  private int lastLevelEntry() {
    for (int e = trailSize - 1; e >= 0; e--) {
      if (trailInts[e * INT_FIELDS] == LEVEL_ENTRY) {
        return e;
      }
    }
    return -1;
  }

  // ---------- events ----------

  private void changed(Var v, int oldMin, int oldMax) {
    if (min == max) {
      v.domainHasChanged(GROUND);
    } else if (min != oldMin || max != oldMax) {
      v.domainHasChanged(BOUND);
    } else {
      v.domainHasChanged(ANY);
    }
  }

  // ---------- pruning ----------

  @Override
  public void inMin(int storeLevel, Var v, int newMin) {
    if (newMin > max) {
      throw failException;
    }
    if (newMin <= min) {
      return;
    }
    int value = nextPresent(newMin);
    saveLevel(storeLevel, v);
    size -= count(min, value - 1);
    min = value;
    v.domainHasChanged(min == max ? GROUND : BOUND);
  }

  @Override
  public void inMax(int storeLevel, Var v, int newMax) {
    if (newMax < min) {
      throw failException;
    }
    if (newMax >= max) {
      return;
    }
    int value = previousPresent(newMax);
    saveLevel(storeLevel, v);
    size -= count(value + 1, max);
    max = value;
    v.domainHasChanged(min == max ? GROUND : BOUND);
  }

  @Override
  public void in(int storeLevel, Var v, int newMin, int newMax) {
    if (newMax < min || newMin > max) {
      throw failException;
    }
    if (newMin <= min && newMax >= max) {
      return;
    }
    int lo = nextPresent(newMin);
    if (lo > newMax) {
      throw failException;
    }
    int hi = previousPresent(newMax);
    saveLevel(storeLevel, v);
    size -= count(min, lo - 1) + count(hi + 1, max);
    min = lo;
    max = hi;
    v.domainHasChanged(min == max ? GROUND : BOUND);
  }

  @Override
  public void inValue(int storeLevel, IntVar v, int value) {
    if (min == value && max == value) {
      return;
    }
    if (!contains(value)) {
      throw failException;
    }
    saveLevel(storeLevel, v);
    min = value;
    max = value;
    size = 1;
    v.domainHasChanged(GROUND);
  }

  @Override
  public void inComplement(int storeLevel, Var v, int complement) {
    if (complement < min || complement > max || !present(complement)) {
      return;
    }
    if (min == max) {
      throw failException;
    }
    int oldMin = min;
    int oldMax = max;
    saveLevel(storeLevel, v);
    if (complement == min) {
      int value = nextPresent(complement + 1);
      size--;
      min = value;
    } else if (complement == max) {
      int value = previousPresent(complement - 1);
      size--;
      max = value;
    } else {
      clear(storeLevel, complement, complement);
    }
    changed(v, oldMin, oldMax);
  }

  @Override
  public void inComplement(int storeLevel, Var v, int lo, int hi) {
    if (lo > hi || hi < min || lo > max) {
      return;
    }
    if (lo <= min && hi >= max) {
      throw failException;
    }
    int oldMin = min;
    int oldMax = max;
    int oldSize = size;
    if (lo <= min) {
      int value = nextPresent(hi + 1);
      saveLevel(storeLevel, v);
      size -= count(min, value - 1);
      min = value;
    } else if (hi >= max) {
      int value = previousPresent(lo - 1);
      saveLevel(storeLevel, v);
      size -= count(value + 1, max);
      max = value;
    } else {
      if (count(lo, hi) == 0) {
        return;
      }
      saveLevel(storeLevel, v);
      clear(storeLevel, lo, hi);
    }
    if (size != oldSize) {
      changed(v, oldMin, oldMax);
    }
  }

  @Override
  public void in(int storeLevel, Var v, IntDomain domain) {
    if (domain.isEmpty()) {
      throw failException;
    }
    int intervals = domain.noIntervals();
    if (intervals == 1) {
      in(storeLevel, v, domain.min(), domain.max());
      return;
    }
    // the new bounds: the first and the last value of this domain within domain
    int lo = max + 1;
    for (int i = 0; i < intervals && lo > max; i++) {
      Interval interval = domain.getInterval(i);
      if (interval.max() >= min) {
        int candidate = nextPresent(interval.min());
        if (candidate <= interval.max()) {
          lo = candidate;
        }
      }
    }
    if (lo > max) {
      throw failException;
    }
    int hi = min - 1;
    for (int i = intervals - 1; i >= 0 && hi < min; i--) {
      Interval interval = domain.getInterval(i);
      if (interval.min() <= max) {
        int candidate = previousPresent(interval.max());
        if (candidate >= interval.min()) {
          hi = candidate;
        }
      }
    }
    int oldMin = min;
    int oldMax = max;
    int oldSize = size;
    // values of this domain in the gaps of domain between lo and hi
    boolean saved = false;
    for (int i = 0; i < intervals - 1; i++) {
      int gapLo = Math.max(domain.getInterval(i).max() + 1, lo + 1);
      int gapHi = Math.min(domain.getInterval(i + 1).min() - 1, hi - 1);
      if (gapLo <= gapHi && count(gapLo, gapHi) > 0) {
        if (!saved) {
          saveLevel(storeLevel, v);
          saved = true;
        }
        clear(storeLevel, gapLo, gapHi);
      }
    }
    if (lo != min || hi != max) {
      if (!saved) {
        saveLevel(storeLevel, v);
      }
      size -= count(min, lo - 1) + count(hi + 1, max);
      min = lo;
      max = hi;
    }
    if (size != oldSize) {
      changed(v, oldMin, oldMax);
    }
  }

  @Override
  public void inShift(int storeLevel, Var v, IntDomain domain, int shift) {
    IntervalDomain shifted = new IntervalDomain(domain.noIntervals() + 1);
    for (int i = 0; i < domain.noIntervals(); i++) {
      Interval interval = domain.getInterval(i);
      shifted.unionAdapt(interval.min() + shift, interval.max() + shift);
    }
    in(storeLevel, v, shifted);
  }

  // ---------- constraints ----------

  @Override
  public void putModelConstraint(int storeLevel, Var v, Constraint c, int pruningEvent) {
    saveLevel(storeLevel, v);
    super.putModelConstraint(storeLevel, v, c, pruningEvent);
  }

  @Override
  public void removeModelConstraint(int storeLevel, Var v, Constraint c) {
    saveLevel(storeLevel, v);
    super.removeModelConstraint(storeLevel, v, c);
  }

  @Override
  public void putSearchConstraint(int storeLevel, Var v, Constraint c) {
    if (!searchConstraints.contains(c)) {
      if (stamp < storeLevel) {
        saveLevel(storeLevel, v);
        // as a domain object created for a new level, take a copy of the active constraints
        searchConstraints =
            new ArrayList<>(searchConstraints.subList(0, searchConstraintsToEvaluate));
        searchConstraintsCloned = true;
      }
      super.putSearchConstraint(storeLevel, v, c);
    }
  }

  @Override
  public void removeSearchConstraint(int storeLevel, Var v, Constraint c) {
    saveLevel(storeLevel, v);
    super.removeSearchConstraint(storeLevel, v, c);
  }

  @Override
  public void removeSearchConstraint(int storeLevel, Var v, int position, Constraint c) {
    saveLevel(storeLevel, v);
    super.removeSearchConstraint(storeLevel, v, position, c);
  }

  // ---------- queries ----------

  @Override
  public int min() {
    return min;
  }

  @Override
  public int max() {
    return max;
  }

  @Override
  public int getSize() {
    return size;
  }

  @Override
  public boolean isEmpty() {
    return size == 0;
  }

  @Override
  public boolean singleton() {
    return min == max && size == 1;
  }

  @Override
  public boolean singleton(int c) {
    return min == c && max == c && size == 1;
  }

  @Override
  public int value() {
    return min;
  }

  @Override
  public boolean contains(int value) {
    return value >= min && value <= max && present(value);
  }

  @Override
  public boolean contains(int lo, int hi) {
    if (lo > hi) {
      return true;
    }
    if (lo < min || hi > max) {
      return false;
    }
    return count(lo, hi) == hi - lo + 1;
  }

  @Override
  public boolean isIntersecting(int lo, int hi) {
    if (lo > hi || hi < min || lo > max) {
      return false;
    }
    return nextPresent(lo) <= hi;
  }

  @Override
  public int nextValue(int value) {
    if (value == Integer.MAX_VALUE) {
      return value;
    }
    int next = nextPresent(value + 1);
    return next > max ? value : next;
  }

  @Override
  public int previousValue(int value) {
    if (value == Integer.MIN_VALUE) {
      return value;
    }
    int previous = previousPresent(value - 1);
    return previous < min ? value : previous;
  }

  @Override
  public int noIntervals() {
    if (size == 0) {
      return 0;
    }
    if (bits == null || size == max - min + 1) {
      return 1;
    }
    int result = 0;
    for (int value = min; value <= max; ) {
      result++;
      int end = endOfRun(value);
      value = nextPresent(end + 1);
    }
    return result;
  }

  /** The last value of the run of consecutive values starting at value, which is present. */
  private int endOfRun(int value) {
    if (bits == null) {
      return max;
    }
    int index = value - base;
    int word = index >>> 6;
    int lastWord = (max - base) >>> 6;
    long w = ~bits[word] & (-1L << index);
    while (w == 0) {
      if (++word > lastWord) {
        return max;
      }
      w = ~bits[word];
    }
    int result = base + (word << 6) + Long.numberOfTrailingZeros(w) - 1;
    return Math.min(result, max);
  }

  @Override
  public Interval getInterval(int position) {
    int value = min;
    for (int i = 0; i < position; i++) {
      value = nextPresent(endOfRun(value) + 1);
    }
    return new Interval(value, endOfRun(value));
  }

  @Override
  public int leftElement(int intervalNo) {
    return getInterval(intervalNo).min();
  }

  @Override
  public int rightElement(int intervalNo) {
    return getInterval(intervalNo).max();
  }

  @Override
  public int getElementAt(int index) {
    if (bits == null) {
      return min + index;
    }
    int value = min;
    while (true) {
      int end = endOfRun(value);
      if (index <= end - value) {
        return value + index;
      }
      index -= end - value + 1;
      value = nextPresent(end + 1);
    }
  }

  /**
   * It returns the domain as an interval domain.
   *
   * @return a new interval domain with the values of this domain.
   */
  public IntervalDomain toIntervalDomain() {
    if (size == 0) {
      return new IntervalDomain();
    }
    if (bits == null) {
      return new IntervalDomain(min, max);
    }
    IntervalDomain result = new IntervalDomain(4);
    for (int value = min; value <= max; ) {
      int end = endOfRun(value);
      result.unionAdapt(value, end);
      value = nextPresent(end + 1);
    }
    return result;
  }

  @Override
  public ValueEnumeration valueEnumeration() {
    if (bits != null) {
      bitsShared = true;
    }
    return new LazyBitSetDomainValueEnumeration(min, max, bits, base);
  }

  @Override
  public IntervalEnumeration intervalEnumeration() {
    return toIntervalDomain().intervalEnumeration();
  }

  @Override
  public int domainId() {
    return LAZY_BIT_SET_DOMAIN_ID;
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
  public int getRandomValue() {
    return toIntervalDomain().getRandomValue();
  }

  // ---------- previous domains ----------

  /**
   * {@inheritDoc}
   *
   * <p>The previous domain is rebuilt from the trail: it is this domain before the changes made at
   * the level of its stamp.
   */
  @Override
  public IntDomain getPreviousDomain() {
    int entry = lastLevelEntry();
    if (entry < 0) {
      return null;
    }
    int i = entry * INT_FIELDS;
    int oldMin = trailInts[i + 2];
    int oldMax = trailInts[i + 3];
    if ((trailLongs[entry] & 1L) != 0) {
      return new IntervalDomain(oldMin, oldMax);
    }
    long[] old = bits.clone();
    for (int e = trailSize - 1; e > entry; e--) {
      int word = trailInts[e * INT_FIELDS];
      old[word] = trailLongs[e];
    }
    IntervalDomain result = new IntervalDomain(4);
    for (int value = oldMin; value <= oldMax; value++) {
      int index = value - base;
      if ((old[index >>> 6] & (1L << index)) != 0) {
        result.unionAdapt(value, value);
      }
    }
    return result;
  }

  @Override
  public IntDomain recentDomainPruning(int storeLevel) {
    if (stamp < storeLevel) {
      return IntervalDomain.emptyDomain;
    }
    IntDomain previous = getPreviousDomain();
    if (previous == null) {
      return IntervalDomain.emptyDomain;
    }
    return previous.subtract(toIntervalDomain());
  }

  // ---------- operations creating new domains ----------

  @Override
  public IntDomain complement() {
    return toIntervalDomain().complement();
  }

  @Override
  public IntDomain intersect(IntDomain dom) {
    return toIntervalDomain().intersect(dom);
  }

  @Override
  public IntDomain intersect(int lo, int hi) {
    return toIntervalDomain().intersect(lo, hi);
  }

  @Override
  public IntDomain subtract(int lo, int hi) {
    return toIntervalDomain().subtract(lo, hi);
  }

  @Override
  public IntDomain subtract(int value) {
    return toIntervalDomain().subtract(value);
  }

  @Override
  public IntDomain subtract(IntDomain domain) {
    return toIntervalDomain().subtract(domain);
  }

  @Override
  public IntDomain union(IntDomain domain) {
    return toIntervalDomain().union(domain);
  }

  @Override
  public IntDomain union(int lo, int hi) {
    return toIntervalDomain().union(lo, hi);
  }

  @Override
  public IntDomain union(int value) {
    return toIntervalDomain().union(value);
  }

  @Override
  public boolean contains(IntDomain domain) {
    return toIntervalDomain().contains(domain);
  }

  @Override
  public boolean isIntersecting(IntDomain domain) {
    return toIntervalDomain().isIntersecting(domain);
  }

  @Override
  public boolean eq(IntDomain domain) {
    return toIntervalDomain().eq(domain);
  }

  @Override
  public int sizeOfIntersection(IntDomain domain) {
    return toIntervalDomain().sizeOfIntersection(domain);
  }

  @Override
  public IntDomain copy() {
    IntervalDomain result = toIntervalDomain();
    result.modelConstraints = modelConstraints;
    result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
    result.searchConstraints = searchConstraints;
    result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
    result.searchConstraintsCloned = searchConstraintsCloned;
    result.stamp = stamp;
    return result;
  }

  @Override
  public IntDomain cloneLight() {
    return toIntervalDomain();
  }

  // ---------- changes outside search (no level) ----------

  /**
   * Sets the domain from the values of an interval domain, outside of search.
   *
   * @param values the new values, not empty.
   */
  private void assign(IntDomain values) {
    if (values.isEmpty()) {
      min = 0;
      max = -1;
      size = 0;
      bits = null;
      wordStamp = null;
      return;
    }
    min = values.min();
    max = values.max();
    size = values.getSize();
    bits = null;
    wordStamp = null;
    if (size != max - min + 1) {
      createBits(stamp);
      long[] fresh = new long[bits.length];
      for (int i = 0; i < values.noIntervals(); i++) {
        Interval interval = values.getInterval(i);
        for (int value = interval.min(); value <= interval.max(); value++) {
          int index = value - base;
          fresh[index >>> 6] |= 1L << index;
        }
      }
      bits = fresh;
    }
  }

  @Override
  public void unionAdapt(int lo, int hi) {
    assign(toIntervalDomain().union(lo, hi));
  }

  @Override
  public void unionAdapt(Interval i) {
    unionAdapt(i.min(), i.max());
  }

  @Override
  public int unionAdapt(IntDomain union) {
    IntDomain result = toIntervalDomain().union(union);
    if (result.getSize() == size) {
      return NONE;
    }
    assign(result);
    return ANY;
  }

  @Override
  public void addDom(IntDomain domain) {
    assign(toIntervalDomain().union(domain));
  }

  @Override
  public void subtractAdapt(int value) {
    assign(toIntervalDomain().subtract(value));
  }

  @Override
  public void subtractAdapt(int lo, int hi) {
    assign(toIntervalDomain().subtract(lo, hi));
  }

  @Override
  public int intersectAdapt(IntDomain intersect) {
    IntDomain result = toIntervalDomain().intersect(intersect);
    if (result.getSize() == size) {
      return NONE;
    }
    assign(result);
    if (isEmpty()) {
      return GROUND;
    }
    return singleton() ? GROUND : ANY;
  }

  @Override
  public int intersectAdapt(int lo, int hi) {
    IntervalDomain current = toIntervalDomain();
    int result = current.intersectAdapt(lo, hi);
    assign(current);
    return result;
  }

  @Override
  public void setDomain(IntDomain domain) {
    assign(domain);
  }

  @Override
  public void setDomain(int lo, int hi) {
    assign(new IntervalDomain(lo, hi));
  }

  @Override
  public void clear() {
    assign(new IntervalDomain());
  }

  // ---------- printing ----------

  @Override
  public String toString() {
    return toIntervalDomain().toString();
  }

  @Override
  public String toStringConstraints() {
    return copy().toStringConstraints();
  }

  @Override
  public String toStringFull() {
    return copy().toStringFull();
  }

  @Override
  public String checkInvariants() {
    if (size == 0) {
      return null;
    }
    if (min > max) {
      return "Min value is larger than max value " + min + " " + max;
    }
    if (!present(min) || !present(max)) {
      return "Bounds are not in the domain " + min + " " + max;
    }
    if (size != count(min, max)) {
      return "Size " + size + " does not match the values " + count(min, max);
    }
    return null;
  }

  @Override
  public int sizeConstraintsOriginal() {
    return copy().sizeConstraintsOriginal();
  }
}
