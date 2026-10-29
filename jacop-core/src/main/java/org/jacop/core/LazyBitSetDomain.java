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
 * after the domain variables of OR-Tools' constraint solver. A domain of {@link #MAX_SPAN} values
 * or more keeps its holes as a sorted list of intervals instead of bits.
 *
 * <p>Unlike the other domains, which install a new domain object the first time a variable changes
 * at a search level, this domain is changed in place and saves its old state on the store's {@link
 * DomainTrail}. The first change at a level saves the bounds, the size and the stamp; the
 * constraint lists and a word of the bit set are saved the first time they change at a level.
 * Bounds are kept in fields and never touch the bit set, so bits outside the bounds may be stale
 * and every query is limited to the bounds. Backtracking pops the trail entries of the removed
 * levels, those of all domains of the store.
 *
 * <p>A value enumeration works on a snapshot taken when it is created, as an enumeration of a
 * copied domain would: the bit set is copied on the next change instead of when the enumeration is
 * created.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class LazyBitSetDomain extends IntDomain implements DomainTrail.Entry {

  /** The number of values (max - min + 1) from which the holes are kept as intervals. */
  public static final int MAX_SPAN = 1 << 16;

  private static final int LEVEL_ENTRY = -1;

  private static final int CONSTRAINTS_ENTRY = -2;

  private int minBound;

  private int maxBound;

  private int size;

  /** Bits of values base, base + 1, ...; null while the domain is an interval. */
  private long[] bits;

  private int base;

  /** The level at which each word was last saved. */
  private int[] wordStamp;

  /**
   * Whether the holes are kept in ranges instead of bits, for domains of MAX_SPAN values or more.
   */
  final boolean rangeHoles;

  /**
   * The intervals as pairs lo, hi in increasing order, separated by at least one value, when the
   * holes are kept as intervals; null while the domain is an interval. The values are those of the
   * intervals within the bounds. Never changed once built, so the trail keeps it by reference.
   */
  private int[] ranges;

  /** Set when an enumeration may hold the bits array, which then must be copied before a change. */
  private boolean bitsShared;

  /** It is increased whenever the holes change, to know when cachedIntervals is current. */
  private int bitsVersion;

  /** The intervals of the domain when it was last asked for, or null. */
  private IntervalDomain cachedIntervals;

  private int cachedMin;

  private int cachedMax;

  private int cachedVersion;

  /** The level at which the constraint lists were last saved, at most stamp. */
  private int constraintsStamp;

  /** The entry of the store's domain trail made at the level of stamp, or -1. */
  private int levelEntry = -1;

  /** The domain trail of the store of the variable, known from the first change during search. */
  private DomainTrail trail;

  /**
   * It creates a domain with values between min and max inclusive.
   *
   * @param min the minimum value of the domain.
   * @param max the maximum value of the domain.
   */
  public LazyBitSetDomain(int min, int max) {
    this(min, max, (long) max - min + 1 >= MAX_SPAN);
  }

  /**
   * It creates a domain with values between min and max inclusive.
   *
   * @param min the minimum value of the domain.
   * @param max the maximum value of the domain.
   * @param rangeHoles whether holes are kept as intervals instead of bits.
   */
  LazyBitSetDomain(int min, int max, boolean rangeHoles) {
    this.rangeHoles = rangeHoles;
    if (min > max) {
      throw new IllegalArgumentException("Empty domain " + min + ".." + max);
    }
    this.minBound = min;
    this.maxBound = max;
    this.size = max - min + 1;
    this.searchConstraints = new ArrayList<>();
    this.onDomainTrail = true;
  }

  // ---------- bit set helpers ----------

  private boolean present(int value) {
    if (bits == null) {
      if (ranges == null) {
        return true;
      }
      int i = find(ranges, value);
      return i < ranges.length >>> 1 && ranges[2 * i] <= value;
    }
    int index = value - base;
    return (bits[index >>> 6] & (1L << index)) != 0;
  }

  /** The smallest value of the domain that is at least value, or max + 1. */
  private int nextPresent(int value) {
    if (value > maxBound) {
      return maxBound + 1;
    }
    if (value < minBound) {
      value = minBound;
    }
    if (bits == null) {
      if (ranges == null) {
        return value;
      }
      int i = find(ranges, value);
      if (i == ranges.length >>> 1) {
        return maxBound + 1;
      }
      int result = Math.max(value, ranges[2 * i]);
      return result > maxBound ? maxBound + 1 : result;
    }
    int index = value - base;
    int word = index >>> 6;
    int lastWord = (maxBound - base) >>> 6;
    long w = bits[word] & (-1L << index);
    while (w == 0) {
      if (++word > lastWord) {
        return maxBound + 1;
      }
      w = bits[word];
    }
    int result = base + (word << 6) + Long.numberOfTrailingZeros(w);
    return result > maxBound ? maxBound + 1 : result;
  }

  /** The largest value of the domain that is at most value, or min - 1. */
  private int previousPresent(int value) {
    if (value < minBound) {
      return minBound - 1;
    }
    if (value > maxBound) {
      value = maxBound;
    }
    if (bits == null) {
      if (ranges == null) {
        return value;
      }
      int i = find(ranges, value);
      if (i < ranges.length >>> 1 && ranges[2 * i] <= value) {
        return value;
      }
      if (i == 0) {
        return minBound - 1;
      }
      int result = ranges[2 * i - 1];
      return result < minBound ? minBound - 1 : result;
    }
    int index = value - base;
    int word = index >>> 6;
    int firstWord = (minBound - base) >>> 6;
    long w = bits[word] & (-1L >>> (63 - (index & 63)));
    while (w == 0) {
      if (--word < firstWord) {
        return minBound - 1;
      }
      w = bits[word];
    }
    int result = base + (word << 6) + 63 - Long.numberOfLeadingZeros(w);
    return result < minBound ? minBound - 1 : result;
  }

  /** The number of values of the domain in lo..hi, which must be within the bounds. */
  private int count(int lo, int hi) {
    if (lo > hi) {
      return 0;
    }
    if (bits == null) {
      if (ranges == null) {
        return hi - lo + 1;
      }
      int result = 0;
      int n = ranges.length >>> 1;
      for (int i = find(ranges, lo); i < n && ranges[2 * i] <= hi; i++) {
        result += Math.min(hi, ranges[2 * i + 1]) - Math.max(lo, ranges[2 * i]) + 1;
      }
      return result;
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

  /** The index of the first interval of ranges whose end is at least value, or the count. */
  private static int find(int[] ranges, int value) {
    int lo = 0;
    int hi = ranges.length >>> 1;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (ranges[2 * mid + 1] < value) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return lo;
  }

  /**
   * Removes the values lo..hi, strictly inside the bounds, from the intervals and returns how many
   * values were removed. The level must have been saved already.
   */
  private int clearRanges(int lo, int hi) {
    int removed = count(lo, hi);
    if (removed == 0) {
      return 0;
    }
    if (ranges == null) {
      ranges = new int[] {minBound, lo - 1, hi + 1, maxBound};
    } else {
      // the intervals within the bounds without lo..hi
      int n = ranges.length >>> 1;
      int[] result = new int[ranges.length + 2];
      int out = 0;
      for (int i = find(ranges, minBound); i < n && ranges[2 * i] <= maxBound; i++) {
        int a = Math.max(minBound, ranges[2 * i]);
        int b = Math.min(maxBound, ranges[2 * i + 1]);
        if (a < lo) {
          result[out++] = a;
          result[out++] = Math.min(b, lo - 1);
        }
        if (b > hi) {
          result[out++] = Math.max(a, hi + 1);
          result[out++] = b;
        }
      }
      setRanges(result, out >>> 1);
    }
    size -= removed;
    return removed;
  }

  /** It installs intervals given as pairs, the first count of them, as the holes of the domain. */
  private void setRanges(int[] pairs, int count) {
    bitsVersion++;
    if (count <= 1) {
      ranges = null;
    } else {
      ranges = pairs.length == 2 * count ? pairs : java.util.Arrays.copyOf(pairs, 2 * count);
    }
  }

  private void createBits(int storeLevel) {
    base = minBound;
    int words = ((maxBound - minBound) >>> 6) + 1;
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
    if (rangeHoles) {
      return clearRanges(lo, hi);
    }
    bitsVersion++;
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

  private void pushWord(int word, int storeLevel, long old) {
    int entry = trail.push(this, word, storeLevel);
    trail.ints[entry * DomainTrail.INTS + 2] = wordStamp[word];
    trail.longs[entry] = old;
    wordStamp[word] = storeLevel;
  }

  /**
   * Saves the state before the first change at storeLevel on the store's domain trail, as the other
   * domains do by creating a new domain object. The constraint lists, which rarely change during
   * search, are saved apart by {@link #saveConstraints(int, Var)}.
   */
  private void saveLevel(int storeLevel, Var v) {
    if (stamp >= storeLevel) {
      return;
    }
    if (trail == null) {
      trail = v.getStore().domainTrail;
    }
    int entry = trail.push(this, LEVEL_ENTRY, storeLevel);
    int i = entry * DomainTrail.INTS;
    int[] ints = trail.ints;
    ints[i + 2] = minBound;
    ints[i + 3] = maxBound;
    ints[i + 4] = size;
    ints[i + 5] = stamp;
    ints[i + 6] = levelEntry;
    trail.longs[entry] = bits == null ? 1L : 0L;
    trail.objects[entry * DomainTrail.OBJECTS + 1] = ranges;
    // the variable is not visited on backtracking, so undo restores the bounds it keeps
    trail.objects[entry * DomainTrail.OBJECTS + 2] = v;
    levelEntry = entry;
    stamp = storeLevel;
  }

  /** Saves the constraint lists before their first change at storeLevel. */
  private void saveConstraints(int storeLevel, Var v) {
    saveLevel(storeLevel, v);
    if (constraintsStamp >= storeLevel) {
      return;
    }
    int entry = trail.push(this, CONSTRAINTS_ENTRY, storeLevel);
    trail.ints[entry * DomainTrail.INTS + 2] = constraintsStamp;
    trail.longs[entry] =
        ((long) searchConstraintsToEvaluate << 1) | (searchConstraintsCloned ? 1L : 0L);
    int o = entry * DomainTrail.OBJECTS;
    trail.objects[o + 1] = modelConstraints;
    trail.objects[o + 2] = modelConstraintsToEvaluate;
    trail.objects[o + 3] = searchConstraints;
    constraintsStamp = storeLevel;
    // the saved state shares the constraint arrays, so they are copied before they grow
    ownedModelConstraints = null;
    ownedModelConstraintTables = null;
    ownedModelConstraintTableSizes = null;
    // a domain object created for a new level does not own the search constraint list
    searchConstraintsCloned = false;
  }

  @Override
  @SuppressWarnings("unchecked")
  public void undo(DomainTrail from, int entry) {
    bitsVersion++;
    int i = entry * DomainTrail.INTS;
    int[] ints = from.ints;
    int kind = ints[i];
    if (kind == LEVEL_ENTRY) {
      minBound = ints[i + 2];
      maxBound = ints[i + 3];
      size = ints[i + 4];
      stamp = ints[i + 5];
      levelEntry = ints[i + 6];
      ranges = (int[]) from.objects[entry * DomainTrail.OBJECTS + 1];
      if (from.longs[entry] != 0) {
        bits = null;
        wordStamp = null;
      }
      ((IntVar) from.objects[entry * DomainTrail.OBJECTS + 2]).setBounds(minBound, maxBound);
    } else if (kind == CONSTRAINTS_ENTRY) {
      constraintsStamp = ints[i + 2];
      long flags = from.longs[entry];
      searchConstraintsCloned = (flags & 1L) != 0;
      searchConstraintsToEvaluate = (int) (flags >>> 1);
      int o = entry * DomainTrail.OBJECTS;
      modelConstraints = (Constraint[][]) from.objects[o + 1];
      modelConstraintsToEvaluate = (int[]) from.objects[o + 2];
      searchConstraints = (List<Constraint>) from.objects[o + 3];
    } else {
      if (bitsShared) {
        bits = bits.clone();
        bitsShared = false;
      }
      bits[kind] = from.longs[entry];
      wordStamp[kind] = ints[i + 2];
    }
  }

  @Override
  public void removeLevel(int level, Var v) {
    // the store pops its domain trail before it visits the changed variables, so the domain is
    // already restored then; a level removed without the store pops the trail here
    if (stamp >= level) {
      trail.removeLevel(level);
    }
  }

  // ---------- events ----------

  private void changed(Var v, int oldMin, int oldMax) {
    if (minBound == maxBound) {
      v.domainHasChanged(GROUND);
    } else if (minBound != oldMin || maxBound != oldMax) {
      v.domainHasChanged(boundEvent(minBound != oldMin, maxBound != oldMax));
    } else {
      v.domainHasChanged(ANY);
    }
  }

  // ---------- pruning ----------

  @Override
  public void inMin(int storeLevel, Var v, int newMin) {
    if (newMin > maxBound) {
      throw failException;
    }
    if (newMin <= minBound) {
      return;
    }
    int value = nextPresent(newMin);
    saveLevel(storeLevel, v);
    size -= count(minBound, value - 1);
    minBound = value;
    v.domainHasChanged(minBound == maxBound ? GROUND : MIN_EVENT);
  }

  @Override
  public void inMax(int storeLevel, Var v, int newMax) {
    if (newMax < minBound) {
      throw failException;
    }
    if (newMax >= maxBound) {
      return;
    }
    int value = previousPresent(newMax);
    saveLevel(storeLevel, v);
    size -= count(value + 1, maxBound);
    maxBound = value;
    v.domainHasChanged(minBound == maxBound ? GROUND : MAX_EVENT);
  }

  @Override
  public void in(int storeLevel, Var v, int newMin, int newMax) {
    if (newMax < minBound || newMin > maxBound) {
      throw failException;
    }
    if (newMin <= minBound && newMax >= maxBound) {
      return;
    }
    int lo = nextPresent(newMin);
    if (lo > newMax) {
      throw failException;
    }
    int hi = previousPresent(newMax);
    saveLevel(storeLevel, v);
    size -= count(minBound, lo - 1) + count(hi + 1, maxBound);
    boolean minChanged = lo != minBound;
    boolean maxChanged = hi != maxBound;
    minBound = lo;
    maxBound = hi;
    v.domainHasChanged(lo == hi ? GROUND : boundEvent(minChanged, maxChanged));
  }

  @Override
  public void inValue(int storeLevel, IntVar v, int value) {
    if (minBound == value && maxBound == value) {
      return;
    }
    if (!contains(value)) {
      throw failException;
    }
    saveLevel(storeLevel, v);
    minBound = value;
    maxBound = value;
    size = 1;
    v.domainHasChanged(GROUND);
  }

  @Override
  public void inComplement(int storeLevel, Var v, int complement) {
    if (complement < minBound || complement > maxBound || !present(complement)) {
      return;
    }
    if (minBound == maxBound) {
      throw failException;
    }
    ((IntVar) v).removingValue(complement);
    int oldMin = minBound;
    int oldMax = maxBound;
    saveLevel(storeLevel, v);
    if (complement == minBound) {
      int value = nextPresent(complement + 1);
      size--;
      minBound = value;
    } else if (complement == maxBound) {
      int value = previousPresent(complement - 1);
      size--;
      maxBound = value;
    } else {
      clear(storeLevel, complement, complement);
    }
    changed(v, oldMin, oldMax);
  }

  @Override
  public void inComplement(int storeLevel, Var v, int lo, int hi) {
    int oldMin = minBound;
    int oldMax = maxBound;
    int oldSize = size;
    removeRange(storeLevel, v, lo, hi);
    if (size != oldSize) {
      changed(v, oldMin, oldMax);
    }
  }

  @Override
  public void inComplement(int storeLevel, Var v, IntDomain complement) {
    int oldMin = minBound;
    int oldMax = maxBound;
    int oldSize = size;
    int intervals = complement.noIntervals();
    for (int k = 0; k < intervals; k++) {
      removeRange(storeLevel, v, complement.leftElement(k), complement.rightElement(k));
    }
    if (size != oldSize) {
      changed(v, oldMin, oldMax);
    }
  }

  /** It removes the values lo..hi without informing the variable. */
  private void removeRange(int storeLevel, Var v, int lo, int hi) {
    if (lo > hi || hi < minBound || lo > maxBound) {
      return;
    }
    if (lo <= minBound && hi >= maxBound) {
      throw failException;
    }
    if (lo <= minBound) {
      int value = nextPresent(hi + 1);
      saveLevel(storeLevel, v);
      size -= count(minBound, value - 1);
      minBound = value;
    } else if (hi >= maxBound) {
      int value = previousPresent(lo - 1);
      saveLevel(storeLevel, v);
      size -= count(value + 1, maxBound);
      maxBound = value;
    } else {
      if (count(lo, hi) == 0) {
        return;
      }
      saveLevel(storeLevel, v);
      clear(storeLevel, lo, hi);
    }
  }

  @Override
  public void in(int storeLevel, Var v, IntDomain domain) {
    if (domain.isEmpty()) {
      throw failException;
    }
    if (domain.domainId() == BOUND_DOMAIN_ID) {
      in(storeLevel, v, domain.min(), domain.max());
      return;
    }
    if (domain.domainId() != INTERVAL_DOMAIN_ID) {
      // bit sets, this one or a small dense domain: 64 values at a time
      keepOnly(storeLevel, v, domain, 0);
      return;
    }
    inIntervals(storeLevel, v, domain, 0);
  }

  /** It keeps the values x of this domain for which x - shift is in an interval domain. */
  private void inIntervals(int storeLevel, Var v, IntDomain domain, int shift) {
    if (domain.noIntervals() == 1) {
      in(storeLevel, v, domain.min() + shift, domain.max() + shift);
      return;
    }
    // the new bounds: the first and the last value of this domain within domain
    int lo = firstValueIn(domain, shift);
    if (lo > maxBound) {
      throw failException;
    }
    int hi = lastValueIn(domain, shift);
    int oldMin = minBound;
    int oldMax = maxBound;
    int oldSize = size;
    // the bounds first, so that a bit set created below covers only the new bounds
    if (lo != minBound || hi != maxBound) {
      saveLevel(storeLevel, v);
      size -= count(minBound, lo - 1) + count(hi + 1, maxBound);
      minBound = lo;
      maxBound = hi;
    }
    clearGaps(storeLevel, v, domain, shift);
    if (size != oldSize) {
      changed(v, oldMin, oldMax);
    }
  }

  /** The first value x of this domain for which x - shift is in an interval domain, or max + 1. */
  private int firstValueIn(IntDomain domain, int shift) {
    int intervals = domain.noIntervals();
    for (int i = 0; i < intervals; i++) {
      Interval interval = domain.getInterval(i);
      if (interval.max() + shift >= minBound) {
        int candidate = nextPresent(interval.min() + shift);
        if (candidate <= interval.max() + shift) {
          return candidate;
        }
      }
    }
    return maxBound + 1;
  }

  /** The last value x of this domain for which x - shift is in an interval domain, or min - 1. */
  private int lastValueIn(IntDomain domain, int shift) {
    for (int i = domain.noIntervals() - 1; i >= 0; i--) {
      Interval interval = domain.getInterval(i);
      if (interval.min() + shift <= maxBound) {
        int candidate = previousPresent(interval.max() + shift);
        if (candidate >= interval.min() + shift) {
          return candidate;
        }
      }
    }
    return minBound - 1;
  }

  /** It removes the values within the bounds that fall, shifted, between intervals of domain. */
  private void clearGaps(int storeLevel, Var v, IntDomain domain, int shift) {
    int intervals = domain.noIntervals();
    for (int i = 0; i < intervals - 1; i++) {
      int gapLo = Math.max(domain.getInterval(i).max() + shift + 1, minBound + 1);
      int gapHi = Math.min(domain.getInterval(i + 1).min() + shift - 1, maxBound - 1);
      if (gapLo <= gapHi && nextPresent(gapLo) <= gapHi) {
        saveLevel(storeLevel, v);
        clear(storeLevel, gapLo, gapHi);
      }
    }
  }

  @Override
  public void inShift(int storeLevel, Var v, IntDomain domain, int shift) {
    if (domain.isEmpty()) {
      throw failException;
    }
    if (domain.domainId() == BOUND_DOMAIN_ID) {
      in(storeLevel, v, domain.min() + shift, domain.max() + shift);
      return;
    }
    if (domain.domainId() != INTERVAL_DOMAIN_ID) {
      keepOnly(storeLevel, v, domain, shift);
      return;
    }
    inIntervals(storeLevel, v, domain, shift);
  }

  /**
   * It returns the values lo..lo + 63 of this domain as bits: bit k is set when lo + k is in the
   * domain.
   */
  @Override
  public long bitsFrom(int lo) {
    if (size == 0 || lo > maxBound || lo + 63 < minBound) {
      return 0;
    }
    long mask = -1L;
    if (minBound > lo) {
      mask &= -1L << (minBound - lo);
    }
    if (maxBound < lo + 63) {
      mask &= -1L >>> (63 - (maxBound - lo));
    }
    if (bits == null) {
      return ranges == null ? mask : super.bitsFrom(lo);
    }
    return extract(bits, base, lo) & mask;
  }

  /**
   * The values lo..lo + 63 of domain as bits. Most domains met here are bit sets too, and calling
   * bitsFrom on them directly lets it be inlined.
   */
  private static long bitsOf(IntDomain domain, int lo) {
    if (domain instanceof LazyBitSetDomain bitSet) {
      return bitSet.bitsFrom(lo);
    }
    return domain.bitsFrom(lo);
  }

  /** The bits of words for the values lo..lo + 63, where value v has bit v - base. */
  private static long extract(long[] words, int base, int lo) {
    int index = lo - base;
    if (index < -63) {
      return 0;
    }
    if (index < 0) {
      return words[0] << -index;
    }
    int word = index >>> 6;
    if (word >= words.length) {
      return 0;
    }
    int offset = index & 63;
    long w = words[word] >>> offset;
    if (offset != 0 && word + 1 < words.length) {
      w |= words[word + 1] << (64 - offset);
    }
    return w;
  }

  /** It adds the runs of set bits of word, where bit k is the value start + k, to result. */
  private static void appendRuns(IntervalDomain result, int start, long word) {
    while (word != 0) {
      int from = Long.numberOfTrailingZeros(word);
      int length = Long.numberOfTrailingZeros(~(word >>> from));
      result.unionAdapt(start + from, start + from + length - 1);
      word &= ~bitRange(from, from + length - 1);
    }
  }

  /** It keeps only the values x of this domain for which x - shift is in other. */
  private void keepOnly(int storeLevel, Var v, IntDomain other, int shift) {
    // two domains without holes meet in an interval (an element or an equality whose variables
    // only lost bounds), which needs no walk over their words
    if (size == maxBound - minBound + 1
        && !other.isEmpty()
        && other.getSize() == (long) other.max() - other.min() + 1) {
      in(storeLevel, v, other.min() + shift, other.max() + shift);
      return;
    }
    int lo = Math.max(minBound, other.min() + shift);
    int hi = Math.min(maxBound, other.max() + shift);
    if (lo > hi) {
      throw failException;
    }
    if (rangeHoles) {
      keepOnlyRuns(storeLevel, v, other, shift, lo, hi);
      return;
    }
    // the new bounds: the first and the last common value
    int newMin = firstCommon(other, shift, lo, hi);
    if (newMin > hi) {
      throw failException;
    }
    int newMax = lastCommon(other, shift, newMin, hi);
    int oldMin = minBound;
    int oldMax = maxBound;
    int oldSize = size;
    // the bounds first, so that a bit set created below covers only the new bounds
    if (newMin != minBound || newMax != maxBound) {
      saveLevel(storeLevel, v);
      size -= count(minBound, newMin - 1) + count(newMax + 1, maxBound);
      minBound = newMin;
      maxBound = newMax;
    }
    // values strictly between the new bounds that other does not have; there are none when other
    // has no hole, which its size tells without walking the words of the bounds
    if (newMax - newMin > 1
        && other.getSize() != (long) other.max() - other.min() + 1
        && (bits != null || hasHole(other, newMin + 1 - shift, newMax - 1 - shift))) {
      removeMissing(storeLevel, v, other, shift);
    }
    if (size != oldSize) {
      changed(v, oldMin, oldMax);
    }
  }

  /**
   * It keeps only the values x of this domain for which x - shift is in other, walking the runs of
   * both domains within lo..hi, for holes kept as intervals.
   */
  private void keepOnlyRuns(int storeLevel, Var v, IntDomain other, int shift, int lo, int hi) {
    int[] result = new int[8];
    int out = 0;
    int resultSize = 0;
    int x = nextPresent(lo);
    int y = other.contains(x - shift) ? x - shift : other.nextValue(x - shift);
    if (x > hi || !other.contains(y)) {
      throw failException;
    }
    int otherMax = other.max();
    int xEnd = Math.min(hi, endOfRun(x));
    int yEnd = other.runEnd(y);
    while (true) {
      int a = Math.max(x, y + shift);
      int b = Math.min(xEnd, yEnd + shift);
      if (a <= b) {
        if (out == result.length) {
          result = java.util.Arrays.copyOf(result, out * 2);
        }
        result[out++] = a;
        result[out++] = b;
        resultSize += b - a + 1;
      }
      if (xEnd <= yEnd + shift) {
        if (xEnd >= hi) {
          break;
        }
        x = nextPresent(xEnd + 1);
        if (x > hi) {
          break;
        }
        xEnd = Math.min(hi, endOfRun(x));
      } else {
        if (yEnd >= otherMax) {
          break;
        }
        y = other.nextValue(yEnd);
        yEnd = other.runEnd(y);
      }
    }
    if (out == 0) {
      throw failException;
    }
    if (resultSize == size) {
      return;
    }
    int oldMin = minBound;
    int oldMax = maxBound;
    saveLevel(storeLevel, v);
    minBound = result[0];
    maxBound = result[out - 1];
    size = resultSize;
    setRanges(result, out >>> 1);
    changed(v, oldMin, oldMax);
  }

  /** The first value x in lo..hi of this domain for which x - shift is in other, or hi + 1. */
  private int firstCommon(IntDomain other, int shift, int lo, int hi) {
    for (int start = lo; start <= hi; start += 64) {
      long common = bitsFrom(start) & bitsOf(other, start - shift);
      if (hi - start < 63) {
        common &= -1L >>> (63 - (hi - start));
      }
      if (common != 0) {
        return start + Long.numberOfTrailingZeros(common);
      }
    }
    return hi + 1;
  }

  /** The last value x in lo..hi of this domain for which x - shift is in other, or lo. */
  private int lastCommon(IntDomain other, int shift, int lo, int hi) {
    for (int end = hi; end > lo; end -= 64) {
      int start = Math.max(end - 63, lo);
      long common = bitsFrom(start) & bitsOf(other, start - shift);
      common &= -1L >>> (63 - (end - start));
      if (common != 0) {
        return start + 63 - Long.numberOfLeadingZeros(common);
      }
    }
    return lo;
  }

  /** It removes the values strictly inside the bounds for which value - shift is not in other. */
  private void removeMissing(int storeLevel, Var v, IntDomain other, int shift) {
    bitsVersion++;
    if (bits == null) {
      // no holes yet, so the hole of other removes values
      saveLevel(storeLevel, v);
      createBits(storeLevel);
    } else if (bitsShared) {
      bits = bits.clone();
      bitsShared = false;
    }
    int from = minBound + 1 - base;
    int to = maxBound - 1 - base;
    int removed = 0;
    for (int i = from >>> 6; i <= to >>> 6; i++) {
      long mask = ~bitsOf(other, base + (i << 6) - shift);
      if (i == from >>> 6) {
        mask &= -1L << from;
      }
      if (i == to >>> 6) {
        mask &= -1L >>> (63 - (to & 63));
      }
      long old = bits[i];
      long cleared = old & mask;
      if (cleared != 0) {
        saveLevel(storeLevel, v);
        if (wordStamp[i] < storeLevel) {
          pushWord(i, storeLevel, old);
        }
        bits[i] = old & ~mask;
        removed += Long.bitCount(cleared);
      }
    }
    size -= removed;
  }

  /** It tells if some value of lo..hi is not in the domain. */
  private static boolean hasHole(IntDomain domain, int lo, int hi) {
    for (int start = lo; start <= hi; start += 64) {
      long all = -1L >>> (63 - Math.min(63, hi - start));
      if ((bitsOf(domain, start) & all) != all) {
        return true;
      }
    }
    return false;
  }

  /** It tells if the values of the domain are best read interval by interval. */
  private static boolean byIntervals(IntDomain domain) {
    return domain.domainId() == INTERVAL_DOMAIN_ID
        || domain.domainId() == BOUND_DOMAIN_ID
        || domain instanceof LazyBitSetDomain lazy && lazy.rangeHoles;
  }

  // ---------- constraints ----------

  @Override
  public void putModelConstraint(int storeLevel, Var v, Constraint c, int pruningEvent) {
    saveConstraints(storeLevel, v);
    super.putModelConstraint(storeLevel, v, c, pruningEvent);
  }

  @Override
  public void removeModelConstraint(int storeLevel, Var v, Constraint c) {
    saveConstraints(storeLevel, v);
    super.removeModelConstraint(storeLevel, v, c);
  }

  @Override
  public void putSearchConstraint(int storeLevel, Var v, Constraint c) {
    if (!searchConstraints.contains(c)) {
      boolean newLevel = stamp < storeLevel;
      saveConstraints(storeLevel, v);
      if (newLevel) {
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
    saveConstraints(storeLevel, v);
    super.removeSearchConstraint(storeLevel, v, c);
  }

  @Override
  public void removeSearchConstraint(int storeLevel, Var v, int position, Constraint c) {
    saveConstraints(storeLevel, v);
    super.removeSearchConstraint(storeLevel, v, position, c);
  }

  // ---------- queries ----------

  @Override
  public int min() {
    return minBound;
  }

  @Override
  public int max() {
    return maxBound;
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
    return minBound == maxBound && size == 1;
  }

  @Override
  public boolean singleton(int c) {
    return minBound == c && maxBound == c && size == 1;
  }

  @Override
  public int value() {
    return minBound;
  }

  @Override
  public boolean contains(int value) {
    return value >= minBound && value <= maxBound && present(value);
  }

  @Override
  public boolean contains(int lo, int hi) {
    if (lo > hi) {
      return true;
    }
    if (lo < minBound || hi > maxBound) {
      return false;
    }
    return count(lo, hi) == hi - lo + 1;
  }

  @Override
  public boolean isIntersecting(int lo, int hi) {
    if (lo > hi || hi < minBound || lo > maxBound) {
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
    return next > maxBound ? value : next;
  }

  @Override
  public int previousValue(int value) {
    if (value == Integer.MIN_VALUE) {
      return value;
    }
    int previous = previousPresent(value - 1);
    return previous < minBound ? value : previous;
  }

  @Override
  public int noIntervals() {
    if (size == 0) {
      return 0;
    }
    if (bits == null && ranges == null || size == maxBound - minBound + 1) {
      return 1;
    }
    return intervals().size;
  }

  /**
   * The values of the domain as an interval domain, computed once until the domain changes. It must
   * not be modified.
   */
  private IntervalDomain intervals() {
    if (cachedIntervals == null
        || cachedVersion != bitsVersion
        || cachedMin != minBound
        || cachedMax != maxBound) {
      cachedIntervals = toIntervalDomain();
      cachedVersion = bitsVersion;
      cachedMin = minBound;
      cachedMax = maxBound;
    }
    return cachedIntervals;
  }

  /** The last value of the run of consecutive values starting at value, which is present. */
  @Override
  public int runEnd(int value) {
    return endOfRun(value);
  }

  private int endOfRun(int value) {
    if (bits == null) {
      return ranges == null ? maxBound : Math.min(maxBound, ranges[2 * find(ranges, value) + 1]);
    }
    int index = value - base;
    int word = index >>> 6;
    int lastWord = (maxBound - base) >>> 6;
    long w = ~bits[word] & (-1L << index);
    while (w == 0) {
      if (++word > lastWord) {
        return maxBound;
      }
      w = ~bits[word];
    }
    int result = base + (word << 6) + Long.numberOfTrailingZeros(w) - 1;
    return Math.min(result, maxBound);
  }

  @Override
  public Interval getInterval(int position) {
    if ((bits != null || ranges != null) && size != maxBound - minBound + 1) {
      return intervals().intervals[position];
    }
    int value = minBound;
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
    if (bits == null && ranges == null) {
      return minBound + index;
    }
    int value = minBound;
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
      return ranges == null
          ? new IntervalDomain(minBound, maxBound)
          : rangesDomain(ranges, minBound, maxBound);
    }
    return runs(bits, base, minBound, maxBound);
  }

  /** The values of the intervals within lo..hi as an interval domain. */
  private static IntervalDomain rangesDomain(int[] ranges, int lo, int hi) {
    int n = ranges.length >>> 1;
    IntervalDomain result = new IntervalDomain(n);
    for (int i = find(ranges, lo); i < n && ranges[2 * i] <= hi; i++) {
      result.unionAdapt(Math.max(lo, ranges[2 * i]), Math.min(hi, ranges[2 * i + 1]));
    }
    return result;
  }

  @Override
  public ValueEnumeration valueEnumeration() {
    if (ranges != null) {
      return toIntervalDomain().valueEnumeration();
    }
    if (bits != null) {
      bitsShared = true;
    }
    return new LazyBitSetDomainValueEnumeration(minBound, maxBound, bits, base);
  }

  @Override
  public IntervalEnumeration intervalEnumeration() {
    return intervals().intervalEnumeration();
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
    return intervals().getRandomValue();
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
    int entry = levelEntry;
    if (entry < 0) {
      return null;
    }
    int i = entry * DomainTrail.INTS;
    int oldMin = trail.ints[i + 2];
    int oldMax = trail.ints[i + 3];
    int[] oldRanges = (int[]) trail.objects[entry * DomainTrail.OBJECTS + 1];
    if (oldRanges != null) {
      return rangesDomain(oldRanges, oldMin, oldMax);
    }
    if ((trail.longs[entry] & 1L) != 0) {
      return new IntervalDomain(oldMin, oldMax);
    }
    return runs(previousWords(entry), base, oldMin, oldMax);
  }

  /**
   * It returns the values lo..hi whose bits are set in words, where value v has bit v - base, as an
   * interval domain.
   */
  private static IntervalDomain runs(long[] words, int base, int lo, int hi) {
    IntervalDomain result = new IntervalDomain(8);
    int value = lo;
    while (value <= hi) {
      int index = value - base;
      int word = index >>> 6;
      long w = words[word] & (-1L << index);
      while (w == 0) {
        if (++word >= words.length) {
          return result;
        }
        w = words[word];
      }
      int start = base + (word << 6) + Long.numberOfTrailingZeros(w);
      if (start > hi) {
        break;
      }
      index = start - base;
      word = index >>> 6;
      w = ~words[word] & (-1L << index);
      while (w == 0 && word + 1 < words.length) {
        w = ~words[++word];
      }
      int end = w == 0 ? hi : Math.min(hi, base + (word << 6) + Long.numberOfTrailingZeros(w) - 1);
      result.unionAdapt(start, end);
      value = end + 2;
    }
    return result;
  }

  @Override
  public IntDomain recentDomainPruning(int storeLevel) {
    if (stamp < storeLevel) {
      return IntervalDomain.emptyDomain;
    }
    int entry = levelEntry;
    if (entry < 0) {
      return IntervalDomain.emptyDomain;
    }
    if (rangeHoles) {
      IntervalDomain removed = subtractRuns(getPreviousDomain(), this);
      return removed.isEmpty() ? IntervalDomain.emptyDomain : removed;
    }
    int i = entry * DomainTrail.INTS;
    int oldMin = trail.ints[i + 2];
    int oldMax = trail.ints[i + 3];
    // the words before this level, or null when the domain had no holes then
    long[] old = (trail.longs[entry] & 1L) != 0 ? null : previousWords(entry);
    IntervalDomain result = new IntervalDomain(4);
    for (int start = oldMin; start <= oldMax; start += 64) {
      long range = bitRange(0, Math.min(63, oldMax - start));
      long previous = old == null ? range : extract(old, base, start) & range;
      appendRuns(result, start, previous & ~bitsFrom(start));
    }
    return result.isEmpty() ? IntervalDomain.emptyDomain : result;
  }

  /** The bit set as it was before the level of the given level entry. */
  private long[] previousWords(int entry) {
    long[] old = bits.clone();
    // the entries after it of this domain, among those of the other domains of the store
    for (int e = trail.size() - 1; e > entry; e--) {
      int word = trail.ints[e * DomainTrail.INTS];
      if (word >= 0 && trail.objects[e * DomainTrail.OBJECTS] == this) {
        old[word] = trail.longs[e];
      }
    }
    return old;
  }

  // ---------- operations creating new domains ----------

  @Override
  public IntDomain complement() {
    return intervals().complement();
  }

  @Override
  public IntDomain intersect(IntDomain dom) {
    return intersectRuns(this, dom, 0);
  }

  @Override
  public IntDomain intersect(int lo, int hi) {
    return size == 0 ? new IntervalDomain() : intervals().intersect(lo, hi);
  }

  @Override
  public IntDomain subtract(int lo, int hi) {
    return intervals().subtract(lo, hi);
  }

  @Override
  public IntDomain subtract(int value) {
    return intervals().subtract(value);
  }

  @Override
  public IntDomain subtract(IntDomain domain) {
    return subtractRuns(this, domain);
  }

  @Override
  public IntDomain union(IntDomain domain) {
    return unionRuns(this, domain);
  }

  @Override
  public IntDomain union(int lo, int hi) {
    return intervals().union(lo, hi);
  }

  @Override
  public IntDomain union(int value) {
    return intervals().union(value);
  }

  @Override
  public boolean contains(IntDomain domain) {
    if (domain.isEmpty()) {
      return true;
    }
    if (domain.min() < minBound || domain.max() > maxBound) {
      return false;
    }
    if (!byIntervals(domain)) {
      int hi = domain.max();
      for (int start = domain.min(); start <= hi; start += 64) {
        if ((bitsOf(domain, start) & ~bitsFrom(start)) != 0) {
          return false;
        }
      }
      return true;
    }
    IntDomain intervals = domain;
    for (int i = intervals.noIntervals() - 1; i >= 0; i--) {
      Interval interval = intervals.getInterval(i);
      if (count(interval.min(), interval.max()) != interval.max() - interval.min() + 1) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean isIntersecting(IntDomain domain) {
    if (size == 0 || domain.isEmpty() || domain.max() < minBound || domain.min() > maxBound) {
      return false;
    }
    if (!byIntervals(domain)) {
      int hi = Math.min(maxBound, domain.max());
      for (int start = Math.max(minBound, domain.min()); start <= hi; start += 64) {
        if ((bitsFrom(start) & bitsOf(domain, start)) != 0) {
          return true;
        }
      }
      return false;
    }
    IntDomain intervals = domain;
    for (int i = 0, n = intervals.noIntervals(); i < n; i++) {
      Interval interval = intervals.getInterval(i);
      if (interval.min() > maxBound) {
        return false;
      }
      if (isIntersecting(interval.min(), interval.max())) {
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean eq(IntDomain domain) {
    return getSize() == domain.getSize() && contains(domain);
  }

  @Override
  public int sizeOfIntersection(IntDomain domain) {
    if (size == 0 || domain.isEmpty() || domain.max() < minBound || domain.min() > maxBound) {
      return 0;
    }
    int result = 0;
    if (!byIntervals(domain)) {
      int hi = Math.min(maxBound, domain.max());
      for (int start = Math.max(minBound, domain.min()); start <= hi; start += 64) {
        result += Long.bitCount(bitsFrom(start) & bitsOf(domain, start));
      }
      return result;
    }
    IntDomain intervals = domain;
    for (int i = 0, n = intervals.noIntervals(); i < n; i++) {
      Interval interval = intervals.getInterval(i);
      int lo = Math.max(interval.min(), minBound);
      int hi = Math.min(interval.max(), maxBound);
      result += count(lo, hi);
    }
    return result;
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
    bitsVersion++;
    if (values.isEmpty()) {
      minBound = 0;
      maxBound = -1;
      size = 0;
      bits = null;
      wordStamp = null;
      ranges = null;
      return;
    }
    minBound = values.min();
    maxBound = values.max();
    size = values.getSize();
    bits = null;
    wordStamp = null;
    ranges = null;
    if (size != maxBound - minBound + 1 && rangeHoles) {
      int n = values.noIntervals();
      int[] pairs = new int[2 * n];
      for (int i = 0; i < n; i++) {
        pairs[2 * i] = values.leftElement(i);
        pairs[2 * i + 1] = values.rightElement(i);
      }
      ranges = pairs;
    } else if (size != maxBound - minBound + 1) {
      createBits(stamp);
      long[] fresh = new long[bits.length];
      for (int i = 0; i < fresh.length; i++) {
        fresh[i] = values.bitsFrom(base + (i << 6));
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
    IntDomain result = unionRuns(this, union);
    if (result.getSize() == size) {
      return NONE;
    }
    assign(result);
    return ANY;
  }

  @Override
  public void addDom(IntDomain domain) {
    assign(unionRuns(this, domain));
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
    IntDomain result = intersectRuns(this, intersect, 0);
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
    if (minBound > maxBound) {
      return "Min value is larger than max value " + minBound + " " + maxBound;
    }
    if (!present(minBound) || !present(maxBound)) {
      return "Bounds are not in the domain " + minBound + " " + maxBound;
    }
    if (size != count(minBound, maxBound)) {
      return "Size " + size + " does not match the values " + count(minBound, maxBound);
    }
    return null;
  }

  @Override
  public int sizeConstraintsOriginal() {
    return copy().sizeConstraintsOriginal();
  }
}
