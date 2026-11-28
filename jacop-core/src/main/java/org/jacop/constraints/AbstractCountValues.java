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
import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TrailedInts;

/**
 * Abstract base for CountValues and CountValuesBounds constraints. Provides shared fields (list,
 * values, valuesDomain, the trailed counts), impose, swap, and default pruning event.
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
  final int[] sortedValues;

  /** True when the counted values form one interval, so a value's sorted position is computed. */
  private final boolean contiguous;

  /** The position in values of each value of sortedValues. */
  final int[] indexOfSorted;

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

  private static final int POSITION = 0;

  private static final int REST = 1;

  /** The index in state of the number of decided variables equal to the first value. */
  private static final int EQUAL = 2;

  /**
   * The first position of undecided variables, the number of decided variables not matching any
   * counted value, and the number of decided variables equal to each value.
   */
  protected TrailedInts state;

  /*
   * The counted values each undecided variable can take, kept between calls so that a call reads
   * again only the domains that changed, as GlobalCardinality keeps its value lists (#582). A slot
   * is the position of a variable in the list as given; the list is permuted, origin follows it.
   * mayBeBits holds words bit sets over the sorted values per slot, cachedSize the domain size they
   * were read at (-1 when none), mayBeCount their sum over the undecided variables and restCount the
   * undecided variables with a value that is not counted. Within one path of the search domains
   * only shrink, so an unchanged size means an unchanged domain; when a level at which the cache
   * changed is removed, the cache is dropped and read again (stale). Null when too large.
   */
  private int[] origin;

  private long[] mayBeBits;

  private int[] cachedSize;

  private boolean[] cachedRest;

  private int[] mayBeCount;

  private int restCount;

  private int words;

  private long[] scratch;

  private boolean stale = true;

  private Store cacheStore;

  private int recordedLevel = -1;

  /** Drops the cache when a level at which it changed is removed. */
  private final Stateful cacheReset =
      level -> {
        stale = true;
        recordedLevel = -1;
      };

  /**
   * The most words of cached bit sets over all variables; above it every call reads all domains.
   */
  private static final int CACHE_WORDS_LIMIT = 1 << 20;

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

  @Override
  public void impose(Store store) {

    super.impose(store);

    state = new TrailedInts(store, EQUAL + values.length);

    cacheStore = store;
    words = (values.length + 63) >>> 6;
    if (values.length > 0 && (long) n * words <= CACHE_WORDS_LIMIT) {
      origin = new int[n];
      for (int i = 0; i < n; i++) {
        origin[i] = i;
      }
      mayBeBits = new long[n * words];
      cachedSize = new int[n];
      cachedRest = new boolean[n];
      mayBeCount = new int[values.length];
      scratch = new long[words];
    }
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
      if (origin != null) {
        int o = origin[i];
        origin[i] = origin[j];
        origin[j] = o;
      }
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
   * Counts the variables whose domain contains a value.
   *
   * @param value the value.
   * @return the number of variables that can take the value.
   */
  protected int countPossible(int value) {
    int count = 0;
    for (int j = 0; j < n; j++) {
      if (list[j].domain.contains(value)) {
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

    int start = state.get(POSITION);
    restEq = state.get(REST);
    for (int i = 0; i < values.length; i++) {
      numberEq[i] = state.get(EQUAL + i);
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

      if (!store.propagationHasOccurred && subsetBounds()) {
        pruneBySubsets(store, start);
      }

    } while (store.propagationHasOccurred);

    for (int i = 0; i < values.length; i++) {
      state.set(EQUAL + i, numberEq[i]);
    }
    state.set(REST, restEq);
    state.set(POSITION, start);

    // every variable is fixed or holds no counted value: the counts are exact and set, so no
    // change can prune
    if (start == n) {
      removeConstraint();
    }
  }

  /**
   * Counts, for the undecided variables from start on, how many are equal to or may take each value
   * and how many may take a value that is not counted. Variables that become decided (assigned, or
   * without any counted value) are moved before the new start and counted for good.
   */
  private int scanListAndCount(int start, int[] numberEq, int[] numberMayBe) {
    if (origin != null) {
      return scanChanged(start, numberEq, numberMayBe);
    }
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
   * Does what the scan below does, with the same counts, reading again only the variables whose
   * domain size changed since their counted values were cached.
   */
  private int scanChanged(int start, int[] numberEq, int[] numberMayBe) {
    if (stale) {
      Arrays.fill(mayBeBits, 0L);
      Arrays.fill(cachedSize, -1);
      Arrays.fill(cachedRest, false);
      Arrays.fill(mayBeCount, 0);
      restCount = 0;
      stale = false;
    }
    if (recordedLevel != cacheStore.level) {
      cacheStore.recordChange(cacheReset);
      recordedLevel = cacheStore.level;
    }
    for (int i = start; i < n; i++) {
      IntVar v = list[i];
      int slot = origin[i];
      if (v.singleton()) {
        int k = sortedPosition(v.value());
        if (k >= 0) {
          numberEq[indexOfSorted[k]]++;
        } else {
          restEq++;
        }
        dropCached(slot);
        swap(start, i);
        start++;
        continue;
      }
      int size = v.getSize();
      if (cachedSize[slot] == size) {
        continue;
      }
      Arrays.fill(scratch, 0L);
      bitsMode = true;
      int matched = countMayBe(v.domain);
      bitsMode = false;
      if (matched == 0) {
        dropCached(slot);
        swap(start, i);
        start++;
        restEq++;
        continue;
      }
      int base = slot * words;
      for (int w = 0; w < words; w++) {
        long old = mayBeBits[base + w];
        long now = scratch[w];
        for (long gone = old & ~now; gone != 0; gone &= gone - 1) {
          mayBeCount[(w << 6) + Long.numberOfTrailingZeros(gone)]--;
        }
        for (long fresh = now & ~old; fresh != 0; fresh &= fresh - 1) {
          mayBeCount[(w << 6) + Long.numberOfTrailingZeros(fresh)]++;
        }
        mayBeBits[base + w] = now;
      }
      boolean rest = matched < v.domain.getSize();
      if (rest != cachedRest[slot]) {
        restCount += rest ? 1 : -1;
        cachedRest[slot] = rest;
      }
      cachedSize[slot] = size;
    }
    restMayBe = restCount;
    for (int k = 0; k < sortedValues.length; k++) {
      numberMayBe[indexOfSorted[k]] = mayBeCount[k];
    }
    return start;
  }

  /** Takes the cached counted values of a slot out of the counts, as its variable is decided. */
  private void dropCached(int slot) {
    if (cachedSize[slot] < 0) {
      return;
    }
    int base = slot * words;
    for (int w = 0; w < words; w++) {
      for (long gone = mayBeBits[base + w]; gone != 0; gone &= gone - 1) {
        mayBeCount[(w << 6) + Long.numberOfTrailingZeros(gone)]--;
      }
      mayBeBits[base + w] = 0L;
    }
    if (cachedRest[slot]) {
      restCount--;
      cachedRest[slot] = false;
    }
    cachedSize[slot] = -1;
  }

  /** Whether mayBeRange records into scratch, as bits, instead of into mayBeDifference. */
  private boolean bitsMode;

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
        matched +=
            mayBeRange(lowerBound(intervals.leftElement(i)), upperBound(intervals.rightElement(i)));
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
    if (bitsMode) {
      setBits(from, to);
      return to - from;
    }
    mayBeDifference[from]++;
    mayBeDifference[to]--;
    return to - from;
  }

  /** Sets the bits from (inclusive) to to (exclusive) of scratch. */
  private void setBits(int from, int to) {
    int first = from >>> 6;
    int last = (to - 1) >>> 6;
    long firstMask = -1L << from;
    long lastMask = -1L >>> (63 - ((to - 1) & 63));
    if (first == last) {
      scratch[first] |= firstMask & lastMask;
      return;
    }
    scratch[first] |= firstMask;
    for (int w = first + 1; w < last; w++) {
      scratch[w] = -1L;
    }
    scratch[last] |= lastMask;
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

  /** The most classes (the counted values and the rest) whose subsets are checked. */
  private static final int SUBSET_CLASSES = 6;

  // per subset of the classes, the undecided variables whose classes all lie in it
  private int[] within;

  /**
   * Whether the propagation also bounds the counts of every set of classes, see {@link
   * #pruneBySubsets}.
   *
   * @return true if the counts of sets of classes are bounded, false by default.
   */
  protected boolean subsetBounds() {
    return false;
  }

  /**
   * Bounds the sum of the counters of every set S of at least two classes (counted values, or the
   * rest) by the number of variables that may take a class of S and the number that can take only
   * classes of S, as in the pigeonhole reasoning of the flow model of global cardinality (Regin,
   * Generalized arc consistency for global cardinality constraint, AAAI 1996). Each counter of S
   * gets the bounds left by the others, and a set at a bound takes or loses the variables it may
   * take. Only for at most {@link #SUBSET_CLASSES} classes, at a fixpoint of the other rules.
   */
  private void pruneBySubsets(Store store, int start) {
    int classes = values.length + 1;
    if (classes < 3 || classes > SUBSET_CLASSES) {
      return;
    }
    int full = (1 << classes) - 1;
    countWithin(start, classes, full);
    for (int set = 1; set < full; set++) {
      if (Integer.bitCount(set) >= 2) {
        boundSet(store, start, set, full);
      }
    }
  }

  /** Fills within: per set of classes, the undecided variables whose classes all lie in it. */
  private void countWithin(int start, int classes, int full) {
    if (within == null) {
      within = new int[full + 1];
    }
    Arrays.fill(within, 0);
    for (int j = start; j < n; j++) {
      within[classesOf(list[j].domain)]++;
    }
    // sums over subsets (zeta transform), one class at a time
    for (int b = 0; b < classes; b++) {
      int bit = 1 << b;
      for (int set = 0; set <= full; set++) {
        if ((set & bit) != 0) {
          within[set] += within[set ^ bit];
        }
      }
    }
  }

  /** Bounds the counters of one set of classes and prunes the variables of a set at a bound. */
  private void boundSet(Store store, int start, int set, int full) {
    int classes = values.length + 1;
    int fixed = 0;
    int minSum = 0;
    int maxSum = 0;
    for (int i = 0; i < classes; i++) {
      if ((set & (1 << i)) != 0) {
        fixed += i < values.length ? numberEq[i] : restEq;
        minSum += getExtendedCounterMin(i);
        maxSum += getExtendedCounterMax(i);
      }
    }
    int lo = fixed + within[set];
    int hi = fixed + (n - start) - within[full ^ set];
    if (minSum > hi || maxSum < lo) {
      throw Store.failException;
    }
    for (int i = 0; i < classes; i++) {
      if ((set & (1 << i)) != 0) {
        boundCounter(store, i, lo, hi, minSum, maxSum);
      }
    }
    if (lo < hi && maxSum == lo) {
      // the set holds only the variables that can take nothing else
      restrictStraddling(store, start, set, set);
    } else if (lo < hi && minSum == hi) {
      // the set holds every variable that may take it
      restrictStraddling(store, start, set, full ^ set);
    }
  }

  /** Removes the given classes from the variables that may take classes in and out of a set. */
  private void restrictStraddling(Store store, int start, int set, int remove) {
    for (int j = start; j < n; j++) {
      IntVar v = list[j];
      int mask = classesOf(v.domain);
      if ((mask & set) != 0 && (mask & ~set) != 0) {
        restrict(store, v, mask & remove);
      }
    }
  }

  /** Gives counter i of a set the bounds the other counters of the set leave. */
  private void boundCounter(Store store, int i, int lo, int hi, int minSum, int maxSum) {
    int min = getExtendedCounterMin(i);
    int max = getExtendedCounterMax(i);
    int newMin = Math.max(min, lo - (maxSum - max));
    int newMax = Math.min(max, hi - (minSum - min));
    if (newMin != min || newMax != max) {
      updateExtendedCounter(store, i, newMin, newMax);
    }
  }

  /** The classes a domain may take: bit i for values[i], the last bit for the rest. */
  private int classesOf(IntDomain domain) {
    int mask = 0;
    for (int i = 0; i < values.length; i++) {
      if (domain.contains(values[i])) {
        mask |= 1 << i;
      }
    }
    if (!valuesDomain.contains(domain)) {
      mask |= 1 << values.length;
    }
    return mask;
  }

  /** Removes from a variable the classes of a set. */
  private void restrict(Store store, IntVar v, int remove) {
    for (int i = 0; i < values.length; i++) {
      if ((remove & (1 << i)) != 0) {
        v.domain.inComplement(store.level, v, values[i]);
      }
    }
    if ((remove & (1 << values.length)) != 0) {
      v.domain.in(store.level, v, valuesDomain);
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
