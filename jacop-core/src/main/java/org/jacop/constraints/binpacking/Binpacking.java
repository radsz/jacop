/*
 * Binpacking.java
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

package org.jacop.constraints.binpacking;

import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.Builder;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Binpacking constraint implements bin packing problem. It ensures that items are packed into bins
 * while respecting cpacity constraints of each bin.
 *
 * <p>This implementation is based on paper "A Constraint for Bin Packing" by Paul Shaw, CP 2004.
 *
 * <p>This constraint is not idempotent (does not compute fix-point) and, in case when another
 * computation for fix-point is needed, it adds itself to the constraint queue.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Binpacking extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent {

  private static final AtomicInteger idNumber = new AtomicInteger(0);
  static long LBnumber;

  /** It keeps together a list of variables which define bin for item i and their weigts. */
  private final BinItem[] item;

  /** Bin variables of items with weight zero; they are only restricted to the existing bins. */
  private final IntVar[] zeroWeightBins;

  /** It specifies a list of variables which define bin load. */
  private final IntVar[] load;

  private final LinkedHashSet<IntVar> itemQueue = new LinkedHashSet<>();
  private final LinkedHashSet<IntVar> binQueue = new LinkedHashSet<>();
  private final Map<IntVar, Integer> itemMap;
  private final Map<IntVar, Integer> binMap;
  boolean lbPruning = true;
  private boolean firstConsistencyCheck = true;
  private int minBinNumber;
  private long sizeAllItems;
  private long alphaP;
  private long betaP;

  /**
   * It constructs the binpacking constraint for the supplied variable.
   *
   * @param bin which are constrained to define bin for item i.
   * @param load which are constrained to define load for bin i.
   * @param w which define size of item i.
   */
  public Binpacking(IntVar[] bin, IntVar[] load, int[] w) {
    this(bin, load, w, computeDefaultMinBin(bin, w));
  }

  /**
   * It constructs the binpacking constraint for the supplied variable.
   *
   * @param bin which are constrained to define bin for item i.
   * @param load which are constrained to define load for bin i.
   * @param w which define size of item i.
   */
  public Binpacking(List<? extends IntVar> bin, List<? extends IntVar> load, int[] w) {
    this(bin.toArray(new IntVar[0]), load.toArray(new IntVar[0]), w);
  }

  /**
   * It constructs the binpacking constraint for the supplied variable.
   *
   * @param bin which are constrained to define bin for item i.
   * @param load which are constrained to define load for bin i.
   * @param w which define size of item i.
   * @param minBin minimal index of a bin; overrides the value computed from bin variable domains
   */
  public Binpacking(IntVar[] bin, IntVar[] load, int[] w, int minBin) {

    checkInputForNullness(new String[] {"bin", "load", "w"}, bin, load, new Object[] {w});
    checkInputForDuplication("load", load);
    checkInput(w, t -> t >= 0, "weight for item is not >=0");

    if (bin.length != w.length) {
      throw new IllegalArgumentException(
          "Constraint BinPacking has arguments bin and w that are of different sizes");
    }

    LinkedHashMap<IntVar, Integer> itemPar = new LinkedHashMap<>();
    LinkedHashSet<IntVar> zeroWeight = new LinkedHashSet<>();
    for (int i = 0; i < bin.length; i++) {

      if (w[i] == 0) {
        zeroWeight.add(bin[i]);
      } else {
        if (itemPar.get(bin[i]) != null) {
          // a weight above IntDomain.MAX_INT fits in no bin; capping it avoids int overflow
          int s = itemPar.get(bin[i]);
          itemPar.put(bin[i], (int) Math.min((long) s + w[i], IntDomain.MAX_INT + 1L));
        } else {
          itemPar.put(bin[i], w[i]);
        }
      }
    }

    zeroWeight.removeAll(itemPar.keySet());
    this.zeroWeightBins = zeroWeight.toArray(new IntVar[0]);

    this.numberId = idNumber.incrementAndGet();
    this.item = new BinItem[itemPar.size()];
    this.queueIndex = 2;

    minBinNumber = minBin;
    Set<Map.Entry<IntVar, Integer>> entries = itemPar.entrySet();
    int j = 0;
    for (Map.Entry<IntVar, Integer> e : entries) {
      IntVar b = e.getKey();
      int ws = e.getValue();
      item[j] = new BinItem(b, ws);

      sizeAllItems += ws;
      j++;
    }

    this.load = Arrays.copyOf(load, load.length);

    binMap = Var.positionMapping(load, false, this.getClass());

    Comparator<BinItem> weightComparator = (o1, o2) -> Integer.compare(o2.weight(), o1.weight());
    Arrays.sort(item, weightComparator);

    itemMap =
        Var.positionMapping(
            Arrays.stream(item).map(BinItem::bin).toArray(IntVar[]::new), false, this.getClass());

    setScope(Stream.concat(Arrays.stream(item).map(BinItem::bin), Arrays.stream(load)));
  }

  /**
   * It constructs the binpacking constraint for the supplied variable.
   *
   * @param bin which are constrained to define bin for item i.
   * @param load which are constrained to define load for bin i.
   * @param w which define size of item i.
   * @param minBin minimal index of a bin; overrides the value computed from bin variable domains
   */
  public Binpacking(List<? extends IntVar> bin, List<? extends IntVar> load, int[] w, int minBin) {
    this(bin.toArray(new IntVar[0]), load.toArray(new IntVar[0]), w, minBin);
  }

  private static int computeDefaultMinBin(IntVar[] bin, int[] w) {
    int min = Integer.MAX_VALUE;
    for (int i = 0; i < bin.length; i++) {
      if (w[i] != 0 && bin[i].min() < min) {
        min = bin[i].min();
      }
    }
    return min == Integer.MAX_VALUE && bin.length > 0 ? bin[0].min() : min;
  }

  /**
   * It constructs a binpacking constraint.
   *
   * @param bin array of variables representing bin assignment for each item.
   * @param load array of variables representing the load in each bin.
   * @param w array of weights for each item.
   * @param minBin minimum bin number to consider.
   * @param lbPruning flag indicating whether to enable lower bound pruning.
   */
  @Builder
  public Binpacking(IntVar[] bin, IntVar[] load, int[] w, int minBin, boolean lbPruning) {
    this(bin, load, w, minBin);
    this.lbPruning = lbPruning;
  }

  /** Rule "Pack All" -- applied only on first consistency check. */
  private void applyPackAllRule(Store store) {
    if (!firstConsistencyCheck) {
      return;
    }
    Arrays.stream(item)
        .map(BinItem::bin)
        .forEach(i -> i.domain.in(store.level, i, minBinNumber, load.length - 1 + minBinNumber));
    for (IntVar b : zeroWeightBins) {
      b.domain.in(store.level, b, minBinNumber, load.length - 1 + minBinNumber);
    }
    firstConsistencyCheck = false;
  }

  /** Collects changed bin/item indices into an IntervalDomain for propagation. */
  private IntervalDomain collectChangedDomains() {
    IntervalDomain d = new IntervalDomain();
    while (!binQueue.isEmpty()) {
      Iterator<IntVar> it = binQueue.iterator();
      IntVar v = it.next();
      it.remove();
      int i = binMap.get(v) + minBinNumber;
      d.addDom(new IntervalDomain(i, i));
    }
    while (!itemQueue.isEmpty()) {
      Iterator<IntVar> it = itemQueue.iterator();
      IntVar v = it.next();
      it.remove();
      IntDomain pd = v.dom().getPreviousDomain();
      if (pd != null) {
        d.addDom(pd);
      } else {
        d.addDom(v.dom());
      }
    }
    return d;
  }

  /** Bins to be (re)processed in the current consistency call, indexed from 0. */
  private BitSet todo = new BitSet();

  /** Removes bin binIdx from an item and schedules the bins whose item sets changed. */
  private void removeBin(Store store, IntVar b, int binIdx) {
    if (b.domain.contains(binIdx)) {
      b.domain.inComplement(store.level, b, binIdx);
      todo.set(binIdx - minBinNumber);
      if (b.singleton()) { // the item is now required in its last bin
        int k = b.value() - minBinNumber;
        if (k >= 0 && k < load.length) {
          todo.set(k);
        }
      }
    }
  }

  /** Puts an item into bin binIdx and schedules every bin it could be in before. */
  private void assignBin(Store store, IntVar b, int binIdx) {
    if (!b.singleton()) {
      for (ValueEnumeration e = b.dom().valueEnumeration(); e.hasMoreElements(); ) {
        int k = e.nextElement() - minBinNumber;
        if (k >= 0 && k < load.length) {
          todo.set(k);
        }
      }
    }
    b.domain.inValue(store.level, b, binIdx);
  }

  /** Processes one bin index: load maintenance, tightening, elimination/commitment. */
  private void processBin(Store store, int i) {
    if (i < 0 || i >= load.length) {
      return;
    }
    int loadMin = load[i].min();
    int loadMax = load[i].max();
    BinItem[] candidates = new BinItem[item.length];
    int candidatesLength = 0;
    long required = 0;
    long possible = 0;
    int binIdx = i + minBinNumber;
    for (BinItem itemEl : item) {
      if (itemEl.bin().dom().contains(binIdx)) {
        possible += itemEl.weight();
        if (itemEl.bin().singleton()) {
          required += itemEl.weight();
        } else {
          candidates[candidatesLength++] = itemEl;
        }
      }
    }
    load[i].domain.in(store.level, load[i], clamp(required), clamp(possible));
    applyLoadMaintenanceToCandidates(
        store, i, binIdx, required, possible, candidates, candidatesLength);
    int[] Cj = new int[candidatesLength];
    for (int l = 0; l < candidatesLength; l++) {
      Cj[l] = candidates[l].weight();
    }
    applyTighteningBounds(store, i, required, Cj);
    applyEliminationAndCommitment(store, i, binIdx, required, candidates, Cj, candidatesLength);
    if (load[i].min() != loadMin || load[i].max() != loadMax) {
      todo.set(i);
    }
  }

  private void applyLoadMaintenanceToCandidates(
      Store store,
      int i,
      int binIdx,
      long required,
      long possible,
      BinItem[] candidates,
      int candidatesLength) {
    int loadMin = load[i].min();
    int loadMax = load[i].max();
    for (int l = 0; l < candidatesLength; l++) {
      BinItem bi = candidates[l];
      if (required + bi.weight() > loadMax) {
        removeBin(store, bi.bin(), binIdx);
      } else if (possible - bi.weight() < loadMin) {
        assignBin(store, bi.bin(), binIdx);
      }
    }
  }

  private void applyTighteningBounds(Store store, int i, long required, int[] candidateWeights) {
    long sumCandidates = sum(candidateWeights);
    int len = candidateWeights.length;
    if (noSum(
        candidateWeights, len, sumCandidates, load[i].min() - required, load[i].min() - required)) {
      load[i].domain.inMin(store.level, load[i], clamp(required + betaP));
    }
    if (noSum(
        candidateWeights, len, sumCandidates, load[i].max() - required, load[i].max() - required)) {
      load[i].domain.inMax(store.level, load[i], clamp(required + alphaP));
    }
  }

  private void applyEliminationAndCommitment(
      Store store,
      int i,
      int binIdx,
      long required,
      BinItem[] candidates,
      int[] candidateWeights,
      int candidatesLength) {
    if (candidatesLength == 0) {
      return;
    }
    long loadMin = load[i].min();
    long loadMax = load[i].max();
    long sumCandidates = sum(candidateWeights);
    // candidate weights without candidate j, kept in descending order; moving from j to j + 1 only
    // puts weight j back at position j
    int[] others = Arrays.copyOfRange(candidateWeights, 1, candidatesLength);
    for (int j = 0; j < candidatesLength; j++) {
      if (j > 0) {
        others[j - 1] = candidateWeights[j - 1];
      }
      long sumOthers = sumCandidates - candidateWeights[j];
      if (noSum(
          others,
          candidatesLength - 1,
          sumOthers,
          loadMin - required - candidateWeights[j],
          loadMax - required - candidateWeights[j])) {
        removeBin(store, candidates[j].bin(), binIdx);
      }
      if (noSum(others, candidatesLength - 1, sumOthers, loadMin - required, loadMax - required)) {
        assignBin(store, candidates[j].bin(), binIdx);
      }
    }
  }

  /** Rule "Load and Size Coherence": updates load domains from global capacity. */
  private void applyLoadAndSizeCoherence(Store store) {
    long allCapacityMin = 0;
    long allCapacityMax = 0;
    for (IntVar aLoad : load) {
      allCapacityMin += aLoad.min();
      allCapacityMax += aLoad.max();
    }
    long s1 = sizeAllItems - allCapacityMax;
    long s2 = sizeAllItems - allCapacityMin;
    for (int i = 0; i < load.length; i++) {
      IntVar aLoad = load[i];
      int min = aLoad.min();
      int max = aLoad.max();
      aLoad.domain.in(store.level, aLoad, clamp(s1 + max), clamp(s2 + min));
      if (aLoad.min() != min || aLoad.max() != max) {
        todo.set(i);
      }
    }
  }

  @Override
  public void consistency(Store store) {
    applyPackAllRule(store);
    todo.clear();
    IntervalDomain d = collectChangedDomains();
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      int i = e.nextElement() - minBinNumber;
      if (i >= 0 && i < load.length) {
        todo.set(i);
      }
    }
    // Apply the rules until no bin changes (the changes made here are not queued by the store).
    do {
      for (int i = todo.nextSetBit(0); i >= 0; i = todo.nextSetBit(0)) {
        todo.clear(i);
        processBin(store, i);
      }
      applyLoadAndSizeCoherence(store);
    } while (!todo.isEmpty());
    if (lbPruning) {
      lbNumberBins();
    }
  }

  /** Computes and applies the lower bound on the number of bins required. */
  void lbNumberBins() {
    // Lower bound of number of bins pruning
    int[] unpacked = new int[item.length];
    int unpackedLength = 0;
    int[] a = new int[load.length];

    for (BinItem itemI : item) {
      if (itemI.bin().singleton()) {
        int p = itemI.bin().value() - minBinNumber;
        a[p] += itemI.weight();
      } else {
        unpacked[unpackedLength++] = itemI.weight();
      }
    }
    if (unpackedLength == 0) {
      return;
    }

    int firstBin = IntDomain.MAX_INT;
    int lastBin = IntDomain.MIN_INT;
    for (BinItem anItem : item) {
      firstBin = Math.min(firstBin, anItem.bin().min());
      lastBin = Math.max(lastBin, anItem.bin().max());
    }
    int first = Math.max(0, firstBin - minBinNumber);
    int last = Math.min(load.length - 1, lastBin - minBinNumber);
    int nb = last - first + 1;

    // Free space of every bin that items can still use; the items already packed and the
    // capacity a bin lacks compared to the largest one become one virtual item per bin.
    int[] free = new int[nb];
    int maxCapacity = 0;
    int maxFree = 0;
    for (int i = first; i <= last; i++) {
      free[i - first] = load[i].max() - a[i];
      maxCapacity = Math.max(maxCapacity, load[i].max());
      maxFree = Math.max(maxFree, free[i - first]);
    }

    if (maxCapacity <= 0) {
      throw Store.failException; // unpacked items of positive weight and no capacity
    }

    // Reduction R0 (Shaw 2004): capacity is the largest bin capacity.
    lbBins(withVirtualItems(unpacked, unpackedLength, free, maxCapacity), maxCapacity, nb);
    // Reduction RMin (Dupuis, Schaus and Deville 2010): capacity and virtual items lowered by
    // the smallest virtual item, i.e. capacity is the largest free space. Neither dominates.
    if (maxFree > 0 && maxFree < maxCapacity) {
      lbBins(withVirtualItems(unpacked, unpackedLength, free, maxFree), maxFree, nb);
    }
  }

  /** Unpacked items and one virtual item per bin (capacity - free space), in descending order. */
  private int[] withVirtualItems(int[] unpacked, int unpackedLength, int[] free, int capacity) {
    int[] v = new int[free.length];
    for (int i = 0; i < free.length; i++) {
      v[i] = capacity - free[i];
    }
    Arrays.sort(v); // ascending, merge reads it backwards
    return merge(unpacked, unpackedLength, v);
  }

  private int[] merge(int[] a, int arrLength, int[] b) {
    int[] c = new int[arrLength + b.length];
    int i = 0;
    int j = b.length - 1;
    for (int k = 0; k < c.length; k++) {
      if (i >= arrLength) {
        c[k] = b[j--];
      } else if (j < 0) {
        c[k] = a[i++];
      } else if (a[i] >= b[j]) {
        c[k] = a[i++];
      } else {
        c[k] = b[j--];
      }
    }
    return c;
  }

  @Override
  public boolean satisfied() {

    grounded();

    return false;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (itemMap.containsKey(v)) {
      itemQueue.add((IntVar) v);
    } else {
      binQueue.add((IntVar) v);
    }
  }

  @Override
  public void removeLevel(int level) {
    itemQueue.clear();
    binQueue.clear();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : binpacking([");

    for (int i = 0; i < item.length; i++) {
      result.append(item[i].bin());
      if (i < item.length - 1) {
        result.append(", ");
      }
    }
    result.append("], [");
    for (int i = 0; i < load.length; i++) {
      result.append(load[i]);
      if (i < load.length - 1) {
        result.append(", ");
      }
    }
    result.append("], [");
    for (int i = 0; i < item.length; i++) {
      result.append(item[i].weight());
      if (i < item.length - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(lbPruning).append(")");

    return result.toString();
  }

  /** Converts a long bound to an int; values outside the domain range still prune or fail. */
  private static int clamp(long v) {
    return (int) Math.max(IntDomain.MIN_INT - 1L, Math.min(IntDomain.MAX_INT + 1L, v));
  }

  /**
   * NoSum of Shaw (2004) on the first len weights of x, sorted in descending order, summing to
   * sumX.
   */
  private boolean noSum(int[] x, int len, long sumX, long alpha, long beta) {

    if (alpha <= 0 || beta >= sumX) {
      return false;
    }

    long sumA = 0;
    long sumB;
    long sumC = 0;
    int k = 0;
    int kPrime = 0;
    int n = len - 1; // |x|

    while (sumC + x[n - kPrime] < alpha) {
      sumC += x[n - kPrime];
      kPrime++;
    }

    sumB = x[n - kPrime];
    while (sumA < alpha && sumB <= beta) {
      sumA += x[k++];
      if (sumA < alpha) {
        kPrime--;
        sumB += x[n - kPrime];
        sumC -= x[n - kPrime];
        while (sumA + sumC >= alpha) {
          kPrime--;
          sumC -= x[n - kPrime];
          sumB += x[n - kPrime] - x[n - kPrime - k - 1];
        }
      }
    }

    alphaP = sumA + sumC;
    betaP = sumB;

    return sumA < alpha;
  }

  private long sum(int[] x) {
    long summa = 0;
    for (int v : x) {
      summa += v;
    }
    return summa;
  }

  private void lbBins(int[] x, int capacity, int nb) {
    int nn = x.length;
    long sum = sum(x);
    long lb = sum / capacity + (sum % capacity != 0 ? 1 : 0);

    if (nb < lb) {
      throw Store.failException;
    }

    // Martello and Toth's L2 is the maximum of L(k) over 0 <= k <= capacity / 2, but L(k) only
    // needs to be evaluated for k = 0 and for the distinct item sizes up to capacity / 2
    // (x is sorted in descending order).
    int previous = -1;
    for (int j = nn; j >= 0; j--) {
      int k = j == nn ? 0 : x[j];
      if (k > capacity / 2) {
        break;
      }
      if (k == previous) {
        continue;
      }
      previous = k;
      long currentLb = computeLbForK(x, nn, capacity, k);
      if (currentLb > lb) {
        lb = currentLb;
      }
    }
    if (nb < lb) {
      throw Store.failException;
    }
  }

  private long computeLbForK(int[] x, int nn, int capacity, int k) {
    int N1 = 0;
    int N2 = 0;
    int i = 0;
    while (i < nn && x[i] > capacity - k) {
      N1++;
      i++;
    }
    long freeSpaceN2 = 0;
    while (i < nn && x[i] > capacity / 2) {
      N2++;
      freeSpaceN2 += capacity - x[i];
      i++;
    }
    long sizeInN3 = 0;
    while (i < nn && x[i] >= k) {
      sizeInN3 += x[i];
      i++;
    }
    long toPack = sizeInN3 - freeSpaceN2;
    long noBinsN3 = 0;
    if (toPack > 0) {
      noBinsN3 = toPack / capacity + (toPack % capacity > 0 ? 1 : 0);
    }
    return N1 + N2 + noBinsN3;
  }
}
