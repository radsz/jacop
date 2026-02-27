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
import org.jacop.core.TimeStamp;
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

  /** It specifies a list of variables which define bin load. */
  private final IntVar[] load;

  private final LinkedHashSet<IntVar> itemQueue = new LinkedHashSet<>();
  private final LinkedHashSet<IntVar> binQueue = new LinkedHashSet<>();
  private final Map<IntVar, Integer> itemMap;
  private final Map<IntVar, Integer> binMap;
  boolean lbPruning = true;
  private boolean firstConsistencyCheck = true;
  private int minBinNumber;
  private int sizeAllItems;
  private int alphaP;
  private int betaP;
  private TimeStamp<Boolean> lbPruningStamp;

  /**
   * It constructs the binpacking constraint for the supplied variable.
   *
   * @param bin which are constrained to define bin for item i.
   * @param load which are constrained to define load for bin i.
   * @param w which define size ofitem i.
   */
  public Binpacking(IntVar[] bin, IntVar[] load, int[] w) {

    checkInputForNullness(new String[] {"bin", "load", "w"}, bin, load, new Object[] {w});
    checkInputForDuplication("load", load);
    checkInput(w, t -> t >= 0, "weight for item is not >=0");

    if (bin.length != w.length) {
      throw new IllegalArgumentException(
          "Constraint BinPacking has arguments bin and w that are of different sizes");
    }

    LinkedHashMap<IntVar, Integer> itemPar = new LinkedHashMap<>();
    for (int i = 0; i < bin.length; i++) {

      if (w[i] != 0) {
        if (itemPar.get(bin[i]) != null) {
          Integer s = itemPar.get(bin[i]);
          Integer ns = s + w[i];
          itemPar.put(bin[i], ns);
        } else {
          itemPar.put(bin[i], w[i]);
        }
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.item = new BinItem[itemPar.size()];
    this.queueIndex = 2;

    minBinNumber = bin[0].min();
    Set<Map.Entry<IntVar, Integer>> entries = itemPar.entrySet();
    int j = 0;
    for (Map.Entry<IntVar, Integer> e : entries) {
      IntVar b = e.getKey();
      int ws = e.getValue();
      item[j] = new BinItem(b, ws);

      sizeAllItems += ws;

      if (minBinNumber > b.min()) {
        minBinNumber = b.min();
      }
      j++;
    }

    this.load = Arrays.copyOf(load, load.length);

    binMap = Var.positionMapping(load, false, this.getClass());

    Comparator<BinItem> weightComparator = (o1, o2) -> o2.weight() - o1.weight();
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
   * @param w which define size ofitem i.
   */
  public Binpacking(List<? extends IntVar> bin, List<? extends IntVar> load, int[] w) {
    this(bin.toArray(new IntVar[0]), load.toArray(new IntVar[0]), w);
  }

  /**
   * It constructs the binpacking constraint for the supplied variable.
   *
   * @param bin which are constrained to define bin for item i.
   * @param load which are constrained to define load for bin i.
   * @param w which define size ofitem i.
   * @param minBin minimal index of a bin; ovewrite the value provided by minimal index of variable
   *     bin
   */
  public Binpacking(IntVar[] bin, IntVar[] load, int[] w, int minBin) {
    this(bin, load, w);
    minBinNumber = minBin;
  }

  /**
   * It constructs the binpacking constraint for the supplied variable.
   *
   * @param bin which are constrained to define bin for item i.
   * @param load which are constrained to define load for bin i.
   * @param w which define size ofitem i.
   * @param minBin minimal index of a bin; ovewrite the value provided by minimal index of variable
   *     bin
   */
  public Binpacking(List<? extends IntVar> bin, List<? extends IntVar> load, int[] w, int minBin) {

    this(bin.toArray(new IntVar[0]), load.toArray(new IntVar[0]), w);
    minBinNumber = minBin;
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

  @Override
  public void impose(Store store) {
    super.impose(store);
    lbPruningStamp = new TimeStamp<>(store, true);
  }

  /** Rule "Pack All" -- applied only on first consistency check. */
  private void applyPackAllRule(Store store) {
    if (!firstConsistencyCheck) {
      return;
    }
    Arrays.stream(item)
        .map(BinItem::bin)
        .forEach(i -> i.domain.in(store.level, i, minBinNumber, load.length - 1 + minBinNumber));
    firstConsistencyCheck = false;
  }

  /** Returns true if LB pruning should be skipped this round (all bins used). */
  private boolean updatePruneLbFlag(boolean pruneLb) {
    if (!pruneLb) {
      return false;
    }
    BitSet binUsed = new BitSet(load.length + minBinNumber);
    for (BinItem itemEl : item) {
      if (itemEl.bin().singleton()) {
        binUsed.set(itemEl.bin().value());
      }
    }
    if (binUsed.cardinality() == load.length) {
      lbPruningStamp.update(false);
      return false;
    }
    return true;
  }

  /** Collects changed bin/item indices into an IntervalDomain for propagation. */
  private IntervalDomain collectChangedDomains(Store store) {
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
      IntDomain pd = v.dom().previousDomain;
      if (pd != null) {
        d.addDom(pd);
      } else {
        d.addDom(v.dom());
      }
    }
    return d;
  }

  /** Processes one bin index: load maintenance, tightening, elimination/commitment. */
  private void processBin(Store store, int i) {
    if (i < 0 || i >= load.length) {
      return;
    }
    BinItem[] candidates = new BinItem[item.length];
    int candidatesLength = 0;
    int required = 0;
    int possible = 0;
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
    load[i].domain.in(store.level, load[i], required, possible);
    applyLoadMaintenanceToCandidates(
        store, i, binIdx, required, possible, candidates, candidatesLength);
    int[] Cj = new int[candidatesLength];
    for (int l = 0; l < candidatesLength; l++) {
      Cj[l] = candidates[l].weight();
    }
    applyTighteningBounds(store, i, required, Cj, candidatesLength);
    applyEliminationAndCommitment(store, i, binIdx, required, candidates, Cj, candidatesLength);
  }

  private void applyLoadMaintenanceToCandidates(
      Store store,
      int i,
      int binIdx,
      int required,
      int possible,
      BinItem[] candidates,
      int candidatesLength) {
    for (int l = 0; l < candidatesLength; l++) {
      BinItem bi = candidates[l];
      if (required + bi.weight() > load[i].max()) {
        bi.bin().domain.inComplement(store.level, bi.bin(), binIdx);
      } else if (possible - bi.weight() < load[i].min()) {
        bi.bin().domain.inValue(store.level, bi.bin(), binIdx);
      }
    }
  }

  private void applyTighteningBounds(
      Store store, int i, int required, int[] Cj, int candidatesLength) {
    if (noSum(Cj, load[i].min() - required, load[i].min() - required)) {
      load[i].domain.inMin(store.level, load[i], required + betaP);
    }
    if (noSum(Cj, load[i].max() - required, load[i].max() - required)) {
      load[i].domain.inMax(store.level, load[i], required + alphaP);
    }
  }

  private void applyEliminationAndCommitment(
      Store store,
      int i,
      int binIdx,
      int required,
      BinItem[] candidates,
      int[] Cj,
      int candidatesLength) {
    for (int j = 0; j < candidatesLength; j++) {
      int[] CjMinusI = new int[candidatesLength - 1];
      System.arraycopy(Cj, 0, CjMinusI, 0, j);
      System.arraycopy(Cj, j + 1, CjMinusI, j, Cj.length - j - 1);
      if (noSum(CjMinusI, load[i].min() - required - Cj[j], load[i].max() - required - Cj[j])) {
        candidates[j].bin().domain.inComplement(store.level, candidates[j].bin(), binIdx);
      }
      if (noSum(CjMinusI, load[i].min() - required, load[i].max() - required)) {
        candidates[j].bin().domain.inValue(store.level, candidates[j].bin(), binIdx);
      }
    }
  }

  /** Rule "Load and Size Coherence": updates load domains from global capacity. */
  private void applyLoadAndSizeCoherence(Store store) {
    int allCapacityMin = 0;
    int allCapacityMax = 0;
    for (IntVar aLoad : load) {
      allCapacityMin += aLoad.min();
      allCapacityMax += aLoad.max();
    }
    int s1 = sizeAllItems - allCapacityMax;
    int s2 = sizeAllItems - allCapacityMin;
    for (IntVar aLoad : load) {
      aLoad.domain.in(store.level, aLoad, s1 + aLoad.max(), s2 + aLoad.min());
    }
  }

  @Override
  public void consistency(Store store) {
    applyPackAllRule(store);
    boolean pruneLb = lbPruning && lbPruningStamp.value();
    pruneLb = updatePruneLbFlag(pruneLb);
    store.propagationHasOccurred = false;
    IntervalDomain d = collectChangedDomains(store);
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      int i = e.nextElement() - minBinNumber;
      processBin(store, i);
    }
    applyLoadAndSizeCoherence(store);
    if (store.propagationHasOccurred) {
      store.addChanged(this);
    } else if (lbPruning && pruneLb) {
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

    int maxCapacity = 0;
    for (IntVar c : load) {
      int maxC = c.max();
      if (maxCapacity < maxC) {
        maxCapacity = maxC;
      }
    }

    for (int i = 0; i < load.length; i++) {
      if (a[i] != 0) { // consider only already loaded bins to add additional "load"
        a[i] += maxCapacity - load[i].max();
      }
    }

    Arrays.sort(a); // sort array a in ascending order

    int[] z = merge(unpacked, unpackedLength, a);

    // check if there is enough binns to pack all items by computing LB.
    // If the number of possible bins is lower than lower bound then fail
    lbBins(z, maxCapacity, getNumberBins(item));
  }

  private int getNumberBins(BinItem[] item) {
    int min = IntDomain.MAX_INT;
    int max = 0;
    for (BinItem anItem : item) {
      IntVar bin = anItem.bin();
      int bmin = bin.min();
      int bmax = bin.max();
      max = Math.max(max, bmax);
      min = Math.min(min, bmin);
    }
    return max - min + 1;
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
    if (itemMap.containsKey((IntVar) v)) {
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

  private boolean noSum(int[] x, int alpha, int beta) {

    if (alpha <= 0 || beta >= sum(x)) {
      return false;
    }

    int sumA = 0;
    int sumB;
    int sumC = 0;
    int k = 0;
    int kPrime = 0;
    int n = x.length - 1; // |x|

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

  private int sum(int[] x) {
    int summa = 0;
    for (int v : x) {
      summa += v;
    }
    return summa;
  }

  private void lbBins(int[] x, int capacity, int nb) {
    int nn = x.length;
    int sum = sum(x);
    int lb = sum / capacity + (sum % capacity != 0 ? 1 : 0);

    if (nb < lb) {
      throw Store.failException;
    }

    for (int k = 0; k <= capacity / 2; k++) {
      int currentLb = computeLbForK(x, nn, capacity, k);
      if (currentLb > lb) {
        lb = currentLb;
      }
    }
    if (nb < lb) {
      throw Store.failException;
    }
  }

  private int computeLbForK(int[] x, int nn, int capacity, int k) {
    int N1 = 0;
    int N2 = 0;
    int i = 0;
    while (i < nn && x[i] > capacity - k) {
      N1++;
      i++;
    }
    int freeSpaceN2 = 0;
    while (i < nn && x[i] > capacity / 2) {
      N2++;
      freeSpaceN2 += capacity - x[i];
      i++;
    }
    int sizeInN3 = 0;
    while (i < nn && x[i] >= k) {
      sizeInN3 += x[i];
      i++;
    }
    int toPack = sizeInN3 - freeSpaceN2;
    int noBinsN3 = 0;
    if (toPack > 0) {
      noBinsN3 = toPack / capacity + (toPack % capacity > 0 ? 1 : 0);
    }
    return N1 + N2 + noBinsN3;
  }
}
