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
import java.util.HashMap;
import java.util.HashSet;
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
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Linearizations;
import org.jacop.core.FailException;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;

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
    implements UsesQueueVariable,
        Stateful,
        SatisfiedPresent,
        Copyable<Binpacking>,
        Explainable,
        Linearizations.Relaxable {

  private static final AtomicInteger idNumber = new AtomicInteger(0);
  static long LBnumber;

  /** It keeps together a list of variables which define bin for item i and their weigts. */
  private final BinItem[] item;

  /** Bin variables of items with weight zero; they are only restricted to the existing bins. */
  private final IntVar[] zeroWeightBins;

  /** It specifies a list of variables which define bin load. */
  private final IntVar[] load;

  /** The number of items in each bin, or null when the constraint has no cardinality variables. */
  private final IntVar[] card;

  /** Number of items given for each entry of item, which merges items sharing a bin variable. */
  private final int[] itemCount;

  /** Number of items given for each entry of zeroWeightBins. */
  private final int[] zeroWeightCount;

  /** Number of items given to the constraint, weight 0 included. */
  private final int totalCount;

  /** True when no two items share a bin variable, so the weight-based cardinality rules apply. */
  private final boolean unitItems;

  /**
   * True if the cardinality rules also run without card variables. Off by default: on bin packing
   * benchmarks without cardinalities they cut few failures and cost 10-15% per node with many bins.
   */
  private boolean cardinalityReasoning;

  private final LinkedHashSet<IntVar> itemQueue = new LinkedHashSet<>();
  private final LinkedHashSet<IntVar> binQueue = new LinkedHashSet<>();
  private final Map<IntVar, Integer> itemMap;
  private final Map<IntVar, Integer> binMap;
  boolean lbPruning = true;

  /** Rule "Pack All", applied in the first consistency call. */
  private final InitOnce packAll = new InitOnce();

  /** Level of the first consistency call, the root of the search. */
  private int rootLevel = -1;

  /** True if the bin-count bound also uses f_CCM1 and reduction RMax. */
  private boolean strongBinCountBound;

  private int minBinNumber;
  private long sizeAllItems;

  /** The sums alpha' and beta' of the last NoSum. */
  private final long[] noSumBounds = new long[2];

  /** Distinct sizes and their multiplicities of the items given to the bin-count bounds. */
  private final int[] sizes;

  private final int[] counts;

  /**
   * Whether the explanations cover the cardinality rules; -Djacop.lcg.binpackingCounts=false leaves
   * them to the generic reason.
   */
  private static final boolean COUNT_EXPLANATIONS =
      !"false".equals(System.getProperty("jacop.lcg.binpackingCounts"));

  /** The explanations for lazy clause generation, created when first needed. */
  private BinpackingExplanation explanation;

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
    this(bin, load, w, minBin, (IntVar[]) null);
  }

  /**
   * It constructs the binpacking constraint with the number of items in each bin (bin packing with
   * cardinality, Schaus et al. CP 2012).
   *
   * @param bin which are constrained to define bin for item i.
   * @param load which are constrained to define load for bin i.
   * @param w which define size of item i.
   * @param minBin minimal index of a bin; overrides the value computed from bin variable domains
   * @param card the number of items in bin i, items of weight 0 included; null for none.
   */
  public Binpacking(IntVar[] bin, IntVar[] load, int[] w, int minBin, IntVar[] card) {

    checkInputForNullness(new String[] {"bin", "load", "w"}, bin, load, new Object[] {w});
    checkInputForDuplication("load", load);
    if (card != null) {
      checkInputForNullness("card", card);
      if (card.length != load.length) {
        throw new IllegalArgumentException(
            "Constraint BinPacking has arguments load and card that are of different sizes");
      }
      Set<IntVar> others = new HashSet<>(Arrays.asList(bin));
      others.addAll(Arrays.asList(load));
      for (IntVar c : card) {
        if (others.contains(c)) {
          throw new IllegalArgumentException(
              "Constraint BinPacking has a card variable that is also a bin or load variable");
        }
      }
    }
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
    this.card = card == null ? null : Arrays.copyOf(card, card.length);
    this.sizes = new int[item.length + load.length];
    this.counts = new int[item.length + load.length];

    binMap = Var.positionMapping(load, false, this.getClass());

    Comparator<BinItem> weightComparator = (o1, o2) -> Integer.compare(o2.weight(), o1.weight());
    Arrays.sort(item, weightComparator);

    itemMap =
        Var.positionMapping(
            Arrays.stream(item).map(BinItem::bin).toArray(IntVar[]::new), false, this.getClass());

    Map<IntVar, Integer> occurrences = new HashMap<>();
    for (IntVar b : bin) {
      occurrences.merge(b, 1, Integer::sum);
    }
    this.itemCount = Arrays.stream(item).mapToInt(it -> occurrences.get(it.bin())).toArray();
    this.zeroWeightCount = Arrays.stream(zeroWeightBins).mapToInt(occurrences::get).toArray();
    this.totalCount = bin.length;
    this.unitItems = Arrays.stream(itemCount).allMatch(c -> c == 1);
    int m = load.length;
    this.packedCount = new int[m];
    this.required = new long[m];
    this.candidateCount = new int[m];
    this.candidateStart = new int[m + 1];
    this.zeroCandidates = new int[m];
    this.cardMin = new long[m];
    this.cardMax = new long[m];
    this.binCandidates = new BinItem[item.length];
    this.binCandidateWeights = new int[item.length];
    this.binOtherWeights = new int[item.length];

    // with card variables the items of weight 0 are counted, so their bins are in the scope
    Stream<Var> scope =
        Stream.concat(Arrays.stream(item).<Var>map(BinItem::bin), Arrays.stream(load));
    if (card != null) {
      scope =
          Stream.concat(scope, Stream.concat(Arrays.stream(zeroWeightBins), Arrays.stream(card)));
    }
    setScope(scope);
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
  public Binpacking(IntVar[] bin, IntVar[] load, int[] w, int minBin, boolean lbPruning) {
    this(bin, load, w, minBin, lbPruning, null);
  }

  /**
   * It constructs a binpacking constraint.
   *
   * @param bin array of variables representing bin assignment for each item.
   * @param load array of variables representing the load in each bin.
   * @param w array of weights for each item.
   * @param minBin minimum bin number to consider.
   * @param lbPruning flag indicating whether to enable lower bound pruning.
   * @param card the number of items in each bin, items of weight 0 included; null for none.
   */
  @Builder
  public Binpacking(
      IntVar[] bin, IntVar[] load, int[] w, int minBin, boolean lbPruning, IntVar[] card) {
    this(bin, load, w, minBin, card);
    this.lbPruning = lbPruning;
  }

  /**
   * It switches on the cardinality rules for a constraint without card variables: bounds on the
   * number of items of each bin derived from the loads and from the total number of items, which
   * tighten the loads and remove items from bins (Schaus et al., CP 2012).
   *
   * @param on true to use the rules.
   * @return this constraint.
   */
  public Binpacking cardinalityReasoning(boolean on) {
    this.cardinalityReasoning = on;
    return this;
  }

  /** Rule "Pack All" -- applied only on first consistency check. */
  private void applyPackAllRule(Store store) {
    if (!packAll.begin(store)) {
      return;
    }
    Arrays.stream(item)
        .map(BinItem::bin)
        .forEach(i -> i.domain.in(store.level, i, minBinNumber, load.length - 1 + minBinNumber));
    for (IntVar b : zeroWeightBins) {
      b.domain.in(store.level, b, minBinNumber, load.length - 1 + minBinNumber);
    }
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

  /** Scratch space of processBin: the candidate items of a bin and their weights. */
  private final BinItem[] binCandidates;

  private final int[] binCandidateWeights;

  private final int[] binOtherWeights;

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
      int last = b.max();
      for (int val = b.min(); val <= last; val = val < last ? b.domain.nextValue(val) : last + 1) {
        int k = val - minBinNumber;
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
    BinItem[] candidates = binCandidates;
    int[] weights = binCandidateWeights;
    int candidatesLength = 0;
    long required = 0;
    long possible = 0;
    int binIdx = i + minBinNumber;
    for (BinItem itemEl : item) {
      IntVar b = itemEl.bin();
      if (b.min() <= binIdx && b.max() >= binIdx && b.dom().contains(binIdx)) {
        possible += itemEl.weight();
        if (b.singleton()) {
          required += itemEl.weight();
        } else {
          weights[candidatesLength] = itemEl.weight();
          candidates[candidatesLength++] = itemEl;
        }
      }
    }
    load[i].domain.in(store.level, load[i], clamp(required), clamp(possible));
    applyLoadMaintenanceToCandidates(
        store, i, binIdx, required, possible, candidates, candidatesLength);
    applyTighteningBounds(store, i, required, weights, candidatesLength);
    applyEliminationAndCommitment(
        store, i, binIdx, required, candidates, weights, candidatesLength);
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

  private void applyTighteningBounds(
      Store store, int i, long required, int[] candidateWeights, int len) {
    long sumCandidates = sum(candidateWeights, len);
    if (noSum(
        candidateWeights, len, sumCandidates, load[i].min() - required, load[i].min() - required)) {
      load[i].domain.inMin(store.level, load[i], clamp(required + noSumBounds[1]));
    }
    if (noSum(
        candidateWeights, len, sumCandidates, load[i].max() - required, load[i].max() - required)) {
      load[i].domain.inMax(store.level, load[i], clamp(required + noSumBounds[0]));
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
    long sumCandidates = sum(candidateWeights, candidatesLength);
    // candidate weights without candidate j, kept in descending order; moving from j to j + 1 only
    // puts weight j back at position j
    int[] others = binOtherWeights;
    System.arraycopy(candidateWeights, 1, others, 0, candidatesLength - 1);
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
      if (todo.isEmpty() && (cardinalityReasoning || card != null)) {
        applyCardinality(store);
        if (todo.isEmpty()) {
          applyBinGroupsSometimes(store);
        }
      }
    } while (!todo.isEmpty());
    if (lbPruning) {
      if (rootLevel < 0) {
        rootLevel = store.level;
      }
      // f_CCM1 and RMax pay at the root, where they can prove infeasibility before any search;
      // during search they saved few failures for 10-30% more time per node.
      strongBinCountBound = store.level == rootLevel;
      lbNumberBins();
    }
  }

  /** Number of packed items of each bin (cardinality rules). */
  private final int[] packedCount;

  /** Weight of the packed items of each bin (cardinality rules). */
  private final long[] required;

  /** Number of candidate items of positive weight of each bin (cardinality rules). */
  private final int[] candidateCount;

  /** Start of each bin's candidates in candidates, which lists them by decreasing weight. */
  private final int[] candidateStart;

  /** Number of candidate items of weight 0 of each bin (cardinality rules). */
  private final int[] zeroCandidates;

  /** Bounds on the number of items in each bin (cardinality rules). */
  private final long[] cardMin;

  private final long[] cardMax;

  /** Indices into item of the candidates of each bin, and their prefix sums of weights. */
  private int[] candidates = new int[0];

  private long[] prefix = new long[0];

  /**
   * Cardinality reasoning for bin packing: Schaus, Régin, Van Schaeren, Dullaert and Raa, CP 2012
   * (bounds on the number of items in a bin from its load and back), the global count of items, and
   * the "too big"/"too small" rules of Derval, Régin and Schaus, Constraints 23 (2018). With card
   * variables the counts include items of weight 0; without them only the groups of items of
   * positive weight (one per bin variable) are counted, so the rules strengthen plain bin packing.
   */
  private void applyCardinality(Store store) {
    int m = load.length;
    boolean counted = card != null;
    Arrays.fill(packedCount, 0);
    Arrays.fill(required, 0);
    Arrays.fill(candidateCount, 0);
    Arrays.fill(zeroCandidates, 0);
    int entries = 0;
    for (int k = 0; k < item.length; k++) {
      IntVar b = item[k].bin();
      int c = counted ? itemCount[k] : 1;
      if (b.singleton()) {
        int j = b.value() - minBinNumber;
        packedCount[j] += c;
        required[j] += item[k].weight();
      } else {
        int last = b.max();
        for (int val = b.min();
            val <= last;
            val = val < last ? b.domain.nextValue(val) : last + 1) {
          candidateCount[val - minBinNumber]++;
          entries++;
        }
      }
    }
    if (counted) {
      for (int z = 0; z < zeroWeightBins.length; z++) {
        IntVar b = zeroWeightBins[z];
        if (b.singleton()) {
          packedCount[b.value() - minBinNumber] += zeroWeightCount[z];
        } else {
          int last = b.max();
          for (int val = b.min();
              val <= last;
              val = val < last ? b.domain.nextValue(val) : last + 1) {
            zeroCandidates[val - minBinNumber] += zeroWeightCount[z];
          }
        }
      }
    }
    if (candidates.length < entries || prefix.length < entries + m) {
      candidates = new int[entries];
      prefix = new long[entries + m];
    }
    candidateStart[0] = 0;
    for (int j = 0; j < m; j++) {
      candidateStart[j + 1] = candidateStart[j] + candidateCount[j];
      candidateCount[j] = 0;
    }
    for (int k = 0; k < item.length; k++) {
      IntVar b = item[k].bin();
      if (!b.singleton()) {
        int last = b.max();
        for (int val = b.min();
            val <= last;
            val = val < last ? b.domain.nextValue(val) : last + 1) {
          int j = val - minBinNumber;
          candidates[candidateStart[j] + candidateCount[j]++] = k;
        }
      }
    }
    // the weight-based rules count one item per candidate, so they need unit items
    boolean unit = !counted || unitItems;

    // bounds on the number of items of each bin
    long total = counted ? totalCount : item.length;
    long sumMin = 0;
    long sumMax = 0;
    for (int j = 0; j < m; j++) {
      int s = candidateStart[j];
      int n = candidateCount[j];
      long candidateItems = 0;
      long sum = 0;
      for (int t = 0; t < n; t++) {
        int k = candidates[s + t];
        candidateItems += counted ? itemCount[k] : 1;
        sum += item[k].weight();
        prefix[s + j + t + 1] = sum; // prefix of bin j starts at s + j
      }
      prefix[s + j] = 0;
      long lo = packedCount[j];
      long hi = (long) packedCount[j] + candidateItems + zeroCandidates[j];
      if (counted) {
        lo = Math.max(lo, card[j].min());
        hi = Math.min(hi, card[j].max());
      }
      if (unit) {
        // fewest items reaching the minimum load: the heaviest ones
        long r = load[j].min() - required[j];
        if (r > 0) {
          int a = 0;
          while (a < n && prefix[s + j + a] < r) {
            a++;
          }
          if (prefix[s + j + a] < r) {
            throw Store.failException;
          }
          lo = Math.max(lo, (long) packedCount[j] + a);
        }
        // most items within the maximum load: the lightest ones
        long free = load[j].max() - required[j];
        int b = 0;
        while (b < n && prefix[s + j + n] - prefix[s + j + n - b - 1] <= free) {
          b++;
        }
        hi = Math.min(hi, (long) packedCount[j] + zeroCandidates[j] + b);
      }
      if (lo > hi) {
        throw Store.failException;
      }
      cardMin[j] = lo;
      cardMax[j] = hi;
      sumMin += lo;
      sumMax += hi;
    }
    // every item is in exactly one bin
    if (sumMin > total || sumMax < total) {
      throw Store.failException;
    }
    for (int j = 0; j < m; j++) {
      long lo = Math.max(cardMin[j], total - (sumMax - cardMax[j]));
      long hi = Math.min(cardMax[j], total - (sumMin - cardMin[j]));
      if (counted) {
        card[j].domain.in(store.level, card[j], clamp(lo), clamp(hi));
        lo = Math.max(lo, card[j].min());
        hi = Math.min(hi, card[j].max());
      }
      cardMin[j] = lo;
      cardMax[j] = hi;
    }
    for (int j = 0; j < m; j++) {
      applyCardinalityToBin(store, j, unit);
    }
  }

  private void applyCardinalityToBin(Store store, int j, boolean unit) {
    boolean counted = card != null;
    int s = candidateStart[j];
    int n = candidateCount[j];
    int p = s + j; // prefix sums of bin j
    int binIdx = j + minBinNumber;
    long lo = cardMin[j];
    long hi = cardMax[j];
    long packed = packedCount[j];
    long all = packed + zeroCandidates[j];
    for (int t = 0; t < n; t++) {
      all += counted ? itemCount[candidates[s + t]] : 1;
    }
    // counts alone: a bin at its largest count takes no more items, a bin that needs all its
    // candidates takes them
    if (packed >= hi || all <= lo) {
      boolean in = packed < hi;
      for (int t = 0; t < n; t++) {
        IntVar b = item[candidates[s + t]].bin();
        if (in) {
          assignBin(store, b, binIdx);
        } else {
          removeBin(store, b, binIdx);
        }
      }
      if (counted) {
        for (IntVar b : zeroWeightBins) {
          if (!b.singleton() && b.domain.contains(binIdx)) {
            if (in) {
              assignBin(store, b, binIdx);
            } else {
              removeBin(store, b, binIdx);
            }
          }
        }
      }
      return;
    }
    if (counted && !unit) {
      for (int t = 0; t < n; t++) {
        int c = itemCount[candidates[s + t]];
        IntVar b = item[candidates[s + t]].bin();
        if (packed + c > hi) {
          removeBin(store, b, binIdx);
        } else if (all - c < lo) {
          assignBin(store, b, binIdx);
        }
      }
      return;
    }
    long minLoad = load[j].min();
    long maxLoad = load[j].max();
    long req = required[j];
    // load bounds from the count bounds: the lightest and the heaviest candidates
    long need = lo - packed - zeroCandidates[j];
    if (need > 0) {
      long lightest = prefix[p + n] - prefix[p + n - (int) need];
      if (req + lightest > minLoad) {
        minLoad = req + lightest;
        load[j].domain.inMin(store.level, load[j], clamp(minLoad));
        todo.set(j);
      }
    }
    long most = hi - packed;
    if (most < n) {
      long heaviest = prefix[p + (int) most];
      if (req + heaviest < maxLoad) {
        maxLoad = req + heaviest;
        load[j].domain.inMax(store.level, load[j], clamp(maxLoad));
        todo.set(j);
      }
    }
    // too big and too small (Derval, Régin and Schaus 2018): with the item, the bin needs at least
    // lo - packed - 1 and takes at most hi - packed - 1 other items
    long others = lo - packed - 1 - zeroCandidates[j];
    int h = (int) Math.min(hi - packed - 1, n - 1L);
    for (int t = 0; t < n; t++) {
      int k = candidates[s + t];
      long w = item[k].weight();
      if (others > 0) {
        int o = (int) others;
        // the o lightest candidates other than t
        long light =
            t >= n - o
                ? prefix[p + n] - prefix[p + n - o - 1] - w
                : prefix[p + n] - prefix[p + n - o];
        if (req + w + light > maxLoad) {
          removeBin(store, item[k].bin(), binIdx);
          continue;
        }
      }
      // the h heaviest candidates other than t
      long heavy = t < h ? prefix[p + h + 1] - w : prefix[p + h];
      if (req + w + heavy < minLoad) {
        removeBin(store, item[k].bin(), binIdx);
      }
    }
  }

  /** The most items times bin groups that the group rules look at in one call. */
  private static final int GROUP_WORK_LIMIT = 1 << 16;

  /** Indices into item of the candidates of the current bin group, by increasing weight. */
  private int[] groupCandidates = new int[0];

  /** The smallest and the largest bin of each item when the group rules start. */
  private int[] groupMin = new int[0];

  private int[] groupMax = new int[0];

  /** The most calls the group rules skip after calls that pruned nothing. */
  private static final int GROUP_MAX_SKIP = 63;

  /** Calls of the group rules still to skip, and how many to skip after the next idle call. */
  private int groupPending;

  private int groupSkip;

  /**
   * Runs the group rules, but after calls that pruned nothing it skips the next calls, twice as
   * many each time up to GROUP_MAX_SKIP, until a call prunes again. On models where they hardly
   * ever prune (gbac) they cost a quarter of the time; where they prune they run at every call.
   */
  private void applyBinGroupsSometimes(Store store) {
    if (groupPending > 0) {
      groupPending--;
      return;
    }
    boolean pruned;
    try {
      applyBinGroups(store);
      pruned = !todo.isEmpty();
    } catch (FailException e) {
      groupSkip = 0;
      throw e;
    }
    groupSkip = pruned ? 0 : Math.min(2 * groupSkip + 1, GROUP_MAX_SKIP);
    groupPending = groupSkip;
  }

  /**
   * The cardinality rules on groups of consecutive bins: the items whose bins all lie in the group
   * are packed in it, the others that can use it are its candidates, and its count and load bounds
   * are the sums of those of its bins. So a group that needs more items than its packed ones fails
   * when even its lightest candidates overload it, as for one bin, although each bin on its own can
   * still be filled. Groups of consecutive bins suit models whose bins are ordered, such as periods
   * with precedences. The rules need one count per item, as the weight-based rules of one bin.
   */
  private void applyBinGroups(Store store) {
    int m = load.length;
    boolean counted = card != null;
    if (m < 3 || counted && (!unitItems || zeroWeightBins.length > 0)) {
      return;
    }
    int n = item.length;
    // longest group within the work limit; whole groups of m bins are the global count
    int longest = (int) Math.min(m - 1L, Math.max(1L, (long) GROUP_WORK_LIMIT / ((long) n * m)));
    if (longest < 2) {
      return;
    }
    if (groupCandidates.length < n) {
      groupCandidates = new int[n];
      groupMin = new int[n];
      groupMax = new int[n];
    }
    // the bounds of the items when the call starts; the domains pruned since are subsets of them,
    // so the rules stay sound on these, only weaker
    for (int k = 0; k < n; k++) {
      IntVar v = item[k].bin();
      groupMin[k] = v.min();
      groupMax[k] = v.max();
    }
    long total = counted ? totalCount : n;
    long allMin = 0;
    long allMax = 0;
    for (int j = 0; j < m; j++) {
      allMin += cardMin[j];
      allMax += cardMax[j];
    }
    for (int a = 0; a < m; a++) {
      long loadMin = load[a].min();
      long loadMax = load[a].max();
      long countMin = cardMin[a];
      long countMax = cardMax[a];
      for (int b = a + 1; b < m && b - a < longest; b++) {
        loadMin += load[b].min();
        loadMax += load[b].max();
        countMin += cardMin[b];
        countMax += cardMax[b];
        long lo = Math.max(countMin, total - (allMax - countMax));
        long hi = Math.min(countMax, total - (allMin - countMin));
        applyBinGroup(store, a, b, lo, hi, loadMin, loadMax);
      }
    }
  }

  /** The cardinality rules on the group of bins a..b, with its count and load bounds. */
  private void applyBinGroup(
      Store store, int a, int b, long countMin, long countMax, long loadMin, long loadMax) {
    int first = a + minBinNumber;
    int last = b + minBinNumber;
    long packed = 0;
    long weight = 0;
    int c = 0;
    long candidateWeight = 0;
    int[] lo = groupMin;
    int[] hi = groupMax;
    for (int k = item.length - 1; k >= 0; k--) {
      if (hi[k] < first || lo[k] > last) {
        continue;
      }
      if (lo[k] >= first && hi[k] <= last) {
        packed++;
        weight += item[k].weight();
      } else if (item[k].bin().domain.isIntersecting(first, last)) {
        groupCandidates[c++] = k;
        candidateWeight += item[k].weight();
      }
    }
    if (packed > countMax || packed + c < countMin || weight > loadMax) {
      throw Store.failException;
    }
    if (weight + candidateWeight < loadMin) {
      throw Store.failException;
    }
    if (c == 0) {
      return;
    }
    // too small: the group needs at least need more items, the lightest candidates first
    long need = countMin - packed;
    long light = 0;
    for (int t = 0; t < need; t++) {
      light += item[groupCandidates[t]].weight();
    }
    if (weight + light > loadMax) {
      throw Store.failException;
    }
    // too big: the group takes at most most more items, the heaviest candidates first
    int most = (int) Math.min(c, countMax - packed);
    long heavy = 0;
    for (int t = c - most; t < c; t++) {
      heavy += item[groupCandidates[t]].weight();
    }
    if (weight + heavy < loadMin) {
      throw Store.failException;
    }
    if (packed == countMax || packed + c == countMin) {
      // counts alone: the group takes no more items, or needs all its candidates
      boolean in = packed < countMax;
      for (int t = 0; t < c; t++) {
        if (in) {
          assignGroup(store, groupCandidates[t], first, last);
        } else {
          removeGroup(store, groupCandidates[t], first, last);
        }
      }
      return;
    }
    if (need > 0) {
      // a candidate heavier than the lightest need ones replaces the heaviest of them
      long base = weight + light - item[groupCandidates[(int) need - 1]].weight();
      for (int t = c - 1; t >= need; t--) {
        int k = groupCandidates[t];
        if (base + item[k].weight() <= loadMax) {
          break;
        }
        removeGroup(store, k, first, last);
      }
    }
    if (most < c) {
      // a candidate left out of the heaviest most ones is replaced by the next heaviest
      long base = weight + heavy + item[groupCandidates[c - most - 1]].weight();
      for (int t = c - 1; t >= c - most; t--) {
        int k = groupCandidates[t];
        if (base - item[k].weight() >= loadMin) {
          break;
        }
        assignGroup(store, k, first, last);
      }
    }
    // the loads of the group sum to at least weight + light and at most weight + heavy
    for (int j = a; j <= b; j++) {
      IntVar l = load[j];
      long othersMax = loadMax - l.max();
      long othersMin = loadMin - l.min();
      int min = l.min();
      int max = l.max();
      l.domain.in(
          store.level, l, clamp(weight + light - othersMax), clamp(weight + heavy - othersMin));
      if (l.min() != min || l.max() != max) {
        todo.set(j);
      }
    }
  }

  /** Removes the bins first..last from item k and schedules them and its remaining bin. */
  private void removeGroup(Store store, int k, int first, int last) {
    IntVar v = item[k].bin();
    if (!v.domain.isIntersecting(first, last)) {
      return;
    }
    for (int i = Math.max(first, v.min()); i <= Math.min(last, v.max()); i++) {
      todo.set(i - minBinNumber);
    }
    v.domain.inComplement(store.level, v, first, last);
    groupMin[k] = v.min();
    groupMax[k] = v.max();
    if (v.singleton()) {
      int j = v.value() - minBinNumber;
      if (j >= 0 && j < load.length) {
        todo.set(j);
      }
    }
  }

  /** Restricts item k to the bins first..last and schedules every bin it could be in before. */
  private void assignGroup(Store store, int k, int first, int last) {
    IntVar v = item[k].bin();
    if (v.min() >= first && v.max() <= last) {
      return;
    }
    int max = v.max();
    for (int val = v.min(); val <= max; val = val < max ? v.domain.nextValue(val) : max + 1) {
      int j = val - minBinNumber;
      if (j >= 0 && j < load.length) {
        todo.set(j);
      }
    }
    v.domain.in(store.level, v, first, last);
    groupMin[k] = v.min();
    groupMax[k] = v.max();
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
    int nb = Math.max(0, last - first + 1);
    int[] packed = new int[nb];
    int[] capacity = new int[nb];
    for (int i = 0; i < nb; i++) {
      packed[i] = a[first + i];
      capacity[i] = load[first + i].max();
    }
    if (binCountFails(
        unpacked, unpackedLength, packed, capacity, strongBinCountBound, sizes, counts)) {
      throw Store.failException;
    }
  }

  /**
   * Tells whether the bin-count bounds show that the unpacked items (in descending order) do not
   * fit into the bins whose largest loads are {@code capacity} and which already hold {@code
   * packed}.
   *
   * @param unpacked the weights of the unpacked items, in descending order
   * @param unpackedLength the number of unpacked items, at least 1
   * @param packed the weight already packed in each bin the unpacked items can use
   * @param capacity the largest load of each of those bins
   * @param strong true to use also f_CCM1 and reduction RMax
   * @param sizes scratch space of at least unpackedLength + capacity.length entries
   * @param counts scratch space of at least unpackedLength + capacity.length entries
   * @return true when the items need more bins than there are
   */
  static boolean binCountFails(
      int[] unpacked,
      int unpackedLength,
      int[] packed,
      int[] capacity,
      boolean strong,
      int[] sizes,
      int[] counts) {
    int nb = capacity.length;

    // Reduction R0 (Shaw 2004): the capacity is the largest bin capacity and every bin that items
    // can still use gets one virtual item made of the items already packed in it and the capacity
    // it lacks compared to the largest bin.
    int maxCapacity = 0;
    for (int c : capacity) {
      maxCapacity = Math.max(maxCapacity, c);
    }
    if (maxCapacity <= 0) {
      return true; // unpacked items of positive weight and no capacity
    }
    int[] virtual = new int[nb];
    for (int i = 0; i < nb; i++) {
      virtual[i] = maxCapacity - (capacity[i] - packed[i]);
    }
    Arrays.sort(virtual);
    int minVirtual = virtual[0];

    // A packing found by first fit decreasing shows that no bound can exceed nb.
    if (fitsFirstFitDecreasing(unpacked, unpackedLength, virtual, maxCapacity)) {
      return false;
    }

    // Any reduction R(delta) that adds delta to the capacity and to every virtual item keeps the
    // packings feasible (every bin holds exactly one virtual item), so each gives a valid bound
    // (Dupuis, Schaus and Deville 2010). Neither of R0, RMin and RMax dominates the others.
    if (lbBins(unpacked, unpackedLength, virtual, 0, maxCapacity, nb, strong, sizes, counts)) {
      return true;
    }
    // RMin: the smallest virtual item becomes empty, i.e. the capacity is the largest free space.
    if (minVirtual > 0
        && minVirtual < maxCapacity
        && lbBins(
            unpacked,
            unpackedLength,
            virtual,
            -minVirtual,
            maxCapacity - minVirtual,
            nb,
            strong,
            sizes,
            counts)) {
      return true;
    }
    // RMax: every virtual item becomes larger than half the capacity.
    long deltaMax = (long) maxCapacity - 2L * minVirtual + 1;
    return strong
        && deltaMax != 0
        && maxCapacity + deltaMax <= IntDomain.MAX_INT
        && lbBins(
            unpacked,
            unpackedLength,
            virtual,
            (int) deltaMax,
            (int) (maxCapacity + deltaMax),
            nb,
            true,
            sizes,
            counts);
  }

  /**
   * Returns true if first fit packs the unpacked items (in descending order) into the free space of
   * the bins, capacity minus their virtual item.
   */
  private static boolean fitsFirstFitDecreasing(
      int[] unpacked, int unpackedLength, int[] virtual, int capacity) {
    int[] free = new int[virtual.length];
    for (int i = 0; i < free.length; i++) {
      free[i] = capacity - virtual[i];
    }
    for (int k = 0; k < unpackedLength; k++) {
      int w = unpacked[k];
      int b = 0;
      while (b < free.length && free[b] < w) {
        b++;
      }
      if (b == free.length) {
        return false;
      }
      free[b] -= w;
    }
    return true;
  }

  /**
   * Tells whether the bin-count bounds on the unpacked items plus the virtual items (ascending)
   * shifted by delta, with the given capacity, exceed nb.
   */
  private static boolean lbBins(
      int[] unpacked,
      int unpackedLength,
      int[] virtual,
      int delta,
      int capacity,
      int nb,
      boolean strong,
      int[] sizes,
      int[] counts) {
    int[] v = new int[virtual.length];
    for (int i = 0; i < v.length; i++) {
      v[i] = virtual[i] + delta;
    }
    int[] x = merge(unpacked, unpackedLength, v);
    if (x[0] > capacity) {
      return true; // an item fits in no bin
    }
    return lbBins(x, capacity, nb) || strong && ccm1Fails(x, capacity, nb, sizes, counts);
  }

  /**
   * Tells whether the dual feasible function f_CCM1 of Carlier, Clautiaux and Moukrim (2007) shows
   * that the items x (in descending order) need more than nb bins of the given capacity. A dual
   * feasible function maps the sizes so that items fitting together in a bin still fit after the
   * mapping, so ceil(sum f(x) / f(capacity)) is a lower bound. Its parameter lambda (1 to capacity
   * / 2) is tried at the distinct item sizes, as for L2.
   */
  private static boolean ccm1Fails(int[] x, int capacity, int nb, int[] sizes, int[] counts) {
    int half = capacity / 2;
    if (half == 0) {
      return false;
    }
    // distinct sizes with their multiplicities
    int d = 0;
    for (int i = 0; i < x.length; i++) {
      if (d > 0 && sizes[d - 1] == x[i]) {
        counts[d - 1]++;
      } else {
        sizes[d] = x[i];
        counts[d] = 1;
        d++;
      }
    }
    for (int j = d - 1; j >= 0 && sizes[j] <= half; j--) {
      int lambda = sizes[j];
      if (lambda == 0) {
        continue;
      }
      long capacityLambda = capacity / lambda;
      long sum = 0;
      // sizes below lambda map to 0
      for (int i = 0; i < d && sizes[i] >= lambda; i++) {
        int w = sizes[i];
        long f;
        if (w > capacity - w) {
          f = 2 * (capacityLambda - (capacity - w) / lambda);
        } else if (w == capacity - w) {
          f = capacityLambda;
        } else {
          f = 2L * (w / lambda);
        }
        sum += f * counts[i];
      }
      // ceil(sum / f(capacity)) > nb, with f(capacity) = 2 * capacityLambda
      if (sum > 2 * capacityLambda * nb) {
        return true;
      }
    }
    return false;
  }

  private static int[] merge(int[] a, int arrLength, int[] b) {
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
    } else if (binMap.containsKey(v)) {
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
    return noSum(x, len, sumX, alpha, beta, noSumBounds);
  }

  /**
   * NoSum of Shaw (2004): tells whether no subset of the first len weights of x, sorted in
   * descending order and summing to sumX, sums to a value in [alpha, beta]. It stores in bounds the
   * largest such sum below alpha and the smallest above beta that it found.
   */
  static boolean noSum(int[] x, int len, long sumX, long alpha, long beta, long[] bounds) {

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

    bounds[0] = sumA + sumC;
    bounds[1] = sumB;

    return sumA < alpha;
  }

  private static long sum(int[] x) {
    return sum(x, x.length);
  }

  private static long sum(int[] x, int len) {
    long summa = 0;
    for (int i = 0; i < len; i++) {
      summa += x[i];
    }
    return summa;
  }

  /** Tells whether the bounds L1 and L2 of Martello and Toth exceed nb. */
  private static boolean lbBins(int[] x, int capacity, int nb) {
    int nn = x.length;
    long sum = sum(x);
    long lb = sum / capacity + (sum % capacity != 0 ? 1 : 0);

    if (nb < lb) {
      return true;
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
    return nb < lb;
  }

  private static long computeLbForK(int[] x, int nn, int capacity, int k) {
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

  /**
   * Explains a pruning by the packed, candidate and excluded items of the bins and the bounds of
   * the loads; see {@link BinpackingExplanation}.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    BinpackingExplanation e = explanation();
    return e != null && e.explain(trail, entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    BinpackingExplanation e = explanation();
    return e != null && e.explainFailure(trail, out);
  }

  // null when a bin variable is also a load, which the explanations do not handle
  private BinpackingExplanation explanation() {
    if (explanation == null) {
      IntVar[] bins = Arrays.stream(item).map(BinItem::bin).toArray(IntVar[]::new);
      for (IntVar b : Stream.concat(Arrays.stream(bins), Arrays.stream(zeroWeightBins)).toList()) {
        if (binMap.containsKey(b)) {
          return null;
        }
      }
      explanation =
          new BinpackingExplanation(
              bins,
              Arrays.stream(item).mapToInt(BinItem::weight).toArray(),
              load,
              itemMap,
              binMap,
              zeroWeightBins,
              minBinNumber);
      boolean counted = card != null;
      if ((counted || cardinalityReasoning) && COUNT_EXPLANATIONS) {
        int m = load.length;
        boolean groups = m >= 3 && !(counted && (!unitItems || zeroWeightBins.length > 0));
        int longest =
            (int)
                Math.min(
                    m - 1L,
                    Math.max(1L, (long) GROUP_WORK_LIMIT / Math.max(1L, (long) item.length * m)));
        int[] ones = new int[item.length];
        Arrays.fill(ones, 1);
        explanation.counting(
            card,
            counted ? itemCount : ones,
            counted ? zeroWeightBins : new IntVar[0],
            counted ? zeroWeightCount : new int[0],
            counted ? totalCount : item.length,
            !counted || unitItems,
            groups ? longest : 1);
      }
    }
    return explanation;
  }

  @Override
  public Binpacking copy(VarMap map) {
    if (card != null) {
      // every item again, so that the copy counts the same items
      IntVar[] bins = new IntVar[totalCount];
      int[] w = new int[totalCount];
      int n = 0;
      for (int i = 0; i < item.length; i++) {
        for (int c = 0; c < itemCount[i]; c++) {
          bins[n] = map.get(item[i].bin());
          w[n++] = c == 0 ? item[i].weight() : 0;
        }
      }
      for (int z = 0; z < zeroWeightBins.length; z++) {
        for (int c = 0; c < zeroWeightCount[z]; c++) {
          bins[n++] = map.get(zeroWeightBins[z]);
        }
      }
      return new Binpacking(bins, map.get(load), w, minBinNumber, lbPruning, map.get(card));
    }
    IntVar[] bins = new IntVar[item.length];
    int[] w = new int[item.length];
    for (int i = 0; i < item.length; i++) {
      bins[i] = map.get(item[i].bin());
      w[i] = item[i].weight();
    }
    Binpacking copy = new Binpacking(bins, map.get(load), w, minBinNumber, lbPruning);
    copy.cardinalityReasoning = cardinalityReasoning;
    return copy;
  }

  /** Bins of items of weight 0 are restricted by the first consistency; they are not arguments. */
  @Override
  public boolean canCopy() {
    return card != null || zeroWeightBins.length == 0 || !packAll.due();
  }

  /**
   * Returns the row that every item is in some bin: the loads add up to the weight of all items.
   *
   * @return the row
   */
  @Override
  public List<LinearForm> relaxation() {
    long[] ones = new long[load.length];
    Arrays.fill(ones, 1);
    return List.of(new LinearForm(load.clone(), ones, sizeAllItems, LinearForm.EQ));
  }
}
