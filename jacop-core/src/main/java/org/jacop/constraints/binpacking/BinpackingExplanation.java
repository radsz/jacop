/*
 * BinpackingExplanation.java
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of {@link Binpacking} for lazy clause generation.
 *
 * <p>Every explanation is rebuilt from the domains just before the atom it explains, so it does not
 * depend on which rule pruned: each removed value or bound is proven by the first of these rules
 * that holds, and the atom is left to the generic reason when none does.
 *
 * <ul>
 *   <li>a bin's load is at least the weight of a few items packed in it (the largest first), and at
 *       most the weight of the items not excluded from it (the largest excluded items first);
 *   <li>the loads sum to the weight of all items, so the bounds of the other loads bound a load,
 *       and a failure when the only loads they leave are holes;
 *   <li>an item is not in a bin when it would overload it with a few packed items, or when another
 *       bin cannot reach its smallest load without it;
 *   <li>otherwise the loads a bin can take are its packed weight plus the subset sums of its
 *       candidate items. They are computed exactly by a bitset when the sums are small, and by the
 *       NoSum of Shaw (2004) otherwise; the reason is the packed and excluded items and the bounds
 *       and holes of the load that the reachable sums hit. Excluded items too heavy to reach the
 *       values explained are left out of it;
 *   <li>a failure of the bin-count bound is explained by the bounds of the item variables and the
 *       largest loads of the bins, after dropping the items that the bound does not need. *
 *   <li>with the cardinality rules (card variables, or {@link Binpacking#cardinalityReasoning}),
 *       the number of items of a bin, or of a group of consecutive bins, is bounded by its card
 *       variables, its packed items, the items not excluded from it, the fewest heaviest or most
 *       lightest items its loads allow (one count per item), and the bounds of the other bins
 *       against the number of items. These bounds explain the bounds of the card variables, an item
 *       kept out of a group that is full or that it would overload or underload with the lightest
 *       or heaviest items the count needs, an item needed by a group that cannot reach its count or
 *       load without it, the loads from the lightest or heaviest items of the count, and a count
 *       bound above the other.
 * </ul>
 *
 * <p>The packed items of a bin and the candidate set (as packed plus excluded items) follow M. de
 * Kloe, "Lazy Clause Generation for Bin Packing", TU Delft (2025); exact subset sums with holes,
 * the heavy-item and bin-count reductions and commitment through another bin are additions.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class BinpackingExplanation {

  /** The largest sum the exact subset sums are computed up to; above it NoSum is used. */
  private static final int SUBSET_SUM_LIMIT = 1 << 16;

  /** The most items the bin-count explanation tries to drop one by one. */
  private static final int SHRINK_LIMIT = 128;

  /** The most holes of a load that the failure by the other loads goes through. */
  private static final int HOLE_LIMIT = 1024;

  private static final byte FIXED = 1;
  private static final byte CANDIDATE = 2;
  private static final byte EXCLUDED = 3;

  private final IntVar[] bins; // per item, by descending weight
  private final int[] weights;
  private final IntVar[] load;
  private final Map<IntVar, Integer> itemMap;
  private final Map<IntVar, Integer> binMap;
  private final IntVar[] zeroWeightBins;
  private final int minBin;
  private final long sizeAll;

  // the domains just before the position being explained
  private AtomicTrail trail;
  private int position;
  private final int[] itemMin;
  private final int[] itemMax;
  private final byte[][] status; // per bin and item, computed when first asked; 0 when not yet
  private final EntryList scratch = new EntryList();
  private final long[] bounds = new long[2];

  // the cardinality rules, set by counting(); off while card is null and counts is false
  private boolean counts;
  private IntVar[] card;
  private Map<IntVar, Integer> cardMap = Map.of();
  private int[] itemCount; // per item, the number of items it stands for
  private IntVar[] zeroBins = new IntVar[0]; // the items of weight 0 that are counted
  private int[] zeroCount = new int[0];
  private long totalCount;
  private boolean unit; // every item of positive weight counts once: the weight-based rules hold
  private int groupWidth = 1; // the widest group of consecutive bins the rules look at
  private int[] zeroMin;
  private int[] zeroMax;
  private byte[][] zeroStatus;
  private long[] binLo;
  private long[] binHi;
  private byte[] binLoSource;
  private byte[] binHiSource;
  private boolean[] binBounds; // binLo and binHi are computed for the snapshot
  private Scan ruleScan;
  private Scan boundScan;
  private Scan binScan;

  BinpackingExplanation(
      IntVar[] bins,
      int[] weights,
      IntVar[] load,
      Map<IntVar, Integer> itemMap,
      Map<IntVar, Integer> binMap,
      IntVar[] zeroWeightBins,
      int minBin) {
    this.bins = bins;
    this.weights = weights;
    this.load = load;
    this.itemMap = itemMap;
    this.binMap = binMap;
    this.zeroWeightBins = zeroWeightBins;
    this.minBin = minBin;
    long s = 0;
    for (int w : weights) {
      s += w;
    }
    this.sizeAll = s;
    this.itemMin = new int[bins.length];
    this.itemMax = new int[bins.length];
    this.status = new byte[load.length][];
  }

  private void snapshot(AtomicTrail trail, int position) {
    this.trail = trail;
    this.position = position;
    int n = bins.length;
    for (int k = 0; k < n; k++) {
      itemMin[k] = trail.minBefore(bins[k], position);
      itemMax[k] = trail.maxBefore(bins[k], position);
    }
    for (byte[] s : status) {
      if (s != null) {
        Arrays.fill(s, (byte) 0);
      }
    }
    if (counts) {
      for (int z = 0; z < zeroBins.length; z++) {
        zeroMin[z] = trail.minBefore(zeroBins[z], position);
        zeroMax[z] = trail.maxBefore(zeroBins[z], position);
      }
      for (byte[] s : zeroStatus) {
        if (s != null) {
          Arrays.fill(s, (byte) 0);
        }
      }
      Arrays.fill(binBounds, false);
    }
  }

  // whether item k was packed in, a candidate of, or excluded from bin i
  private byte status(int i, int k) {
    byte[] s = status[i];
    if (s == null) {
      s = new byte[bins.length];
      status[i] = s;
    }
    if (s[k] == 0) {
      int b = i + minBin;
      if (itemMin[k] == b && itemMax[k] == b) {
        s[k] = FIXED;
      } else if (b < itemMin[k] || b > itemMax[k] || excluded(bins[k], b)) {
        s[k] = EXCLUDED;
      } else {
        s[k] = CANDIDATE;
      }
    }
    return s[k];
  }

  private boolean excluded(IntVar x, long v) {
    if (v < Integer.MIN_VALUE || v > Integer.MAX_VALUE) {
      return true;
    }
    scratch.clear();
    return trail.excludedBefore(x, (int) v, position, scratch);
  }

  private void addPacked(int k, EntryList out) {
    trail.addLowerBound(bins[k], position, out);
    trail.addUpperBound(bins[k], position, out);
  }

  private void addExcluded(int i, int k, EntryList out) {
    trail.excludedBefore(bins[k], i + minBin, position, out);
  }

  /** Explains an atom; see {@link org.jacop.lcg.Explainable#explain}. */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar x = trail.variable(entry);
    int kind = trail.kind(entry);
    int v = trail.value(entry);
    snapshot(trail, entry);
    Integer i = binMap.get(x);
    if (i != null) {
      return switch (kind) {
        case AtomicTrail.GE -> loadAtLeast(i, v, out);
        case AtomicTrail.LE -> loadAtMost(i, v, out);
        default -> false;
      };
    }
    Integer c = cardMap.get(x);
    if (c != null) {
      return switch (kind) {
        case AtomicTrail.GE -> cardAtLeast(c, v, out);
        case AtomicTrail.LE -> cardAtMost(c, v, out);
        default -> false;
      };
    }
    Integer j = itemMap.get(x);
    if (j == null && !isZeroWeightBin(x)) {
      return false;
    }
    int k = j == null ? zeroItem(x) : j;
    int lastBin = minBin + load.length - 1;
    switch (kind) {
      case AtomicTrail.GE -> {
        int m = trail.minBefore(x, entry);
        if (m > minBin) {
          trail.addLowerBound(x, entry, out); // the bins below m
        }
        for (long u = Math.max(minBin, m); u < v && u <= lastBin; u++) {
          if (!notIn(k, x, (int) u, out)) {
            return false;
          }
        }
        return true;
      }
      case AtomicTrail.LE -> {
        int m = trail.maxBefore(x, entry);
        if (m < lastBin) {
          trail.addUpperBound(x, entry, out); // the bins above m
        }
        for (long u = Math.min(lastBin, m); u > v && u >= minBin; u--) {
          if (!notIn(k, x, (int) u, out)) {
            return false;
          }
        }
        return true;
      }
      default -> {
        return notIn(k, x, v, out);
      }
    }
  }

  // the code of a counted item of weight 0 (see zeroSkip), or -1
  private int zeroItem(IntVar x) {
    for (int z = 0; z < zeroBins.length; z++) {
      if (zeroBins[z] == x) {
        return -2 - z;
      }
    }
    return -1;
  }

  private boolean isZeroWeightBin(IntVar x) {
    for (IntVar b : zeroWeightBins) {
      if (b == x) {
        return true;
      }
    }
    return false;
  }

  /** Explains a failure; see {@link org.jacop.lcg.Explainable#explainFailure}. */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    snapshot(trail, trail.size());
    for (int i = 0; i < load.length; i++) {
      if (overloaded(i, -1, 0, out) || underloaded(i, -1, 0, out)) {
        return true;
      }
    }
    long sumMax = 0;
    long sumMin = 0;
    for (IntVar l : load) {
      sumMax += trail.maxBefore(l, position);
      sumMin += trail.minBefore(l, position);
    }
    if (sumMax < sizeAll || sumMin > sizeAll) {
      for (IntVar l : load) {
        if (sumMax < sizeAll) {
          trail.addUpperBound(l, position, out);
        } else {
          trail.addLowerBound(l, position, out);
        }
      }
      return true;
    }
    for (int i = 0; i < load.length; i++) {
      if (othersLeaveHole(i, sumMin, sumMax, out)) {
        return true;
      }
    }
    if (counts && countFailure(out)) {
      return true;
    }
    for (int i = 0; i < load.length; i++) {
      if (loadValues(i, -1, 0, Long.MIN_VALUE, Long.MAX_VALUE, out)) {
        return true;
      }
    }
    for (int k = 0; k < bins.length; k++) {
      int mark = out.size();
      boolean wipedOut = true;
      for (int u = minBin; u < minBin + load.length && wipedOut; u++) {
        wipedOut = notIn(k, bins[k], u, out);
      }
      if (wipedOut) {
        return true;
      }
      out.truncate(mark);
    }
    return binCount(out);
  }

  // the load of bin i is at least v: from packed items, or the other loads, then the holes of the
  // load just below v; else from the loads its items can reach
  private boolean loadAtLeast(int i, int v, EntryList out) {
    IntVar l = load[i];
    int m = trail.minBefore(l, position);
    long b = v;
    while (b - 1 > m && excluded(l, b - 1)) {
      b--;
    }
    if (packedAtLeast(i, -1, 0, b, out)
        || othersAtMost(i, b, out)
        || counts && countLoadAtLeast(i, b, false, out)) {
      for (long t = b; t < v; t++) {
        trail.excludedBefore(l, (int) t, position, out);
      }
      return true;
    }
    if (loadValues(i, -1, 0, Long.MIN_VALUE, v - 1L, out)) {
      return true;
    }
    if (counts && groupWidth > 1 && countLoadAtLeast(i, b, true, out)) {
      for (long t = b; t < v; t++) {
        trail.excludedBefore(l, (int) t, position, out);
      }
      return true;
    }
    return false;
  }

  private boolean loadAtMost(int i, int v, EntryList out) {
    IntVar l = load[i];
    int m = trail.maxBefore(l, position);
    long b = v;
    while (b + 1 < m && excluded(l, b + 1)) {
      b++;
    }
    if (possibleAtMost(i, -1, 0, b, out)
        || othersAtLeast(i, b, out)
        || counts && countLoadAtMost(i, b, false, out)) {
      for (long t = v + 1L; t <= b; t++) {
        trail.excludedBefore(l, (int) t, position, out);
      }
      return true;
    }
    if (loadValues(i, -1, 0, v + 1L, Long.MAX_VALUE, out)) {
      return true;
    }
    if (counts && groupWidth > 1 && countLoadAtMost(i, b, true, out)) {
      for (long t = v + 1L; t <= b; t++) {
        trail.excludedBefore(l, (int) t, position, out);
      }
      return true;
    }
    return false;
  }

  // the other loads at their largest leave at least b for load i
  private boolean othersAtMost(int i, long b, EntryList out) {
    long rest = sizeAll;
    for (int k = 0; k < load.length; k++) {
      if (k != i) {
        rest -= trail.maxBefore(load[k], position);
      }
    }
    if (rest < b) {
      return false;
    }
    for (int k = 0; k < load.length; k++) {
      if (k != i) {
        trail.addUpperBound(load[k], position, out);
      }
    }
    return true;
  }

  private boolean othersAtLeast(int i, long b, EntryList out) {
    long rest = sizeAll;
    for (int k = 0; k < load.length; k++) {
      if (k != i) {
        rest -= trail.minBefore(load[k], position);
      }
    }
    if (rest > b) {
      return false;
    }
    for (int k = 0; k < load.length; k++) {
      if (k != i) {
        trail.addLowerBound(load[k], position, out);
      }
    }
    return true;
  }

  // the other loads leave load i only values in [sizeAll - their maxima, sizeAll - their minima],
  // and those are holes of load i
  private boolean othersLeaveHole(int i, long sumMin, long sumMax, EntryList out) {
    IntVar l = load[i];
    int lmin = trail.minBefore(l, position);
    int lmax = trail.maxBefore(l, position);
    long from = sizeAll - (sumMax - lmax);
    long to = sizeAll - (sumMin - lmin);
    long a = Math.max(from, lmin);
    long b = Math.min(to, lmax);
    if (a > b || b - a >= HOLE_LIMIT) {
      return false;
    }
    for (long t = a; t <= b; t++) {
      if (!excluded(l, t)) {
        return false;
      }
    }
    for (long t = a; t <= b; t++) {
      trail.excludedBefore(l, (int) t, position, out);
    }
    if (from < lmin) {
      trail.addLowerBound(l, position, out);
    }
    if (to > lmax) {
      trail.addUpperBound(l, position, out);
    }
    for (int k = 0; k < load.length; k++) {
      if (k != i) {
        trail.addUpperBound(load[k], position, out);
        trail.addLowerBound(load[k], position, out);
      }
    }
    return true;
  }

  /**
   * Explains that item k, whose bin variable is x, is not in bin u: x excludes it, or u is not a
   * bin, or k in u would overload or underload u, or another bin needs k, or the counts of the bins
   * (or groups of bins) rule it out. An item of weight 0 has k below -1 (see zeroSkip) and only the
   * counts apply to it.
   */
  private boolean notIn(int k, IntVar x, int u, EntryList out) {
    if (u < minBin || u >= minBin + load.length) {
      return true;
    }
    if (trail.excludedBefore(x, u, position, out)) {
      return true;
    }
    int i = u - minBin;
    if (k < 0) {
      int z = zeroSkip(k);
      return z >= 0
          && (countNotIn(i, k, zeroCount[z], 0, false, out)
              || groupWidth > 1 && countNotIn(i, k, zeroCount[z], 0, true, out));
    }
    int w = weights[k];
    if (overloaded(i, k, w, out) || underloaded(i, k, w, out)) {
      return true;
    }
    for (int i2 = 0; i2 < load.length; i2++) {
      if (i2 != i && status(i2, k) != EXCLUDED && underloaded(i2, k, 0, out)) {
        return true;
      }
    }
    if (counts && countNotIn(i, k, itemCount[k], w, false, out)) {
      return true;
    }
    if (loadValues(i, k, w, Long.MIN_VALUE, Long.MAX_VALUE, out)) {
      return true;
    }
    for (int i2 = 0; i2 < load.length; i2++) {
      if (i2 != i
          && status(i2, k) != EXCLUDED
          && loadValues(i2, k, 0, Long.MIN_VALUE, Long.MAX_VALUE, out)) {
        return true;
      }
    }
    return counts && groupWidth > 1 && countNotIn(i, k, itemCount[k], w, true, out);
  }

  // bin i with weight extra and its packed items other than skip exceeds its largest load
  private boolean overloaded(int i, int skip, long extra, EntryList out) {
    int max = trail.maxBefore(load[i], position);
    if (!packedAtLeast(i, skip, extra, max + 1L, out)) {
      return false;
    }
    trail.addUpperBound(load[i], position, out);
    return true;
  }

  // bin i with weight extra and every item other than skip not excluded from it stays below its
  // smallest load
  private boolean underloaded(int i, int skip, long extra, EntryList out) {
    int min = trail.minBefore(load[i], position);
    if (!possibleAtMost(i, skip, extra, min - 1L, out)) {
      return false;
    }
    trail.addLowerBound(load[i], position, out);
    return true;
  }

  // extra plus the items other than skip packed in bin i reach need; adds the fewest, largest
  private boolean packedAtLeast(int i, int skip, long extra, long need, EntryList out) {
    long sum = extra;
    for (int k = 0; k < bins.length && sum < need; k++) {
      if (k != skip && status(i, k) == FIXED) {
        sum += weights[k];
      }
    }
    if (sum < need) {
      return false;
    }
    sum = extra;
    for (int k = 0; k < bins.length && sum < need; k++) {
      if (k != skip && status(i, k) == FIXED) {
        addPacked(k, out);
        sum += weights[k];
      }
    }
    return true;
  }

  // extra plus the items other than skip not excluded from bin i stay at most cap; adds the
  // fewest, largest excluded items
  private boolean possibleAtMost(int i, int skip, long extra, long cap, EntryList out) {
    long possible = extra + sizeAll - (skip >= 0 ? weights[skip] : 0);
    if (possible <= cap) {
      return true;
    }
    long p = possible;
    for (int k = 0; k < bins.length && p > cap; k++) {
      if (k != skip && status(i, k) == EXCLUDED) {
        p -= weights[k];
      }
    }
    if (p > cap) {
      return false;
    }
    for (int k = 0; k < bins.length && possible > cap; k++) {
      if (k != skip && status(i, k) == EXCLUDED) {
        addExcluded(i, k, out);
        possible -= weights[k];
      }
    }
    return true;
  }

  /**
   * Explains that the load of bin i is not in [lo, hi] when it holds weight extra, its packed items
   * and a subset of its candidates, item skip aside: every such load in [lo, hi] is below the
   * load's minimum, above its maximum or a hole.
   */
  private boolean loadValues(int i, int skip, long extra, long lo, long hi, EntryList out) {
    IntVar l = load[i];
    int lmin = trail.minBefore(l, position);
    int lmax = trail.maxBefore(l, position);
    long base = extra;
    long total = 0;
    int[] c = new int[bins.length];
    int nc = 0;
    for (int k = 0; k < bins.length; k++) {
      if (k == skip) {
        continue;
      }
      byte s = status(i, k);
      if (s == FIXED) {
        base += weights[k];
      } else if (s == CANDIDATE) {
        c[nc++] = weights[k];
        total += weights[k];
      }
    }
    long a = Math.max(lo, base);
    long b = Math.min(hi, base + total);
    boolean needMin = false;
    boolean needMax = false;
    int mark = out.size();
    if (a <= b) {
      if (b - base <= SUBSET_SUM_LIMIT) {
        long[] sums = subsetSums(c, nc, (int) (b - base));
        int s = nextSum(sums, (int) (a - base));
        while (s >= 0 && s <= b - base) {
          long t = base + s;
          if (t < lmin) {
            needMin = true;
          } else if (t > lmax) {
            needMax = true;
          } else if (!trail.excludedBefore(l, (int) t, position, out)) {
            out.truncate(mark);
            return false;
          }
          s = nextSum(sums, s + 1);
        }
      } else {
        long from = Math.max(a, lmin);
        long to = Math.min(b, lmax);
        if (from <= to && reachable(c, nc, total, from - base, to - base)) {
          return false;
        }
        needMin = a < lmin;
        needMax = b > lmax;
      }
    }
    if (needMin) {
      trail.addLowerBound(l, position, out);
    }
    if (needMax) {
      trail.addUpperBound(l, position, out);
    }
    for (int k = 0; k < bins.length; k++) {
      if (k == skip) {
        continue;
      }
      byte s = status(i, k);
      if (s == FIXED) {
        addPacked(k, out);
      } else if (s == EXCLUDED && weights[k] <= hi - base) {
        // an excluded item heavier than that would put the load above hi anyway
        addExcluded(i, k, out);
      }
    }
    return true;
  }

  // the subset sums of the first n weights up to limit, as a bitset
  private static long[] subsetSums(int[] w, int n, int limit) {
    long[] bits = new long[(limit >>> 6) + 1];
    bits[0] = 1L;
    for (int k = 0; k < n; k++) {
      int x = w[k];
      if (x > limit || x == 0) {
        continue;
      }
      int ws = x >>> 6;
      int bs = x & 63;
      for (int i = bits.length - 1; i >= ws; i--) {
        long v = bits[i - ws] << bs;
        if (bs != 0 && i - ws - 1 >= 0) {
          v |= bits[i - ws - 1] >>> (64 - bs);
        }
        bits[i] |= v;
      }
    }
    return bits;
  }

  private static int nextSum(long[] bits, int from) {
    int i = from >>> 6;
    if (i >= bits.length) {
      return -1;
    }
    long word = bits[i] & (-1L << (from & 63));
    while (true) {
      if (word != 0) {
        return (i << 6) + Long.numberOfTrailingZeros(word);
      }
      if (++i == bits.length) {
        return -1;
      }
      word = bits[i];
    }
  }

  // false only when no subset of the weights (descending) sums to a value in [lo, hi]
  private boolean reachable(int[] w, int n, long total, long lo, long hi) {
    if (hi < 0 || lo > total) {
      return false;
    }
    if (lo <= 0 || hi >= total) {
      return true;
    }
    return !Binpacking.noSum(w, n, total, lo, hi, bounds);
  }

  /**
   * Turns on the explanations of the cardinality rules of {@link Binpacking}: bounds on the number
   * of items in a bin or a group of consecutive bins, from its card variables, its packed and
   * excluded items, its loads and the other bins.
   *
   * @param card the number of items of each bin, or null for none
   * @param itemCount per item, the number of items it stands for (1 without card variables)
   * @param zeroBins the bin variables of the counted items of weight 0
   * @param zeroCount the number of items each of them stands for
   * @param totalCount the number of items
   * @param unit whether every item of positive weight counts once
   * @param groupWidth the widest group of consecutive bins the rules look at, 1 for single bins
   */
  void counting(
      IntVar[] card,
      int[] itemCount,
      IntVar[] zeroBins,
      int[] zeroCount,
      long totalCount,
      boolean unit,
      int groupWidth) {
    this.counts = true;
    this.card = card;
    if (card != null) {
      Map<IntVar, Integer> map = new HashMap<>();
      Set<IntVar> shared = new HashSet<>();
      for (int i = 0; i < card.length; i++) {
        if (map.putIfAbsent(card[i], i) != null) {
          shared.add(card[i]);
        }
      }
      map.keySet().removeAll(shared); // a counter of two bins bounds their sum, not each bin
      this.cardMap = map;
    }
    this.itemCount = itemCount;
    this.zeroBins = zeroBins;
    this.zeroCount = zeroCount;
    this.totalCount = totalCount;
    this.unit = unit;
    this.groupWidth = Math.max(1, Math.min(groupWidth, load.length));
    int m = load.length;
    this.zeroMin = new int[zeroBins.length];
    this.zeroMax = new int[zeroBins.length];
    this.zeroStatus = new byte[m][];
    this.binLo = new long[m];
    this.binHi = new long[m];
    this.binLoSource = new byte[m];
    this.binHiSource = new byte[m];
    this.binBounds = new boolean[m];
    this.ruleScan = new Scan(bins.length);
    this.boundScan = new Scan(bins.length);
    this.binScan = new Scan(bins.length);
  }

  /** The items of a group of bins a..b, item skip aside. */
  private static final class Scan {
    long packedCount; // the number of items packed in the group, weight 0 included
    long packedWeight;
    long zeroCandidates; // the number of items of weight 0 that may be in it, not packed
    long candidateCount; // the number of items of positive weight that may be in it, not packed
    final int[] candidates; // those items, by decreasing weight
    int n;

    Scan(int items) {
      this.candidates = new int[items];
    }

    long all() {
      return packedCount + candidateCount + zeroCandidates;
    }
  }

  // skip codes an item of positive weight as its index and one of weight 0 as -2 - its index
  private static int zeroSkip(int skip) {
    return skip <= -2 ? -2 - skip : -1;
  }

  // the status of item k in bins a..b: packed when its bins all lie in them, excluded when it is
  // excluded from each of them
  private byte status(int a, int b, int k) {
    if (a == b) {
      return status(a, k);
    }
    int lo = itemMin[k] - minBin;
    int hi = itemMax[k] - minBin;
    if (lo >= a && hi <= b) {
      return FIXED;
    }
    for (int j = Math.max(a, lo); j <= Math.min(b, hi); j++) {
      if (status(j, k) != EXCLUDED) {
        return CANDIDATE;
      }
    }
    return EXCLUDED;
  }

  private byte zeroStatus(int i, int z) {
    byte[] s = zeroStatus[i];
    if (s == null) {
      s = new byte[zeroBins.length];
      zeroStatus[i] = s;
    }
    if (s[z] == 0) {
      int b = i + minBin;
      if (zeroMin[z] == b && zeroMax[z] == b) {
        s[z] = FIXED;
      } else if (b < zeroMin[z] || b > zeroMax[z] || excluded(zeroBins[z], b)) {
        s[z] = EXCLUDED;
      } else {
        s[z] = CANDIDATE;
      }
    }
    return s[z];
  }

  private byte zeroStatus(int a, int b, int z) {
    if (a == b) {
      return zeroStatus(a, z);
    }
    int lo = zeroMin[z] - minBin;
    int hi = zeroMax[z] - minBin;
    if (lo >= a && hi <= b) {
      return FIXED;
    }
    for (int j = Math.max(a, lo); j <= Math.min(b, hi); j++) {
      if (zeroStatus(j, z) != EXCLUDED) {
        return CANDIDATE;
      }
    }
    return EXCLUDED;
  }

  private void scan(int a, int b, int skip, Scan s) {
    s.packedCount = 0;
    s.packedWeight = 0;
    s.zeroCandidates = 0;
    s.candidateCount = 0;
    s.n = 0;
    for (int k = 0; k < bins.length; k++) {
      if (k == skip) {
        continue;
      }
      byte st = status(a, b, k);
      if (st == FIXED) {
        s.packedCount += itemCount[k];
        s.packedWeight += weights[k];
      } else if (st == CANDIDATE) {
        s.candidates[s.n++] = k;
        s.candidateCount += itemCount[k];
      }
    }
    int zs = zeroSkip(skip);
    for (int z = 0; z < zeroBins.length; z++) {
      if (z == zs) {
        continue;
      }
      byte st = zeroStatus(a, b, z);
      if (st == FIXED) {
        s.packedCount += zeroCount[z];
      } else if (st == CANDIDATE) {
        s.zeroCandidates += zeroCount[z];
      }
    }
  }

  private void addPackedPositive(int a, int b, int skip, EntryList out) {
    for (int k = 0; k < bins.length; k++) {
      if (k != skip && status(a, b, k) == FIXED) {
        addPacked(k, out);
      }
    }
  }

  private void addPackedZero(int a, int b, int skip, EntryList out) {
    int zs = zeroSkip(skip);
    for (int z = 0; z < zeroBins.length; z++) {
      if (z != zs && zeroStatus(a, b, z) == FIXED) {
        trail.addLowerBound(zeroBins[z], position, out);
        trail.addUpperBound(zeroBins[z], position, out);
      }
    }
  }

  private void addExcludedZero(int a, int b, int skip, EntryList out) {
    int zs = zeroSkip(skip);
    for (int z = 0; z < zeroBins.length; z++) {
      if (z != zs && zeroStatus(a, b, z) == EXCLUDED) {
        for (int j = a; j <= b; j++) {
          trail.excludedBefore(zeroBins[z], j + minBin, position, out);
        }
      }
    }
  }

  // the items of positive weight other than skip excluded from bins a..b with a weight above
  // heavier and below lighter
  private void addExcludedPositive(
      int a, int b, int skip, long heavier, long lighter, EntryList out) {
    for (int k = 0; k < bins.length && weights[k] > heavier; k++) {
      if (k != skip && weights[k] < lighter && status(a, b, k) == EXCLUDED) {
        for (int j = a; j <= b; j++) {
          addExcluded(j, k, out);
        }
      }
    }
  }

  // the exclusions that keep the t heaviest candidates of s the heaviest t items: those heavier
  // than the t-th, all when there are fewer than t, none for t = 0
  private long heavierThan(int t, Scan s) {
    if (t <= 0) {
      return Long.MAX_VALUE;
    }
    return t <= s.n ? weights[s.candidates[t - 1]] : -1;
  }

  // the exclusions that keep the t lightest candidates of s the lightest t items
  private long lighterThan(int t, Scan s) {
    if (t <= 0) {
      return Long.MIN_VALUE;
    }
    return t <= s.n ? weights[s.candidates[s.n - t]] : Long.MAX_VALUE;
  }

  private long heaviest(int t, Scan s) {
    long sum = 0;
    for (int u = 0; u < Math.min(t, s.n); u++) {
      sum += weights[s.candidates[u]];
    }
    return sum;
  }

  private long lightest(int t, Scan s) {
    long sum = 0;
    for (int u = s.n - 1; u >= Math.max(0, s.n - t); u--) {
      sum += weights[s.candidates[u]];
    }
    return sum;
  }

  private long loadMinSum(int a, int b) {
    long sum = 0;
    for (int j = a; j <= b; j++) {
      sum += trail.minBefore(load[j], position);
    }
    return sum;
  }

  private long loadMaxSum(int a, int b) {
    long sum = 0;
    for (int j = a; j <= b; j++) {
      sum += trail.maxBefore(load[j], position);
    }
    return sum;
  }

  private void addLoadMins(int a, int b, EntryList out) {
    for (int j = a; j <= b; j++) {
      trail.addLowerBound(load[j], position, out);
    }
  }

  private void addLoadMaxs(int a, int b, EntryList out) {
    for (int j = a; j <= b; j++) {
      trail.addUpperBound(load[j], position, out);
    }
  }

  // the fewest heaviest candidates that reach the loads' minimum, beyond the packed items; more
  // than all items when none reach it
  private int heavyNeeded(int a, int b, Scan s) {
    long r = loadMinSum(a, b) - s.packedWeight;
    long sum = 0;
    int t = 0;
    while (t < s.n && sum < r) {
      sum += weights[s.candidates[t++]];
    }
    return sum >= r ? t : s.n + 1;
  }

  // the least number of items of bins a..b by their loads (unit items), on s scanned without skip
  private long loadCountMin(int a, int b, Scan s) {
    int t = heavyNeeded(a, b, s);
    return t > s.n ? s.all() + 1 : s.packedCount + t;
  }

  private void addLoadCountMin(int a, int b, Scan s, EntryList out) {
    int t = heavyNeeded(a, b, s);
    addPackedPositive(a, b, -1, out);
    addPackedZero(a, b, -1, out);
    if (t > 0) {
      addLoadMins(a, b, out);
      addExcludedPositive(a, b, -1, heavierThan(t > s.n ? s.n + 1 : t - 1, s), Long.MAX_VALUE, out);
    }
  }

  // the most lightest candidates within the loads' maximum, beyond the packed items; -1 when the
  // packed items exceed it
  private int lightFitting(int a, int b, Scan s) {
    long free = loadMaxSum(a, b) - s.packedWeight;
    if (free < 0) {
      return -1;
    }
    long sum = 0;
    int t = 0;
    while (t < s.n && sum + weights[s.candidates[s.n - 1 - t]] <= free) {
      sum += weights[s.candidates[s.n - 1 - t++]];
    }
    return t;
  }

  private long loadCountMax(int a, int b, Scan s) {
    int t = lightFitting(a, b, s);
    return t < 0 ? -1 : s.packedCount + s.zeroCandidates + t;
  }

  private void addLoadCountMax(int a, int b, Scan s, EntryList out) {
    int t = lightFitting(a, b, s);
    addLoadMaxs(a, b, out);
    addPackedPositive(a, b, -1, out);
    if (t >= 0) {
      addExcludedZero(a, b, -1, out);
      addExcludedPositive(a, b, -1, Long.MIN_VALUE, lighterThan(t + 1, s), out);
    }
  }

  private static final byte CARD = 0;
  private static final byte PACKED = 1;
  private static final byte LOAD = 2;
  private static final byte ALL = 3;

  // the bounds on the number of items of bin j from its card variable, its items and its load
  private void binBounds(int j) {
    if (binBounds[j]) {
      return;
    }
    binBounds[j] = true;
    Scan s = binScan;
    scan(j, j, -1, s);
    long lo = s.packedCount;
    byte loSource = PACKED;
    long hi = s.all();
    byte hiSource = ALL;
    if (unit) {
      long l = loadCountMin(j, j, s);
      if (l > lo) {
        lo = l;
        loSource = LOAD;
      }
      long h = loadCountMax(j, j, s);
      if (h < hi) {
        hi = h;
        hiSource = LOAD;
      }
    }
    if (card != null) {
      long c = trail.minBefore(card[j], position);
      if (c >= lo) {
        lo = c;
        loSource = CARD;
      }
      c = trail.maxBefore(card[j], position);
      if (c <= hi) {
        hi = c;
        hiSource = CARD;
      }
    }
    binLo[j] = lo;
    binHi[j] = hi;
    binLoSource[j] = loSource;
    binHiSource[j] = hiSource;
  }

  private long binLo(int j) {
    binBounds(j);
    return binLo[j];
  }

  private long binHi(int j) {
    binBounds(j);
    return binHi[j];
  }

  // that bin j holds at least need items, need at most binLo(j)
  private void addBinLo(int j, long need, EntryList out) {
    binBounds(j);
    switch (binLoSource[j]) {
      case CARD -> trail.addBoundReaching(card[j], position, true, need, out);
      case PACKED -> {
        addPackedPositive(j, j, -1, out);
        addPackedZero(j, j, -1, out);
      }
      default -> {
        scan(j, j, -1, binScan);
        addLoadCountMin(j, j, binScan, out);
      }
    }
  }

  private void addBinHi(int j, long most, EntryList out) {
    binBounds(j);
    switch (binHiSource[j]) {
      case CARD -> trail.addBoundReaching(card[j], position, false, most, out);
      case ALL -> {
        addExcludedPositive(j, j, -1, Long.MIN_VALUE, Long.MAX_VALUE, out);
        addExcludedZero(j, j, -1, out);
      }
      default -> {
        scan(j, j, -1, binScan);
        addLoadCountMax(j, j, binScan, out);
      }
    }
  }

  // the items the bins outside a..b cannot take: the least count of bins a..b by the others
  private long othersLo(int a, int b) {
    long rest = totalCount;
    for (int j = 0; j < load.length; j++) {
      if (j < a || j > b) {
        rest -= binHi(j);
      }
    }
    return rest;
  }

  private long othersHi(int a, int b) {
    long rest = totalCount;
    for (int j = 0; j < load.length; j++) {
      if (j < a || j > b) {
        rest -= binLo(j);
      }
    }
    return rest;
  }

  /** The least number of items of bins a..b that the rules derive. */
  private long countLo(int a, int b) {
    long lo = 0;
    for (int j = a; j <= b; j++) {
      lo += binLo(j);
    }
    if (a < b) {
      Scan s = boundScan;
      scan(a, b, -1, s);
      lo = Math.max(lo, s.packedCount);
      if (unit) {
        lo = Math.max(lo, loadCountMin(a, b, s));
      }
    }
    return Math.max(lo, othersLo(a, b));
  }

  private long countHi(int a, int b) {
    long hi = 0;
    for (int j = a; j <= b; j++) {
      hi += binHi(j);
    }
    if (a < b) {
      Scan s = boundScan;
      scan(a, b, -1, s);
      hi = Math.min(hi, s.all());
      if (unit) {
        hi = Math.min(hi, loadCountMax(a, b, s));
      }
    }
    return Math.min(hi, othersHi(a, b));
  }

  /** Explains that bins a..b hold at least need items; false when the rules do not derive it. */
  private boolean addCountLo(int a, int b, long need, EntryList out) {
    if (need <= 0) {
      return true;
    }
    long sum = 0;
    for (int j = a; j <= b; j++) {
      sum += binLo(j);
    }
    if (sum >= need) {
      for (int j = a; j <= b; j++) {
        // a single bin needs need items; in a group each bin gives what it has
        addBinLo(j, a == b ? need : binLo(j), out);
      }
      return true;
    }
    if (a < b) {
      Scan s = boundScan;
      scan(a, b, -1, s);
      if (s.packedCount >= need) {
        addPackedPositive(a, b, -1, out);
        addPackedZero(a, b, -1, out);
        return true;
      }
      if (unit && loadCountMin(a, b, s) >= need) {
        addLoadCountMin(a, b, s, out);
        return true;
      }
    }
    if (othersLo(a, b) >= need) {
      for (int j = 0; j < load.length; j++) {
        if (j < a || j > b) {
          addBinHi(j, binHi(j), out);
        }
      }
      return true;
    }
    return false;
  }

  /** Explains that bins a..b hold at most most items; false when the rules do not derive it. */
  private boolean addCountHi(int a, int b, long most, EntryList out) {
    long sum = 0;
    for (int j = a; j <= b; j++) {
      sum += binHi(j);
    }
    if (sum <= most) {
      for (int j = a; j <= b; j++) {
        addBinHi(j, a == b ? most : binHi(j), out);
      }
      return true;
    }
    if (a < b) {
      Scan s = boundScan;
      scan(a, b, -1, s);
      if (s.all() <= most) {
        for (int k = 0; k < bins.length; k++) {
          if (status(a, b, k) == EXCLUDED) {
            for (int j = a; j <= b; j++) {
              addExcluded(j, k, out);
            }
          }
        }
        addExcludedZero(a, b, -1, out);
        return true;
      }
      if (unit && loadCountMax(a, b, s) <= most) {
        addLoadCountMax(a, b, s, out);
        return true;
      }
    }
    if (othersHi(a, b) <= most) {
      for (int j = 0; j < load.length; j++) {
        if (j < a || j > b) {
          addBinLo(j, binLo(j), out);
        }
      }
      return true;
    }
    return false;
  }

  // the counter of bin i is at least v, or at most v
  private boolean cardAtLeast(int i, int v, EntryList out) {
    return countLo(i, i) >= v && addCountLo(i, i, v, out);
  }

  private boolean cardAtMost(int i, int v, EntryList out) {
    return countHi(i, i) <= v && addCountHi(i, i, v, out);
  }

  /**
   * Explains by the counts that item skip (see zeroSkip), of count c and weight w, is not in bin i:
   * some group of bins with i is full without it or overloaded or underloaded with it, or some
   * group without i needs it. Groups wider than one bin only when groups is set.
   */
  private boolean countNotIn(int i, int skip, int c, long w, boolean groups, EntryList out) {
    int m = load.length;
    int from = groups ? 2 : 1;
    int to = groups ? groupWidth : 1;
    for (int width = from; width <= to; width++) {
      for (int a = Math.max(0, i - width + 1); a <= Math.min(i, m - width); a++) {
        if (countExcludes(a, a + width - 1, skip, c, w, out)) {
          return true;
        }
      }
    }
    for (int width = from; width <= to; width++) {
      for (int a = 0; a + width <= m; a++) {
        int b = a + width - 1;
        if ((i < a || i > b) && countNeeds(a, b, skip, c, out)) {
          return true;
        }
      }
    }
    return false;
  }

  private boolean candidate(int a, int b, int skip) {
    return skip >= 0 ? status(a, b, skip) == CANDIDATE : zeroStatus(a, b, -2 - skip) == CANDIDATE;
  }

  // the item, counted c times and weighing w, does not fit in bins a..b by their counts
  private boolean countExcludes(int a, int b, int skip, int c, long w, EntryList out) {
    Scan s = ruleScan;
    scan(a, b, skip, s);
    long hi = countHi(a, b);
    if (s.packedCount + c > hi) {
      int mark = out.size();
      if (addCountHi(a, b, s.packedCount + c - 1, out)) {
        addPackedPositive(a, b, skip, out);
        addPackedZero(a, b, skip, out);
        return true;
      }
      out.truncate(mark);
      return false;
    }
    if (!unit) {
      return false;
    }
    // too big: with it the group still needs others more items, and the lightest of them overload
    // the group
    long lo = countLo(a, b);
    long others = lo - s.packedCount - c - s.zeroCandidates;
    if (others > 0 && others <= s.n) {
      long light = lightest((int) others, s);
      if (s.packedWeight + w + light > loadMaxSum(a, b)) {
        int mark = out.size();
        if (addCountLo(a, b, lo, out)) {
          addLoadMaxs(a, b, out);
          addPackedPositive(a, b, skip, out);
          addExcludedZero(a, b, skip, out);
          addExcludedPositive(a, b, skip, Long.MIN_VALUE, lighterThan((int) others, s), out);
          return true;
        }
        out.truncate(mark);
        return false;
      }
    }
    // too small: with it the group takes at most h more items, and the heaviest of them do not
    // reach the group's minimum load
    long h = hi - s.packedCount - c;
    if (h < s.n) {
      long heavy = heaviest((int) h, s);
      if (s.packedWeight + w + heavy < loadMinSum(a, b)) {
        int mark = out.size();
        if (addCountHi(a, b, hi, out)) {
          addLoadMins(a, b, out);
          addPackedPositive(a, b, skip, out);
          addPackedZero(a, b, skip, out);
          addExcludedPositive(a, b, skip, heavierThan((int) h, s), Long.MAX_VALUE, out);
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  // bins a..b, which the item could still use, need it: without it they do not reach their count
  // or their minimum load
  private boolean countNeeds(int a, int b, int skip, int c, EntryList out) {
    if (!candidate(a, b, skip)) {
      return false;
    }
    Scan s = ruleScan;
    scan(a, b, skip, s);
    long lo = countLo(a, b);
    if (s.all() < lo) {
      int mark = out.size();
      if (addCountLo(a, b, s.all() + 1, out)) {
        for (int k = 0; k < bins.length; k++) {
          if (k != skip && status(a, b, k) == EXCLUDED) {
            for (int j = a; j <= b; j++) {
              addExcluded(j, k, out);
            }
          }
        }
        addExcludedZero(a, b, skip, out);
        return true;
      }
      out.truncate(mark);
      return false;
    }
    if (!unit) {
      return false;
    }
    long hi = countHi(a, b);
    long most = hi - s.packedCount;
    if (most >= 0 && most < s.n && s.packedWeight + heaviest((int) most, s) < loadMinSum(a, b)) {
      int mark = out.size();
      if (addCountHi(a, b, hi, out)) {
        addLoadMins(a, b, out);
        addPackedPositive(a, b, skip, out);
        addPackedZero(a, b, skip, out);
        addExcludedPositive(a, b, skip, heavierThan((int) most, s), Long.MAX_VALUE, out);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // the load of bin i is at least v since a group with it holds at least its count's lightest
  // items and the group's other loads take at most their maxima
  private boolean countLoadAtLeast(int i, long v, boolean groups, EntryList out) {
    if (!unit) {
      return false;
    }
    int m = load.length;
    int from = groups ? 2 : 1;
    int to = groups ? groupWidth : 1;
    for (int width = from; width <= to; width++) {
      for (int a = Math.max(0, i - width + 1); a <= Math.min(i, m - width); a++) {
        int b = a + width - 1;
        Scan s = ruleScan;
        scan(a, b, -1, s);
        long lo = countLo(a, b);
        long need = lo - s.packedCount - s.zeroCandidates;
        if (need <= 0 || need > s.n) {
          continue;
        }
        long others = loadMaxSum(a, b) - trail.maxBefore(load[i], position);
        if (s.packedWeight + lightest((int) need, s) - others >= v) {
          int mark = out.size();
          if (addCountLo(a, b, lo, out)) {
            addPackedPositive(a, b, -1, out);
            addExcludedZero(a, b, -1, out);
            addExcludedPositive(a, b, -1, Long.MIN_VALUE, lighterThan((int) need, s), out);
            for (int j = a; j <= b; j++) {
              if (j != i) {
                trail.addUpperBound(load[j], position, out);
              }
            }
            return true;
          }
          out.truncate(mark);
        }
      }
    }
    return false;
  }

  private boolean countLoadAtMost(int i, long v, boolean groups, EntryList out) {
    if (!unit) {
      return false;
    }
    int m = load.length;
    int from = groups ? 2 : 1;
    int to = groups ? groupWidth : 1;
    for (int width = from; width <= to; width++) {
      for (int a = Math.max(0, i - width + 1); a <= Math.min(i, m - width); a++) {
        int b = a + width - 1;
        Scan s = ruleScan;
        scan(a, b, -1, s);
        long hi = countHi(a, b);
        long most = hi - s.packedCount;
        if (most < 0 || most >= s.n) {
          continue;
        }
        long others = loadMinSum(a, b) - trail.minBefore(load[i], position);
        if (s.packedWeight + heaviest((int) most, s) - others <= v) {
          int mark = out.size();
          if (addCountHi(a, b, hi, out)) {
            addPackedPositive(a, b, -1, out);
            addPackedZero(a, b, -1, out);
            addExcludedPositive(a, b, -1, heavierThan((int) most, s), Long.MAX_VALUE, out);
            for (int j = a; j <= b; j++) {
              if (j != i) {
                trail.addLowerBound(load[j], position, out);
              }
            }
            return true;
          }
          out.truncate(mark);
        }
      }
    }
    return false;
  }

  // a failure of the counts: a bin or group whose least count exceeds its largest, or bins that
  // together need more items than there are or take fewer
  private boolean countFailure(EntryList out) {
    int m = load.length;
    long sumLo = 0;
    long sumHi = 0;
    for (int j = 0; j < m; j++) {
      sumLo += binLo(j);
      sumHi += binHi(j);
    }
    if (sumLo > totalCount || sumHi < totalCount) {
      for (int j = 0; j < m; j++) {
        if (sumLo > totalCount) {
          addBinLo(j, binLo(j), out);
        } else {
          addBinHi(j, binHi(j), out);
        }
      }
      return true;
    }
    for (int width = 1; width <= groupWidth; width++) {
      for (int a = 0; a + width <= m; a++) {
        int b = a + width - 1;
        long hi = countHi(a, b);
        if (countLo(a, b) > hi) {
          int mark = out.size();
          if (addCountLo(a, b, hi + 1, out) && addCountHi(a, b, hi, out)) {
            return true;
          }
          out.truncate(mark);
        }
      }
    }
    return false;
  }

  // a failure of the bin-count bound: the bounds of the items it needs and the largest loads of
  // the bins they can use
  private boolean binCount(EntryList out) {
    int n = bins.length;
    boolean[] keep = new boolean[n];
    Arrays.fill(keep, true);
    if (!binCountFails(keep)) {
      return false;
    }
    if (n <= SHRINK_LIMIT) {
      for (int k = n - 1; k >= 0; k--) {
        keep[k] = false;
        if (!binCountFails(keep)) {
          keep[k] = true;
        }
      }
    }
    int first = Integer.MAX_VALUE;
    int last = Integer.MIN_VALUE;
    for (int k = 0; k < n; k++) {
      if (keep[k]) {
        trail.addLowerBound(bins[k], position, out);
        trail.addUpperBound(bins[k], position, out);
        first = Math.min(first, itemMin[k] - minBin);
        last = Math.max(last, itemMax[k] - minBin);
      }
    }
    for (int i = Math.max(0, first); i <= Math.min(load.length - 1, last); i++) {
      trail.addUpperBound(load[i], position, out);
    }
    return true;
  }

  private boolean binCountFails(boolean[] keep) {
    int n = bins.length;
    int[] unpacked = new int[n];
    int unpackedLength = 0;
    int[] packed = new int[load.length];
    long first = Long.MAX_VALUE;
    long last = Long.MIN_VALUE;
    for (int k = 0; k < n; k++) {
      if (!keep[k]) {
        continue;
      }
      if (itemMin[k] == itemMax[k]) {
        int p = itemMin[k] - minBin;
        if (p < 0 || p >= load.length) {
          return false;
        }
        packed[p] += weights[k];
      } else {
        unpacked[unpackedLength++] = weights[k];
      }
      first = Math.min(first, (long) itemMin[k] - minBin);
      last = Math.max(last, (long) itemMax[k] - minBin);
    }
    if (unpackedLength == 0) {
      return false;
    }
    int f = (int) Math.max(0, first);
    int nb = (int) Math.max(0, Math.min(load.length - 1L, last) - f + 1);
    int[] p = new int[nb];
    int[] capacity = new int[nb];
    for (int i = 0; i < nb; i++) {
      p[i] = packed[f + i];
      capacity[i] = trail.maxBefore(load[f + i], position);
    }
    int[] scratchSizes = new int[unpackedLength + nb];
    int[] scratchCounts = new int[unpackedLength + nb];
    return Binpacking.binCountFails(
        unpacked, unpackedLength, p, capacity, true, scratchSizes, scratchCounts);
  }
}
