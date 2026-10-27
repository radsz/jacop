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
import java.util.Map;
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
 *       largest loads of the bins, after dropping the items that the bound does not need.
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
  private int[] itemMin;
  private int[] itemMax;
  private byte[][] status; // per bin and item, computed when first asked; 0 when not yet
  private final EntryList scratch = new EntryList();
  private final long[] bounds = new long[2];

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
  }

  private void snapshot(AtomicTrail trail, int position) {
    this.trail = trail;
    this.position = position;
    int n = bins.length;
    if (itemMin == null) {
      itemMin = new int[n];
      itemMax = new int[n];
      status = new byte[load.length][];
    }
    for (int k = 0; k < n; k++) {
      itemMin[k] = trail.minBefore(bins[k], position);
      itemMax[k] = trail.maxBefore(bins[k], position);
    }
    for (byte[] s : status) {
      if (s != null) {
        Arrays.fill(s, (byte) 0);
      }
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
    Integer j = itemMap.get(x);
    if (j == null && !isZeroWeightBin(x)) {
      return false;
    }
    int k = j == null ? -1 : j;
    int lastBin = minBin + load.length - 1;
    switch (kind) {
      case AtomicTrail.GE -> {
        int m = trail.minBefore(x, entry);
        for (long u = minBin; u < v && u <= lastBin; u++) {
          if (u < m) {
            trail.addLowerBound(x, entry, out);
            u = m - 1L;
          } else if (!notIn(k, x, (int) u, out)) {
            return false;
          }
        }
        return true;
      }
      case AtomicTrail.LE -> {
        int m = trail.maxBefore(x, entry);
        for (long u = lastBin; u > v && u >= minBin; u--) {
          if (u > m) {
            trail.addUpperBound(x, entry, out);
            u = m + 1L;
          } else if (!notIn(k, x, (int) u, out)) {
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
    if (packedAtLeast(i, -1, 0, b, out) || othersAtMost(i, b, out)) {
      for (long t = b; t < v; t++) {
        trail.excludedBefore(l, (int) t, position, out);
      }
      return true;
    }
    return loadValues(i, -1, 0, Long.MIN_VALUE, v - 1L, out);
  }

  private boolean loadAtMost(int i, int v, EntryList out) {
    IntVar l = load[i];
    int m = trail.maxBefore(l, position);
    long b = v;
    while (b + 1 < m && excluded(l, b + 1)) {
      b++;
    }
    if (possibleAtMost(i, -1, 0, b, out) || othersAtLeast(i, b, out)) {
      for (long t = v + 1L; t <= b; t++) {
        trail.excludedBefore(l, (int) t, position, out);
      }
      return true;
    }
    return loadValues(i, -1, 0, v + 1L, Long.MAX_VALUE, out);
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
   * bin, or k in u would overload or underload u, or another bin needs k.
   */
  private boolean notIn(int k, IntVar x, int u, EntryList out) {
    if (u < minBin || u >= minBin + load.length) {
      return true;
    }
    if (trail.excludedBefore(x, u, position, out)) {
      return true;
    }
    if (k < 0) {
      return false;
    }
    int i = u - minBin;
    int w = weights[k];
    if (overloaded(i, k, w, out) || underloaded(i, k, w, out)) {
      return true;
    }
    for (int i2 = 0; i2 < load.length; i2++) {
      if (i2 != i && status(i2, k) != EXCLUDED && underloaded(i2, k, 0, out)) {
        return true;
      }
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
    return false;
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
        for (int s = nextSum(sums, (int) (a - base)); s >= 0 && s <= b - base; ) {
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
    int nb = (int) Math.max(0, Math.min(load.length - 1, last) - f + 1);
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
