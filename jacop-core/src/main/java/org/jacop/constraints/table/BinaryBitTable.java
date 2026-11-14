/*
 * BinaryBitTable.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with section 7 of the License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints.table;

import java.util.Map;
import java.util.WeakHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * A binary table (x, y) in R kept domain consistent with bit-sets: the supports of each value of x
 * are a bit-set over the values of y and the other way round, and a value w of y stays when its
 * bit-set meets the domain of x, checked first on the word of its last support (the residue). This
 * is AC3-bit with residues of Lecoutre and Vion, "Enforcing arc consistency using bitwise
 * operations", Constraint Programming Letters 2 (2008) 21-35. A revision costs about one word per
 * value of the revised variable and trails nothing but the domains, where a compact table trails
 * the words of its tuple set at every change.
 *
 * <p>The bit-sets of tables over the same tuples and the same value ranges are shared.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class BinaryBitTable extends Constraint
    implements UsesQueueVariable, SatisfiedPresent, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The most values between the least and the largest value of a column. */
  public static final int MAX_SPAN = Integer.getInteger("org.jacop.table.binaryBitSpan", 4096);

  private final IntVar x;

  private final IntVar y;

  private final int[][] tuples;

  /** The bit-sets of the supports, shared by the tables over the same tuples and ranges. */
  private Masks masks;

  /** Residues: the word of the last support found for each value, per direction. */
  private int[] xResidue;

  private int[] yResidue;

  private long[] xBits;

  private long[] yBits;

  private long[] keptBits;

  /** The variable that lost all its values in the last failure. */
  private IntVar failed;

  /** Marks of the values of the other variable already in a reason, by stamp. */
  private int[] reasonMark;

  private int reasonStamp;

  /** The bounds of the other variable at the position explained, and the supports beyond them. */
  private int boundLow;

  private int boundHigh;

  private int belowMax;

  private int aboveMin;

  private boolean xChanged;

  private boolean yChanged;

  private record Masks(
      int xBase, int xSpan, int yBase, int ySpan, long[][] forward, long[][] backward) {}

  /** Bit-sets per tuple array, then per value ranges. */
  private static final Map<int[][], Map<String, Masks>> SHARED = new WeakHashMap<>();

  /**
   * Creates the table.
   *
   * @param x the first variable
   * @param y the second variable
   * @param tuples the allowed pairs (x, y)
   */
  public BinaryBitTable(IntVar x, IntVar y, int[][] tuples) {
    checkInputForNullness(
        new String[] {"x", "y", "tuples"}, new Object[] {x}, new Object[] {y}, tuples);
    if (x == y) {
      throw new IllegalArgumentException("BinaryBitTable: x and y must be different variables");
    }
    this.x = x;
    this.y = y;
    this.tuples = tuples;
    this.queueIndex = 1;
    numberId = idNumber.incrementAndGet();
    setScope(x, y);
  }

  /**
   * Tells whether a table over two variables fits this constraint: two different variables whose
   * value ranges are at most {@link #MAX_SPAN} wide.
   *
   * @param x the first variable
   * @param y the second variable
   * @return true when it fits
   */
  public static boolean fits(IntVar x, IntVar y) {
    return x != y
        && (long) x.max() - x.min() < MAX_SPAN
        && (long) y.max() - y.min() < MAX_SPAN
        && !x.singleton()
        && !y.singleton();
  }

  private static Masks masks(int[][] tuples, int xBase, int xSpan, int yBase, int ySpan) {
    String key = xBase + ":" + xSpan + ":" + yBase + ":" + ySpan;
    synchronized (SHARED) {
      Map<String, Masks> byRange = SHARED.computeIfAbsent(tuples, t -> new java.util.HashMap<>());
      Masks m = byRange.get(key);
      if (m == null) {
        long[][] forward = new long[xSpan][];
        long[][] backward = new long[ySpan][];
        int yWords = (ySpan + 63) >>> 6;
        int xWords = (xSpan + 63) >>> 6;
        for (int[] t : tuples) {
          int a = t[0] - xBase;
          int b = t[1] - yBase;
          if (a < 0 || a >= xSpan || b < 0 || b >= ySpan) {
            continue;
          }
          if (forward[a] == null) {
            forward[a] = new long[yWords];
          }
          if (backward[b] == null) {
            backward[b] = new long[xWords];
          }
          forward[a][b >>> 6] |= 1L << b;
          backward[b][a >>> 6] |= 1L << a;
        }
        m = new Masks(xBase, xSpan, yBase, ySpan, forward, backward);
        byRange.put(key, m);
      }
      return m;
    }
  }

  @Override
  public void impose(Store store) {
    int xBase = x.min();
    int yBase = y.min();
    int xSpan = x.max() - xBase + 1;
    int ySpan = y.max() - yBase + 1;
    masks = masks(tuples, xBase, xSpan, yBase, ySpan);
    xResidue = new int[xSpan];
    yResidue = new int[ySpan];
    xBits = new long[(xSpan + 63) >>> 6];
    yBits = new long[(ySpan + 63) >>> 6];
    keptBits = new long[Math.max(xBits.length, yBits.length)];
    super.impose(store);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (v == x) {
      xChanged = true;
    } else {
      yChanged = true;
    }
  }

  @Override
  public void consistency(Store store) {
    boolean reviseY = xChanged;
    boolean reviseX = yChanged;
    xChanged = false;
    yChanged = false;
    if (!reviseX && !reviseY) {
      reviseX = true;
      reviseY = true;
    }
    while (reviseX || reviseY) {
      if (reviseY) {
        reviseY = false;
        if (revise(store, y, masks.yBase, masks.backward, yResidue, x, masks.xBase, xBits)) {
          reviseX = true;
        }
      }
      if (reviseX) {
        reviseX = false;
        if (revise(store, x, masks.xBase, masks.forward, xResidue, y, masks.yBase, yBits)) {
          reviseY = true;
        }
      }
    }
    if (x.singleton() || y.singleton()) {
      // domain consistent with one of them fixed: every value of the other one is supported
      removeConstraint();
    }
  }

  /**
   * Removes the values of v without a support in the domain of other.
   *
   * @return whether v lost values
   */
  private boolean revise(
      Store store,
      IntVar v,
      int vBase,
      long[][] supports,
      int[] residue,
      IntVar other,
      int otherBase,
      long[] otherBits) {
    IntDomain od = other.dom();
    for (int k = 0; k < otherBits.length; k++) {
      otherBits[k] = od.bitsFrom(otherBase + (k << 6));
    }
    IntDomain d = v.dom();
    long[] kept = keptBits;
    int words = (supports.length + 63) >>> 6;
    boolean removed = false;
    long[][] opposite = supports == masks.forward ? masks.backward : masks.forward;
    if ((long) od.getSize() * words < d.getSize()) {
      // few values of other: the union of their supports, a word per value and word
      java.util.Arrays.fill(kept, 0, words, 0L);
      for (int k = 0; k < otherBits.length; k++) {
        long word = otherBits[k];
        while (word != 0) {
          int i = (k << 6) + Long.numberOfTrailingZeros(word);
          word &= word - 1;
          long[] s = i < opposite.length ? opposite[i] : null;
          if (s != null) {
            for (int j = 0; j < words; j++) {
              kept[j] |= s[j];
            }
          }
        }
      }
      for (int k = 0; k < words; k++) {
        long word = d.bitsFrom(vBase + (k << 6));
        long keep = word & kept[k];
        if (keep != word) {
          removed = true;
        }
        kept[k] = keep;
      }
      return removed && narrow(store, v, vBase, supports.length, kept);
    }
    for (int k = 0; k < words; k++) {
      long word = d.bitsFrom(vBase + (k << 6));
      long keep = word;
      while (word != 0) {
        int bit = Long.numberOfTrailingZeros(word);
        word &= word - 1;
        int i = (k << 6) + bit;
        long[] s = supports[i];
        if (s == null) {
          keep &= ~(1L << bit);
          continue;
        }
        int r = residue[i];
        if ((s[r] & otherBits[r]) != 0) {
          continue;
        }
        boolean ok = false;
        for (int j = 0; j < s.length; j++) {
          if ((s[j] & otherBits[j]) != 0) {
            residue[i] = j;
            ok = true;
            break;
          }
        }
        if (!ok) {
          keep &= ~(1L << bit);
        }
      }
      if (keep != d.bitsFrom(vBase + (k << 6))) {
        removed = true;
      }
      kept[k] = keep;
    }
    return removed && narrow(store, v, vBase, supports.length, kept);
  }

  private boolean narrow(Store store, IntVar v, int vBase, int span, long[] kept) {
    IntervalDomain result = new IntervalDomain();
    int start = -1;
    for (int i = 0; i < span; i++) {
      boolean in = (kept[i >>> 6] & (1L << i)) != 0;
      if (in && start < 0) {
        start = i;
      } else if (!in && start >= 0) {
        result.unionAdapt(vBase + start, vBase + i - 1);
        start = -1;
      }
    }
    if (start >= 0) {
      result.unionAdapt(vBase + start, vBase + span - 1);
    }
    if (result.isEmpty()) {
      failed = v;
      throw Store.failException;
    }
    v.domain.in(store.level, v, result);
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar v = trail.variable(entry);
    if (v != x && v != y) {
      return false;
    }
    return explainRemoved(trail, v, trail.removedMin(entry), trail.removedMax(entry), entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    IntVar v = failed;
    if (v != x && v != y) {
      return false;
    }
    IntDomain root = trail.rootDomain(v);
    return explainRemoved(trail, v, root.min(), root.max(), trail.size(), out);
  }

  /**
   * Adds the reason why the values lo..hi of v are not in its domain at the position: each value
   * was removed before it or has all its supports removed from the other variable before it.
   */
  private boolean explainRemoved(
      AtomicTrail trail, IntVar v, int lo, int hi, int position, EntryList out) {
    boolean isX = v == x;
    IntVar other = isX ? y : x;
    int vBase = isX ? masks.xBase : masks.yBase;
    int otherBase = isX ? masks.yBase : masks.xBase;
    long[][] supports = isX ? masks.forward : masks.backward;
    IntDomain vRoot = trail.rootDomain(v);
    IntDomain otherRoot = trail.rootDomain(other);
    int otherSpan = isX ? masks.ySpan : masks.xSpan;
    if (reasonMark == null || reasonMark.length < Math.max(masks.xSpan, masks.ySpan)) {
      reasonMark = new int[Math.max(masks.xSpan, masks.ySpan)];
    }
    if (++reasonStamp == 0) {
      java.util.Arrays.fill(reasonMark, 0);
      reasonStamp = 1;
    }
    int from = Math.max(lo, vRoot.min());
    int to = Math.min(hi, vRoot.max());
    // supports beyond the bounds of other are excluded by its bound atoms, one per side for all
    // values, the weakest that still excludes them
    boundLow = trail.minBefore(other, position);
    boundHigh = trail.maxBefore(other, position);
    belowMax = Integer.MIN_VALUE;
    aboveMin = Integer.MAX_VALUE;
    for (int w = from; w <= to; w++) {
      if (!vRoot.contains(w)) {
        continue;
      }
      int i = w - vBase;
      long[] s = i >= 0 && i < supports.length ? supports[i] : null;
      if (s == null) {
        // no tuple has w: the table alone removes it
        continue;
      }
      if (!supportsExcluded(trail, other, otherBase, otherRoot, otherSpan, s, position, out)) {
        if (!trail.excludedBefore(v, w, position, out)) {
          return false;
        }
      }
    }
    if (belowMax != Integer.MIN_VALUE) {
      trail.addBoundReaching(other, position, true, (long) belowMax + 1, out);
    }
    if (aboveMin != Integer.MAX_VALUE) {
      trail.addBoundReaching(other, position, false, (long) aboveMin - 1, out);
    }
    return true;
  }

  // adds the exclusions of the supports s of a value from other; false when one is not excluded
  private boolean supportsExcluded(
      AtomicTrail trail,
      IntVar other,
      int otherBase,
      IntDomain otherRoot,
      int otherSpan,
      long[] s,
      int position,
      EntryList out) {
    int mark = out.size();
    int below = belowMax;
    int above = aboveMin;
    for (int k = 0; k < s.length; k++) {
      long word = s[k];
      while (word != 0) {
        int j = (k << 6) + Long.numberOfTrailingZeros(word);
        word &= word - 1;
        if (j >= otherSpan || reasonMark[j] == reasonStamp) {
          continue;
        }
        int a = otherBase + j;
        if (!otherRoot.contains(a)) {
          continue;
        }
        if (a < boundLow) {
          below = Math.max(below, a);
        } else if (a > boundHigh) {
          above = Math.min(above, a);
        } else if (!trail.excludedBefore(other, a, position, out)) {
          out.truncate(mark);
          return false;
        }
      }
    }
    belowMax = below;
    aboveMin = above;
    // only now: a support that is excluded counts for the next values once all of this value's are
    for (int k = 0; k < s.length; k++) {
      long word = s[k];
      while (word != 0) {
        int j = (k << 6) + Long.numberOfTrailingZeros(word);
        word &= word - 1;
        if (j < otherSpan) {
          reasonMark[j] = reasonStamp;
        }
      }
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    if (!x.singleton() || !y.singleton()) {
      return false;
    }
    int a = x.value() - masks.xBase;
    int b = y.value() - masks.yBase;
    long[] s = a >= 0 && a < masks.forward.length ? masks.forward[a] : null;
    return s != null && b >= 0 && b < masks.ySpan && (s[b >>> 6] & (1L << b)) != 0;
  }

  @Override
  public String toString() {
    return id() + " : binaryBitTable(" + x + ", " + y + ", " + tuples.length + " tuples)";
  }
}
