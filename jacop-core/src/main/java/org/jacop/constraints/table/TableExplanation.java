/*
 * TableExplanation.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints.table;

import java.util.Arrays;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of a table of hybrid tuples. An atom of a column's variable holds because every
 * tuple that would allow a value the atom removes was dead before it, and a failure because every
 * tuple is dead. A tuple is dead when some column's restriction accepts only values already out of
 * that column's domain (for the atom's own column, only removed values that were already out), or
 * when the bounds of two columns violate a restriction between them.
 *
 * <p>This is the resolved form of the support clauses with which Chuffed and CP-SAT encode a table,
 * one literal per tuple implied by the atoms of its values: the reason of a removed value has one
 * atom for each tuple that supported it. The work goes into keeping it small and cheap:
 *
 * <ul>
 *   <li>the candidate tuples come from the table's support bit-sets of the removed values rather
 *       than from a scan of the table, and in a scan the explained column is checked first;
 *   <li>the domains just before the explained position are read from the trail once per column, and
 *       the status of each value is computed once per explanation;
 *   <li>a tuple is first tried on the columns that already have an entry in the reason, where it is
 *       often dead for free, so the tuples share their atoms;
 *   <li>a value out of the bounds is explained by the bound, which removes the most values for the
 *       tuples still to come, rather than by its own {@code !=} atom.
 * </ul>
 *
 * <p>A restriction between columns kills a tuple only when the bounds of its two columns already
 * violate it. A tuple kept alive otherwise makes the explanation refuse, and the generic reason is
 * used.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class TableExplanation {

  /** A column restriction is not dead. */
  private static final int ALIVE = -1;

  /** A column restriction is dead by the domains at the start of recording: no entry needed. */
  private static final int FREE = 0;

  /**
   * The class ranges the support bit-sets are united over at most; more and the table is scanned.
   */
  private static final int CLASS_LIMIT = 64;

  /** The largest root domain span whose values are indexed directly. */
  private static final int DENSE_SPAN = 1 << 12;

  private final HybridTable table;

  // The explanation being built: its trail, the position before which the domains are read, and
  // its number, which stamps what was computed for it.
  private AtomicTrail trail;
  private int position;
  private int call;

  // Column snapshots before the position, built on first use: the root domain, the bounds and the
  // entries that set them (-1 for a root bound), and the != entries, indexed by value for a small
  // root span (neStamp, neEntry from neBase) and otherwise sorted by value (neValue, neEntry).
  private final int[] built;
  private final int[] lo;
  private final int[] hi;
  private final int[] geLatest;
  private final int[] leLatest;
  private final int[] neBuilt;
  private final int[][] neValue;
  private final int[][] neEntry;
  private final int[] neSize;
  private final int[][] neStamp;
  private final int[] neBase;
  private final IntDomain[] roots;

  // The status of each value of a column with a small root span, as value() leaves it (ALIVE, FREE
  // or one requirement), for the values whose valueStamp is the call; the alternatives are at
  // valueAlt[3 * k + 1 ..], their number at valueAlt[3 * k].
  private final int[][] valueStamp;
  private final int[][] valueStatus;
  private final int[][] valueAlt;
  private final int[] valueBase;

  // Requirements of a column restriction (or of a restriction between columns): each is a set of
  // alternative entries, one of which must be in the reason. Requirement q has alternatives
  // alt[reqStart[q] .. reqStart[q + 1] - 1].
  private int[] alt = new int[64];
  private int[] reqStart = new int[17];
  private int reqCount;
  private int altCount;

  // Entries in the reason have chosen[entry] == call.
  private int[] chosen = new int[256];

  private long[] candidates;

  // The columns with an entry in the reason have columnChosen[j] == call.
  private final int[] columnChosen;

  TableExplanation(HybridTable table) {
    this.table = table;
    int arity = table.x.length;
    built = new int[arity];
    lo = new int[arity];
    hi = new int[arity];
    geLatest = new int[arity];
    leLatest = new int[arity];
    neBuilt = new int[arity];
    neValue = new int[arity][];
    neEntry = new int[arity][];
    neSize = new int[arity];
    neStamp = new int[arity][];
    neBase = new int[arity];
    roots = new IntDomain[arity];
    columnChosen = new int[arity];
    valueStamp = new int[arity][];
    valueStatus = new int[arity][];
    valueAlt = new int[arity][];
    valueBase = new int[arity];
  }

  /**
   * Adds to {@code out} the reason of an entry of one of the table's variables.
   *
   * @param trail the trail
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when some tuple allowing a removed value is not dead before the entry
   */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar[] x = table.x;
    IntVar y = trail.variable(entry);
    int i = -1;
    for (int k = 0; k < x.length; k++) {
      if (x[k] == y) {
        i = k;
        break;
      }
    }
    if (i < 0) {
      return false;
    }
    start(trail, entry);
    int mark = out.size();
    int rlo = trail.removedMin(entry);
    int rhi = trail.removedMax(entry);
    int n = table.tupleCount;
    if (candidates == null) {
      candidates = new long[(n + 63) >> 6];
    }
    Arrays.fill(candidates, 0L);
    if (table.addCandidates(i, rlo, rhi, candidates, CLASS_LIMIT)) {
      for (int w = 0; w < candidates.length; w++) {
        for (long bits = candidates[w]; bits != 0L; bits &= bits - 1) {
          if (!kill((w << 6) + Long.numberOfTrailingZeros(bits), i, rlo, rhi, out)) {
            out.truncate(mark);
            return false;
          }
        }
      }
    } else {
      for (int t = 0; t < n; t++) {
        if (!kill(t, i, rlo, rhi, out)) {
          out.truncate(mark);
          return false;
        }
      }
    }
    out.sortUnique(mark);
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure: every tuple is dead.
   *
   * @param trail the trail
   * @param out where the reason entries are added
   * @return false when some tuple is not dead now
   */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    start(trail, trail.size());
    int mark = out.size();
    for (int t = 0; t < table.tupleCount; t++) {
      if (!kill(t, -1, 0, 0, out)) {
        out.truncate(mark);
        return false;
      }
    }
    out.sortUnique(mark);
    return true;
  }

  private void start(AtomicTrail trail, int position) {
    this.trail = trail;
    this.position = position;
    call++;
    if (call == Integer.MAX_VALUE) {
      call = 1;
      Arrays.fill(built, 0);
      Arrays.fill(neBuilt, 0);
      Arrays.fill(chosen, 0);
      Arrays.fill(columnChosen, 0);
      for (int[] stamp : neStamp) {
        if (stamp != null) {
          Arrays.fill(stamp, 0);
        }
      }
      for (int[] stamp : valueStamp) {
        if (stamp != null) {
          Arrays.fill(stamp, 0);
        }
      }
    }
    if (chosen.length < position) {
      chosen = Arrays.copyOf(chosen, Math.max(position, 2 * chosen.length));
    }
  }

  /**
   * Shows tuple t dead, adding to {@code out} the entries this needs that are not in it yet: the
   * explained column first, which most candidates of a scan already rule out, then the columns with
   * entries in the reason, where the tuple may be dead for free, and only then every column and
   * restriction between columns for the cheapest way.
   *
   * @return false when the tuple is alive
   */
  private boolean kill(int t, int i, int rlo, int rhi, EntryList out) {
    int arity = table.x.length;
    int base = t * arity;
    Restriction[] cells = table.cells;
    if (i >= 0) {
      int status = evaluate(cells[base + i], i, i, rlo, rhi);
      if (status == FREE || status > 0 && cost() == 0) {
        return true;
      }
    }
    for (int j = 0; j < arity; j++) {
      if (j != i && columnChosen[j] == call) {
        int status = evaluate(cells[base + j], j, i, rlo, rhi);
        if (status == FREE || status > 0 && cost() == 0) {
          return true;
        }
      }
    }
    int best = Integer.MAX_VALUE;
    int bestColumn = -2;
    for (int j = 0; j <= arity && best > 0; j++) {
      int status =
          j == arity
              ? between(cells, base, i, rlo, rhi)
              : evaluate(cells[base + j], j, i, rlo, rhi);
      if (status == FREE) {
        return true;
      }
      if (status > 0 && cost() < best) {
        best = cost();
        bestColumn = j;
      }
    }
    if (bestColumn == -2) {
      return false;
    }
    if (bestColumn == arity) {
      between(cells, base, i, rlo, rhi);
    } else {
      evaluate(cells[base + bestColumn], bestColumn, i, rlo, rhi);
    }
    for (int q = 0; q < reqCount; q++) {
      if (!anyChosen(q)) {
        choose(alt[reqStart[q]], out);
      }
    }
    return true;
  }

  /**
   * Restriction r on column j dead before the position: for the explained column i, accepting only
   * values of [rlo, rhi] already out. An equality on a column with a small root span is looked up
   * in a cache of the explanation.
   */
  private int evaluate(Restriction r, int j, int i, int rlo, int rhi) {
    if (r.kind != Restriction.Kind.EQ) {
      return j == i ? own(r, j, rlo, rhi) : column(r, j);
    }
    int v = r.value;
    if (j == i && (v < rlo || v > rhi)) {
      return FREE;
    }
    snapshot(j);
    int[] stamp = valueStamp[j];
    if (stamp == null) {
      reqCount = 0;
      altCount = 0;
      return value(j, v) ? reqCount : ALIVE;
    }
    int k = v - valueBase[j];
    if (k < 0 || k >= stamp.length) {
      return FREE;
    }
    int[] alts = valueAlt[j];
    if (stamp[k] != call) {
      stamp[k] = call;
      reqCount = 0;
      altCount = 0;
      int status = value(j, v) ? reqCount : ALIVE;
      valueStatus[j][k] = status;
      if (status > 0) {
        alts[3 * k] = altCount;
        System.arraycopy(alt, 0, alts, 3 * k + 1, altCount);
      }
      return status;
    }
    int status = valueStatus[j][k];
    if (status > 0) {
      altCount = alts[3 * k];
      System.arraycopy(alts, 3 * k + 1, alt, 0, altCount);
      reqCount = 1;
      reqStart[0] = 0;
      reqStart[1] = altCount;
    }
    return status;
  }

  // the number of requirements with no alternative in the reason yet
  private int cost() {
    int c = 0;
    for (int q = 0; q < reqCount; q++) {
      if (!anyChosen(q)) {
        c++;
      }
    }
    return c;
  }

  private boolean anyChosen(int q) {
    for (int k = reqStart[q]; k < reqStart[q + 1]; k++) {
      if (chosen[alt[k]] == call) {
        return true;
      }
    }
    return false;
  }

  private void choose(int e, EntryList out) {
    chosen[e] = call;
    out.add(e);
    IntVar y = trail.variable(e);
    for (int j = 0; j < table.x.length; j++) {
      if (table.x[j] == y) {
        columnChosen[j] = call;
      }
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Dead restrictions. Each returns ALIVE, FREE, or the number of requirements (alt, reqStart).

  /** Restriction r on column j, which is not the explained one, accepts no value left before. */
  private int column(Restriction r, int j) {
    if (r.kind == Restriction.Kind.ANY || r.isBinary()) {
      return ALIVE;
    }
    IntDomain root = root(j);
    return accepted(r, j, root.min(), root.max());
  }

  /** Restriction r on the explained column j accepts only values of [rlo, rhi] out before. */
  private int own(Restriction r, int j, int rlo, int rhi) {
    if (r.kind == Restriction.Kind.ANY || r.isBinary()) {
      return ALIVE;
    }
    return accepted(r, j, rlo, rhi);
  }

  /** Whether every value of [a, b] that r accepts was out of column j's domain before. */
  private int accepted(Restriction r, int j, int a, int b) {
    reqCount = 0;
    altCount = 0;
    boolean ok =
        switch (r.kind) {
          case EQ -> r.value < a || r.value > b || value(j, r.value);
          case NE ->
              (r.value <= a || segment(j, a, Math.min(b, r.value - 1)))
                  && (r.value >= b || segment(j, Math.max(a, r.value + 1), b));
          case LE -> r.value < a || segment(j, a, Math.min(b, r.value));
          case GE -> r.value > b || segment(j, Math.max(a, r.value), b);
          case IN -> {
            boolean all = true;
            for (int k = 0; k < r.values.length && all; k++) {
              int v = r.values[k];
              all = v < a || v > b || value(j, v);
            }
            yield all;
          }
          case NOT_IN -> {
            boolean all = true;
            long from = a;
            for (int k = 0; k <= r.values.length && all; k++) {
              long to = k < r.values.length ? Math.min(b, (long) r.values[k] - 1) : b;
              if (from <= to) {
                all = segment(j, (int) from, (int) to);
              }
              if (k < r.values.length) {
                from = Math.max(from, (long) r.values[k] + 1);
              }
            }
            yield all;
          }
          default -> false;
        };
    return ok ? reqCount : ALIVE;
  }

  /**
   * A restriction between two columns of the tuple violated by their bounds, the explained column
   * taking the values the atom removes. The violation with the fewest requirements is kept.
   */
  private int between(Restriction[] cells, int base, int i, int rlo, int rhi) {
    int arity = table.x.length;
    int best = ALIVE;
    int[] bestAlt = null;
    for (int k = 0; k < arity; k++) {
      Restriction r = cells[base + k];
      if (!r.isBinary()) {
        continue;
      }
      int status = violated(r, k, r.column, i, rlo, rhi);
      if (status != ALIVE && (best == ALIVE || status < best)) {
        best = status;
        if (status == FREE) {
          break;
        }
        bestAlt = new int[] {reqCount, altCount};
        bestAlt = Arrays.copyOf(bestAlt, 2 + altCount + reqCount + 1);
        System.arraycopy(alt, 0, bestAlt, 2, altCount);
        System.arraycopy(reqStart, 0, bestAlt, 2 + altCount, reqCount + 1);
      }
    }
    if (best > 0) {
      reqCount = bestAlt[0];
      altCount = bestAlt[1];
      System.arraycopy(bestAlt, 2, alt, 0, altCount);
      System.arraycopy(bestAlt, 2 + altCount, reqStart, 0, reqCount + 1);
    } else {
      reqCount = 0;
      altCount = 0;
    }
    return best;
  }

  /** Whether x[k] rel x[m] + offset is violated by the bounds of the two columns. */
  private int violated(Restriction r, int k, int m, int i, int rlo, int rhi) {
    reqCount = 0;
    altCount = 0;
    reqStart[0] = 0;
    long kMin = k == i ? rlo : low(k);
    long kMax = k == i ? rhi : high(k);
    long mMin = (m == i ? rlo : low(m)) + (long) r.offset;
    long mMax = (m == i ? rhi : high(m)) + (long) r.offset;
    boolean below; // x[k] is below x[m] + offset: needs k's upper and m's lower bound
    switch (r.relation) {
      case LT -> {
        if (kMin < mMax) {
          return ALIVE;
        }
        below = false;
      }
      case LE -> {
        if (kMin <= mMax) {
          return ALIVE;
        }
        below = false;
      }
      case GT -> {
        if (kMax > mMin) {
          return ALIVE;
        }
        below = true;
      }
      case GE -> {
        if (kMax >= mMin) {
          return ALIVE;
        }
        below = true;
      }
      case EQ -> {
        if (kMin > mMax) {
          below = false;
        } else if (kMax < mMin) {
          below = true;
        } else {
          return ALIVE;
        }
      }
      default -> {
        return ALIVE;
      }
    }
    if (below) {
      boundRequirement(k, i, false);
      boundRequirement(m, i, true);
    } else {
      boundRequirement(k, i, true);
      boundRequirement(m, i, false);
    }
    return reqCount;
  }

  // the latest lower (upper) bound entry of column j as a requirement, unless j is the explained
  // column or the bound is the initial one
  private void boundRequirement(int j, int i, boolean lower) {
    if (j == i) {
      return;
    }
    snapshot(j);
    int e = lower ? geLatest[j] : leLatest[j];
    if (e >= 0) {
      addAlternative(e);
      endRequirement();
    }
  }

  /** Whether value v was out of column j's domain before; adds its requirement. */
  private boolean value(int j, int v) {
    IntDomain root = root(j);
    if (!root.contains(v)) {
      return true;
    }
    snapshot(j);
    int e = notEqual(j, v);
    if (v < lo[j]) {
      addAlternative(geLatest[j]);
    } else if (v > hi[j]) {
      addAlternative(leLatest[j]);
    } else if (e < 0) {
      return false;
    }
    if (e >= 0) {
      addAlternative(e);
    }
    endRequirement();
    return true;
  }

  /** Whether every value of [a, b] was out of column j's domain before; adds the requirements. */
  private boolean segment(int j, int a, int b) {
    IntDomain root = root(j);
    a = Math.max(a, root.min());
    b = Math.min(b, root.max());
    if (a > b || !root.isIntersecting(a, b)) {
      return true;
    }
    snapshot(j);
    int l = lo[j];
    int h = hi[j];
    if (a < l && root.isIntersecting(a, Math.min(b, l - 1))) {
      addAlternative(geLatest[j]);
      endRequirement();
    }
    if (b > h && root.isIntersecting(Math.max(a, h + 1), b)) {
      addAlternative(leLatest[j]);
      endRequirement();
    }
    int from = Math.max(a, l);
    int to = Math.min(b, h);
    for (int v = from; v <= to; v++) {
      if (!root.contains(v)) {
        int next = root.nextValue(v);
        if (next <= v) {
          break;
        }
        v = next - 1;
        continue;
      }
      int e = notEqual(j, v);
      if (e < 0) {
        return false;
      }
      addAlternative(e);
      endRequirement();
    }
    return true;
  }

  private void addAlternative(int e) {
    if (altCount == alt.length) {
      alt = Arrays.copyOf(alt, 2 * altCount);
    }
    alt[altCount++] = e;
  }

  private void endRequirement() {
    if (reqCount + 2 > reqStart.length) {
      reqStart = Arrays.copyOf(reqStart, 2 * reqStart.length);
    }
    reqStart[0] = 0;
    reqStart[++reqCount] = altCount;
  }

  // ---------------------------------------------------------------------------------------------
  // Column snapshots.

  private IntDomain root(int j) {
    snapshot(j);
    return roots[j];
  }

  private int low(int j) {
    snapshot(j);
    return lo[j];
  }

  private int high(int j) {
    snapshot(j);
    return hi[j];
  }

  /** Reads column j's bounds and their entries before the position from the trail. */
  private void snapshot(int j) {
    if (built[j] == call) {
      return;
    }
    built[j] = call;
    IntVar y = table.x[j];
    int g = -1;
    int l = -1;
    for (int e = trail.lastEntry(y, position);
        e >= 0 && (g < 0 || l < 0);
        e = trail.previousEntry(e)) {
      int kind = trail.kind(e);
      if (kind == AtomicTrail.GE && g < 0) {
        g = e;
      } else if (kind == AtomicTrail.LE && l < 0) {
        l = e;
      }
    }
    geLatest[j] = g;
    leLatest[j] = l;
    IntDomain root = trail.rootDomain(y);
    roots[j] = root;
    lo[j] = g >= 0 ? trail.value(g) : root.min();
    hi[j] = l >= 0 ? trail.value(l) : root.max();
    if (valueStamp[j] == null && (long) root.max() - root.min() < DENSE_SPAN) {
      int span = root.max() - root.min() + 1;
      valueBase[j] = root.min();
      valueStamp[j] = new int[span];
      valueStatus[j] = new int[span];
      valueAlt[j] = new int[3 * span];
    }
  }

  /** The != entry of value v of column j before the position, or -1. */
  private int notEqual(int j, int v) {
    if (neBuilt[j] != call) {
      buildNotEqual(j);
    }
    int[] stamp = neStamp[j];
    if (stamp != null) {
      int k = v - neBase[j];
      return k >= 0 && k < stamp.length && stamp[k] == call ? neEntry[j][k] : -1;
    }
    int k = Arrays.binarySearch(neValue[j], 0, neSize[j], v);
    return k >= 0 ? neEntry[j][k] : -1;
  }

  /**
   * Reads column j's != entries before the position: into arrays indexed by value when the root
   * domain spans at most DENSE_SPAN values, stamped with the explanation's number so they need no
   * clearing, otherwise sorted by value.
   */
  private void buildNotEqual(int j) {
    neBuilt[j] = call;
    IntVar y = table.x[j];
    if (neStamp[j] == null && neValue[j] == null) {
      IntDomain root = trail.rootDomain(y);
      long span = (long) root.max() - root.min() + 1;
      if (span <= DENSE_SPAN) {
        neBase[j] = root.min();
        neStamp[j] = new int[(int) span];
        neEntry[j] = new int[(int) span];
      } else {
        neValue[j] = new int[8];
        neEntry[j] = new int[8];
      }
    }
    if (neStamp[j] != null) {
      int[] stamp = neStamp[j];
      int[] entry = neEntry[j];
      int b = neBase[j];
      for (int e = trail.lastEntry(y, position); e >= 0; e = trail.previousEntry(e)) {
        if (trail.kind(e) == AtomicTrail.NE) {
          int k = trail.value(e) - b;
          if (k >= 0 && k < stamp.length) {
            stamp[k] = call;
            entry[k] = e;
          }
        }
      }
      return;
    }
    int c = 0;
    long[] keys = new long[8];
    for (int e = trail.lastEntry(y, position); e >= 0; e = trail.previousEntry(e)) {
      if (trail.kind(e) == AtomicTrail.NE) {
        if (c == keys.length) {
          keys = Arrays.copyOf(keys, 2 * c);
        }
        keys[c++] = ((long) trail.value(e) << 32) | e;
      }
    }
    Arrays.sort(keys, 0, c);
    if (neValue[j].length < c) {
      neValue[j] = new int[c];
      neEntry[j] = new int[c];
    }
    for (int k = 0; k < c; k++) {
      neValue[j][k] = (int) (keys[k] >> 32);
      neEntry[j][k] = (int) keys[k];
    }
    neSize[j] = c;
  }
}
