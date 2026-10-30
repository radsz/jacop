/*
 * LexChain.java
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
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LexChainExplanation;
import org.jacop.util.VarIntMap;

/**
 * LexChain constrains a chain of vectors of the same length to be lexicographically ordered, x[0]
 * {@literal <=} x[1] {@literal <=} ... {@literal <=} x[m-1] (or {@literal <} for the strict chain).
 *
 * <p>It is the domain-consistent algorithm of M. Carlsson and N. Beldiceanu, "Arc-Consistency for a
 * Chain of Lexicographic Ordering Constraints", SICS Technical Report T2002-18. A forward pass
 * computes for each vector the lexicographically smallest tuple of its domains that can follow the
 * smallest tuple of the previous vector, a backward pass the largest tuple that can precede the
 * largest tuple of the next vector. The chain has a solution iff every smallest tuple is not above
 * the largest one, and a value has a support in the chain iff it has one in its vector between the
 * two tuples, which is established in linear time. A call from scratch costs O(m n) domain
 * operations for m vectors of length n. The m - 1 pairwise lex constraints it replaces are each
 * domain consistent but do not reach domain consistency on the chain.
 *
 * <p>The tuples are kept between calls. Domains only shrink until a backtrack, so a smallest tuple
 * stays the smallest as long as the tuple before it is unchanged and its own values are still in
 * the domains; only the positions that changed are checked for that. A call recomputes the smallest
 * tuples forward from the first changed vector while they change, the largest tuples backward
 * symmetrically, and prunes only the vectors whose domains or tuples changed. A tuple is saved on a
 * trail before its first change at a level and restored when the level is removed, so after a
 * backtrack the tuples are again those of the restored domains.
 *
 * <p>The consistency is proved for distinct variables; when a variable occurs more than once the
 * pruning stays correct and is repeated until nothing changes.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LexChain extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Copyable<LexChain>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The vectors of the chain, all of length n. */
  final IntVar[][] x;

  /** True for the strict chain x[0] {@literal <} x[1] {@literal <} ... */
  final boolean strict;

  /** Number of vectors. */
  final int m;

  /** Length of each vector. */
  final int n;

  /** True when a variable occurs more than once in the chain. */
  private final boolean hasDuplicates;

  /** Smallest feasible tuple of each vector. */
  private final int[][] lower;

  /** Largest feasible tuple of each vector. */
  private final int[][] upper;

  /** For each variable, its positions i * n + j in the chain. */
  private final VarIntMap varToSlot = new VarIntMap();

  /** For each variable slot, its positions i * n + j in x. */
  private int[][] varToPositions = new int[8][];

  /** Vectors whose domains changed since lower and upper were computed. */
  private final boolean[] changed;

  /** For each vector, the positions that changed, changedCount[i] of them. */
  private final int[][] changedPositions;

  private final int[] changedCount;

  /** Whether position i * n + j is in changedPositions. */
  private final boolean[] positionChanged;

  /** Vectors whose tuples changed in this call, so they are pruned again. */
  private final boolean[] dirty;

  /** First and last changed vector; first {@literal >} last when none changed. */
  private int firstChanged;

  private int lastChanged;

  /** Level of the first complete computation of the tuples; NONE while they are not valid. */
  private int validFrom = NONE;

  /** Level of a call that failed while changing the tuples, until that level is removed. */
  private int brokenAt = NONE;

  /**
   * Trail of saved tuples: the level, the tuple (i for lower[i], m + i for upper[i]), the level of
   * its previous save and its values.
   */
  private int[] trailLevel = new int[16];

  private int[] trailTuple = new int[16];

  private int[] trailPrevious = new int[16];

  private int[][] trailValues = new int[16][];

  private int trailSize;

  /** For each tuple, the level it was last saved at. */
  private final int[] savedAt;

  private static final int NONE = -1;

  /**
   * It creates a chain of lexicographically ordered vectors.
   *
   * @param x the vectors, all of the same length; x[i] is lexicographically before x[i+1].
   * @param strict true for a strictly increasing chain, false for a non-decreasing one.
   */
  public LexChain(IntVar[][] x, boolean strict) {

    checkInputForNullness("x", x);
    for (int i = 0; i < x.length; i++) {
      checkInputForNullness("x[" + i + "]", x[i]);
    }

    this.m = x.length;
    this.n = m == 0 ? 0 : x[0].length;
    for (int i = 1; i < m; i++) {
      if (x[i].length != n) {
        throw new IllegalArgumentException(
            "LexChain vectors must have the same length; x[0] has "
                + n
                + " elements and x["
                + i
                + "] has "
                + x[i].length);
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 1;
    this.strict = strict;
    this.x = new IntVar[m][];
    for (int i = 0; i < m; i++) {
      this.x[i] = Arrays.copyOf(x[i], n);
    }
    this.lower = new int[m][n];
    this.upper = new int[m][n];
    this.changed = new boolean[m];
    this.changedPositions = new int[m][n];
    this.changedCount = new int[m];
    this.positionChanged = new boolean[m * n];
    this.savedAt = new int[2 * m];
    Arrays.fill(savedAt, NONE);
    this.dirty = new boolean[m];
    this.firstChanged = m;
    this.lastChanged = -1;

    IntVar[] all = Arrays.stream(this.x).flatMap(Arrays::stream).toArray(IntVar[]::new);
    this.hasDuplicates = Arrays.stream(all).distinct().count() < all.length;

    setScope(all);
  }

  /**
   * It creates a non-decreasing chain of lexicographically ordered vectors.
   *
   * @param x the vectors, all of the same length; x[i] is lexicographically before x[i+1].
   */
  public LexChain(IntVar[][] x) {
    this(x, false);
  }

  @Override
  public void impose(Store store) {
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        int slot = varToSlot.get(x[i][j]);
        if (slot == VarIntMap.ABSENT) {
          slot = varToSlot.size();
          varToSlot.put(x[i][j], slot);
          if (slot == varToPositions.length) {
            varToPositions = Arrays.copyOf(varToPositions, 2 * slot);
          }
          varToPositions[slot] = new int[] {i * n + j};
        } else {
          int[] positions = varToPositions[slot];
          int[] more = Arrays.copyOf(positions, positions.length + 1);
          more[positions.length] = i * n + j;
          varToPositions[slot] = more;
        }
      }
    }
    super.impose(store);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void queueVariable(int level, Var var) {
    for (int k : varToPositions[varToSlot.get(var)]) {
      if (!positionChanged[k]) {
        positionChanged[k] = true;
        int i = k / n;
        changedPositions[i][changedCount[i]++] = k - i * n;
        changed[i] = true;
        firstChanged = Math.min(firstChanged, i);
        lastChanged = Math.max(lastChanged, i);
      }
    }
  }

  @Override
  public void consistency(Store store) {

    if (m < 2) {
      return;
    }
    if (n == 0) {
      // all vectors are the empty vector
      if (strict) {
        throw Store.failException;
      }
      return;
    }

    boolean all = validFrom == NONE || brokenAt != NONE;
    if (validFrom == NONE) {
      validFrom = store.level;
    }
    // if this call fails, the tuples it changed are valid again only after its level is removed
    brokenAt = store.level;

    do {
      store.propagationHasOccurred = false;
      propagate(store, all);
      all = true;
    } while (hasDuplicates && store.propagationHasOccurred);

    clearChanged();
    brokenAt = NONE;

    boolean fixed = true;
    for (int i = 0; i < m && fixed; i++) {
      fixed = Arrays.equals(lower[i], upper[i]);
    }
    if (fixed) {
      removeConstraint();
    }
  }

  @Override
  public void removeLevel(int level) {
    while (trailSize > 0 && trailLevel[trailSize - 1] >= level) {
      trailSize--;
      int k = trailTuple[trailSize];
      System.arraycopy(trailValues[trailSize], 0, k < m ? lower[k] : upper[k - m], 0, n);
      savedAt[k] = trailPrevious[trailSize];
    }
    if (level <= validFrom) {
      validFrom = NONE;
    }
    if (level <= brokenAt) {
      brokenAt = NONE;
    }
  }

  /** Saves tuple k (lower[k] or upper[k - m]) before its first change at this level. */
  private void save(int level, int k) {
    if (savedAt[k] == level) {
      return;
    }
    if (trailSize == trailLevel.length) {
      int size = 2 * trailSize;
      trailLevel = Arrays.copyOf(trailLevel, size);
      trailTuple = Arrays.copyOf(trailTuple, size);
      trailPrevious = Arrays.copyOf(trailPrevious, size);
      trailValues = Arrays.copyOf(trailValues, size);
    }
    if (trailValues[trailSize] == null) {
      trailValues[trailSize] = new int[n];
    }
    System.arraycopy(k < m ? lower[k] : upper[k - m], 0, trailValues[trailSize], 0, n);
    trailLevel[trailSize] = level;
    trailTuple[trailSize] = k;
    trailPrevious[trailSize] = savedAt[k];
    trailSize++;
    savedAt[k] = level;
  }

  private void clearChanged() {
    for (int i = firstChanged; i <= lastChanged; i++) {
      for (int c = 0; c < changedCount[i]; c++) {
        positionChanged[i * n + changedPositions[i][c]] = false;
      }
      changedCount[i] = 0;
      changed[i] = false;
    }
    firstChanged = m;
    lastChanged = -1;
  }

  /**
   * Recomputes the tuples that can have changed and prunes the vectors where something changed.
   *
   * @param all true to recompute and prune everything.
   */
  private void propagate(Store store, boolean all) {

    int first = all ? 0 : firstChanged;
    int last = all ? m - 1 : lastChanged;
    if (first > last) {
      return;
    }
    Arrays.fill(dirty, false);

    // smallest tuples forward; the one before the first changed vector is unchanged. The kept
    // tuples belong to domains that have only shrunk since, so the smallest tuples only grow and a
    // kept tuple that is still in the domains and still above the new one before it stays the
    // smallest. When the kept tuples are not valid (all) every one is recomputed.
    boolean previousSame = true;
    for (int i = first; i < m; i++) {
      boolean same;
      if (!all
          && (!changed[i] || stillIn(i, lower[i]))
          && (previousSame || follows(lower[i - 1], lower[i]))) {
        same = true;
      } else if (i == 0) {
        save(store.level, 0);
        same = true;
        for (int j = 0; j < n; j++) {
          int v = x[0][j].min();
          same &= lower[0][j] == v;
          lower[0][j] = v;
        }
      } else {
        save(store.level, i);
        same = smallestAbove(x[i], lower[i - 1], lower[i]);
      }
      dirty[i] |= !same;
      previousSame = same;
      if (same && i >= last) {
        break;
      }
    }

    previousSame = true;
    for (int i = last; i >= 0; i--) {
      boolean same;
      if (!all
          && (!changed[i] || stillIn(i, upper[i]))
          && (previousSame || follows(upper[i], upper[i + 1]))) {
        same = true;
      } else if (i == m - 1) {
        save(store.level, 2 * m - 1);
        same = true;
        for (int j = 0; j < n; j++) {
          int v = x[m - 1][j].max();
          same &= upper[m - 1][j] == v;
          upper[m - 1][j] = v;
        }
      } else {
        save(store.level, m + i);
        same = largestBelow(x[i], upper[i + 1], upper[i]);
      }
      dirty[i] |= !same;
      previousSame = same;
      if (same && i <= first) {
        break;
      }
    }

    for (int i = 0; i < m; i++) {
      if (all || dirty[i] || changed[i]) {
        if (Arrays.compare(lower[i], upper[i]) > 0) {
          throw Store.failException;
        }
        between(store, x[i], lower[i], upper[i]);
      }
    }
  }

  /** Whether tuple t can follow tuple s in the chain. */
  private boolean follows(int[] s, int[] t) {
    int c = Arrays.compare(s, t);
    return strict ? c < 0 : c <= 0;
  }

  /** Whether tuple t of vector i is still in the domains at the positions that changed. */
  private boolean stillIn(int i, int[] t) {
    for (int c = 0; c < changedCount[i]; c++) {
      int j = changedPositions[i][c];
      if (!x[i][j].domain.contains(t[j])) {
        return false;
      }
    }
    return true;
  }

  /**
   * Computes the lexicographically smallest tuple t of the domains of v with t {@literal >=} bound
   * ({@literal >} for the strict chain); fails if there is none.
   *
   * @return true if t is the same as before.
   */
  private boolean smallestAbove(IntVar[] v, int[] bound, int[] t) {

    int q = 0;
    while (q < n && v[q].domain.contains(bound[q])) {
      q++;
    }
    if (q == n && !strict) {
      return copy(bound, t, n);
    }

    // t equals bound before some position p, is above it at p and minimal after p; at q the
    // bound value is not in the domain, so any value above it will do
    for (int p = Math.min(q, n - 1); p >= 0; p--) {
      IntDomain d = v[p].domain;
      if (d.max() > bound[p]) {
        boolean same = copy(bound, t, p);
        int value = bound[p] < d.min() ? d.min() : d.nextValue(bound[p]);
        same &= t[p] == value;
        t[p] = value;
        for (int k = p + 1; k < n; k++) {
          value = v[k].min();
          same &= t[k] == value;
          t[k] = value;
        }
        return same;
      }
    }
    throw Store.failException;
  }

  /**
   * Computes the lexicographically largest tuple t of the domains of v with t {@literal <=} bound
   * ({@literal <} for the strict chain); fails if there is none.
   *
   * @return true if t is the same as before.
   */
  private boolean largestBelow(IntVar[] v, int[] bound, int[] t) {

    int q = 0;
    while (q < n && v[q].domain.contains(bound[q])) {
      q++;
    }
    if (q == n && !strict) {
      return copy(bound, t, n);
    }

    for (int p = Math.min(q, n - 1); p >= 0; p--) {
      IntDomain d = v[p].domain;
      if (d.min() < bound[p]) {
        boolean same = copy(bound, t, p);
        int value = bound[p] > d.max() ? d.max() : d.previousValue(bound[p]);
        same &= t[p] == value;
        t[p] = value;
        for (int k = p + 1; k < n; k++) {
          value = v[k].max();
          same &= t[k] == value;
          t[k] = value;
        }
        return same;
      }
    }
    throw Store.failException;
  }

  /** Copies the first length values of from into to; returns true if to already held them. */
  private static boolean copy(int[] from, int[] to, int length) {
    boolean same = Arrays.equals(from, 0, length, to, 0, length);
    if (!same) {
      System.arraycopy(from, 0, to, 0, length);
    }
    return same;
  }

  /**
   * Makes the domains of v domain consistent with a {@literal <=} v {@literal <=} b, where a and b
   * are tuples of the domains of v with a {@literal <=} b.
   */
  private void between(Store store, IntVar[] v, int[] a, int[] b) {

    int alpha = 0;
    while (alpha < n && a[alpha] == b[alpha]) {
      if (!v[alpha].singleton()) {
        v[alpha].domain.inValue(store.level, v[alpha], a[alpha]);
      }
      alpha++;
    }
    if (alpha == n) {
      return;
    }

    IntVar va = v[alpha];
    if (va.min() < a[alpha] || va.max() > b[alpha]) {
      va.domain.in(store.level, va, a[alpha], b[alpha]);
    }
    if (va.domain.nextValue(a[alpha]) < b[alpha]) {
      // a value strictly between a and b at alpha leaves the rest of the vector free
      return;
    }

    // v[alpha] is a[alpha] or b[alpha]. With a[alpha] the rest must be at least a's suffix: up to
    // the first position gamma where the domain has a value above a, a value below a's has no
    // support. With b[alpha] symmetrically up to delta. A value is pruned when it fails both.
    int gamma = alpha + 1;
    while (gamma < n && v[gamma].max() <= a[gamma]) {
      gamma++;
    }
    int delta = alpha + 1;
    while (delta < n && v[delta].min() >= b[delta]) {
      delta++;
    }
    int last = Math.min(Math.min(gamma, delta), n - 1);
    for (int j = alpha + 1; j <= last; j++) {
      // values in (b[j], a[j]) are below a's suffix and above b's suffix
      if (b[j] + 1 < a[j]) {
        v[j].domain.inComplement(store.level, v[j], b[j] + 1, a[j] - 1);
      }
    }
  }

  @Override
  public boolean satisfied() {
    for (int i = 0; i + 1 < m; i++) {
      // the largest tuple of x[i] against the smallest of x[i+1]
      int c = 0;
      for (int j = 0; j < n && c == 0; j++) {
        c = Integer.compare(x[i][j].max(), x[i + 1][j].min());
      }
      if (strict ? c >= 0 : c > 0) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return !hasDuplicates && LexChainExplanation.explain(trail, entry, x, strict, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return !hasDuplicates && LexChainExplanation.explainFailure(trail, x, strict, out);
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : LexChain([");
    for (int i = 0; i < m; i++) {
      result.append(Arrays.toString(x[i]));
      if (i < m - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(strict ? "<" : "<=").append(")");
    return result.toString();
  }

  @Override
  public LexChain copy(VarMap map) {
    IntVar[][] y = new IntVar[m][];
    for (int i = 0; i < m; i++) {
      y[i] = map.get(x[i]);
    }
    return new LexChain(y, strict);
  }
}
