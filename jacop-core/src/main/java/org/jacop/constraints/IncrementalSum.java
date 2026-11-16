/*
 * IncrementalSum.java
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
 * in material form, distribution, or other use of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints;

import java.util.Arrays;
import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * The bounds of a long imposed linear sum kept up to date term by term. The store tells the sum
 * about every bound change of its variables ({@link LinearInt#queueVariable(int, Var)}), so a
 * consistency call reads the bounds of the sum instead of rescanning all terms, which is what
 * dominates propagation of sums with thousands of terms (costs of assignment problems). The minimal
 * weighted value and the variability of each term, and the two sums, are restored on backtracking
 * from an undo log recorded at the first change of each level.
 *
 * <p>The store's per-variable notification plays the role of advisors: M. Z. Lagerkvist and C.
 * Schulte, "Advisors for incremental propagation", CP 2007, LNCS 4741, pp. 409-422; for propagation
 * engines and events see C. Schulte and P. J. Stuckey, "Efficient constraint propagation engines",
 * ACM TOPLAS 31(1), 2008.
 */
final class IncrementalSum implements Stateful {

  private final LinearInt sum;
  private final Store store;

  /** The minimal weighted value of each term, as counted in sumMin. */
  final long[] termMin;

  /**
   * The variability of each term at imposition, an upper bound of its variability later; the terms
   * are sorted by it, descending within each sign, so a pruning pass stops at the first term whose
   * initial variability is within the slack.
   */
  final long[] initialVariability;

  // open addressing table from the identity hash of a variable to its position + 1
  private final int[] table;
  private final int mask;

  // undo log: one entry per term change
  private int entries;
  private int[] entryTerm = new int[16];
  private long[] entryMin = new long[16];
  private long[] entryVariability = new long[16];

  // one mark per level with a change
  private int marks;
  private int[] markLevel = new int[8];
  private int[] markEntries = new int[8];
  private long[] markSumMin = new long[8];
  private long[] markSumMax = new long[8];

  IncrementalSum(LinearInt sum, Store store) {
    this.sum = sum;
    this.store = store;
    int l = sum.l;
    this.termMin = new long[l];
    this.initialVariability = new long[l];
    int size = Integer.highestOneBit(Math.max(4, 2 * l - 1)) << 1;
    this.table = new int[size];
    this.mask = size - 1;
    for (int i = 0; i < l; i++) {
      put(sum.x[i], i);
    }
  }

  /** Fills the bounds of the sum and of each term from the current domains. */
  void initialize() {
    IntVar[] x = sum.x;
    long[] a = sum.a;
    long sMin = 0;
    long sMax = 0;
    long largest = 0;
    for (int i = 0; i < sum.l; i++) {
      IntDomain d = x[i].dom();
      long min;
      long max;
      if (i < sum.pos) {
        min = d.min() * a[i];
        max = d.max() * a[i];
      } else {
        min = d.max() * a[i];
        max = d.min() * a[i];
      }
      termMin[i] = min;
      sum.variability[i] = max - min;
      initialVariability[i] = max - min;
      largest = Math.max(largest, max - min);
      sMin += min;
      sMax += max;
    }
    sum.sumMin = sMin;
    sum.sumMax = sMax;
    sum.maxVariability = largest;
    sum.freePos = sum.pos;
    sum.freeNeg = sum.l;
  }

  private void put(Var v, int position) {
    int h = System.identityHashCode(v) & mask;
    while (table[h] != 0) {
      h = (h + 1) & mask;
    }
    table[h] = position + 1;
  }

  /** Rebuilds the table after the terms were reordered. */
  void rehash() {
    Arrays.fill(table, 0);
    for (int i = 0; i < sum.l; i++) {
      put(sum.x[i], i);
    }
  }

  private int position(Var v) {
    IntVar[] x = sum.x;
    int h = System.identityHashCode(v) & mask;
    int p;
    while ((p = table[h]) != 0) {
      if (x[p - 1] == v) {
        return p - 1;
      }
      h = (h + 1) & mask;
    }
    return -1;
  }

  /**
   * Takes a bound change of a variable into the bounds of the sum.
   *
   * @param v the changed variable.
   */
  void changed(Var v) {
    int i = position(v);
    if (i < 0) {
      return;
    }
    IntDomain d = ((IntVar) v).dom();
    long ai = sum.a[i];
    long min;
    long max;
    if (i < sum.pos) {
      min = d.min() * ai;
      max = d.max() * ai;
    } else {
      min = d.max() * ai;
      max = d.min() * ai;
    }
    long oldMin = termMin[i];
    long oldVariability = sum.variability[i];
    long newVariability = max - min;
    if (min == oldMin && newVariability == oldVariability) {
      return;
    }
    save(i, oldMin, oldVariability);
    termMin[i] = min;
    sum.variability[i] = newVariability;
    sum.sumMin += min - oldMin;
    sum.sumMax += max - (oldMin + oldVariability);
  }

  private void save(int term, long oldMin, long oldVariability) {
    int level = store.level;
    if (marks == 0 || markLevel[marks - 1] != level) {
      if (marks == markLevel.length) {
        int capacity = 2 * marks;
        markLevel = Arrays.copyOf(markLevel, capacity);
        markEntries = Arrays.copyOf(markEntries, capacity);
        markSumMin = Arrays.copyOf(markSumMin, capacity);
        markSumMax = Arrays.copyOf(markSumMax, capacity);
      }
      markLevel[marks] = level;
      markEntries[marks] = entries;
      markSumMin[marks] = sum.sumMin;
      markSumMax[marks] = sum.sumMax;
      marks++;
      store.recordChange(this);
    }
    if (entries == entryTerm.length) {
      int capacity = 2 * entries;
      entryTerm = Arrays.copyOf(entryTerm, capacity);
      entryMin = Arrays.copyOf(entryMin, capacity);
      entryVariability = Arrays.copyOf(entryVariability, capacity);
    }
    entryTerm[entries] = term;
    entryMin[entries] = oldMin;
    entryVariability[entries] = oldVariability;
    entries++;
  }

  @Override
  public void removeLevel(int level) {
    long[] variability = sum.variability;
    while (marks > 0 && markLevel[marks - 1] >= level) {
      marks--;
      int start = markEntries[marks];
      while (entries > start) {
        entries--;
        int i = entryTerm[entries];
        termMin[i] = entryMin[entries];
        variability[i] = entryVariability[entries];
      }
      sum.sumMin = markSumMin[marks];
      sum.sumMax = markSumMax[marks];
    }
  }
}
