/*
 * CompactGroundTable.java
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

package org.jacop.constraints.table;

import java.util.Arrays;
import java.util.Map;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Shared machinery of the Compact-Table propagators over tuples of values: the tuples that are
 * still valid (all their values in the domains) are kept in a reversible sparse bit-set whose words
 * are trailed one by one, and each value of each column has the bit-set of the tuples that contain
 * it (Demeulenaere et al., CP 2016). Subclasses filter positive tables, negative tables (CT-neg,
 * Verhaeghe, Lecoutre and Schaus, AAAI 2017) or both, as the reified table does.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public abstract class CompactGroundTable extends Constraint implements UsesQueueVariable, Stateful {

  /** Variables of the columns. */
  final IntVar[] x;

  /** The tuples, without duplicates. */
  final int[][] tuples;

  final int arity;

  Store store;

  /** Number of words of the bit-sets. */
  int words;

  /** The sorted values of each column that occur in some tuple. */
  int[][] values;

  /** The values of each column as a domain. */
  IntDomain[] tableValues;

  /** The tuples with value values[i][k] in column i. */
  long[][][] supports;

  private int[][] residues;

  /** The value indices of each column that may still be in its domain, first liveSize of them. */
  private int[][] live;

  // Words of the bit-set are records 0..words-1, the limit is record words and the number of live
  // values of column i is record words + 1 + i.
  long[] state;
  int[] index;
  private long[] mask;
  private int limitRecord;
  private int liveRecord;

  private int[] savedEpoch;
  private int epoch;
  private int epochLevel = -1;
  private long[] trail = new long[64];
  private int trailTop;
  private int[] markLevel = new int[16];
  private int[] markPosition = new int[16];
  private int markTop;
  private int currentLevel;

  private final Map<IntVar, Integer> varMap;
  private int[] positionByIndex;
  private int indexOffset;

  /** Columns changed since the last consistency call. */
  int[] queue;

  int queueSize;
  boolean[] queued;

  /** Set while the constraint prunes, so that its own changes are not queued. */
  boolean pruning;

  /** Set when the current consistency call removed tuples. */
  boolean tableChanged;

  /**
   * It creates the shared part of a table over tuples of values.
   *
   * @param list the variables of the columns.
   * @param tuples the tuples.
   * @param extra further variables of the scope that are not columns (for example a control
   *     variable), or null.
   */
  protected CompactGroundTable(IntVar[] list, int[][] tuples, IntVar[] extra) {
    checkInputForNullness(new String[] {"list", "tuples"}, list, tuples);
    checkInputForDuplication("list", list);
    checkInput(
        tuples, t -> t.length == list.length, "tuple need to have the same size as list argument.");
    this.x = Arrays.copyOf(list, list.length);
    this.arity = list.length;
    this.tuples = distinct(tuples);
    this.varMap = Var.positionMapping(list, false, this.getClass());
    this.queueIndex = 1;
    if (extra == null) {
      setScope(list);
    } else {
      IntVar[] all = Arrays.copyOf(list, list.length + extra.length);
      System.arraycopy(extra, 0, all, list.length, extra.length);
      setScope(all);
    }
  }

  private static int[][] distinct(int[][] tuples) {
    int[][] sorted = Arrays.stream(tuples).map(int[]::clone).toArray(int[][]::new);
    Arrays.sort(sorted, Arrays::compare);
    int k = 0;
    for (int t = 0; t < sorted.length; t++) {
      if (k == 0 || !Arrays.equals(sorted[k - 1], sorted[t])) {
        sorted[k++] = sorted[t];
      }
    }
    return Arrays.copyOf(sorted, k);
  }

  @Override
  public void impose(Store store) {
    this.store = store;
    int n = tuples.length;
    words = (n + 63) / 64;
    queue = new int[arity];
    queued = new boolean[arity];

    values = new int[arity][];
    tableValues = new IntDomain[arity];
    supports = new long[arity][][];
    residues = new int[arity][];
    live = new int[arity][];
    for (int i = 0; i < arity; i++) {
      final int column = i;
      int[] vs = Arrays.stream(tuples).mapToInt(t -> t[column]).sorted().distinct().toArray();
      values[i] = vs;
      IntDomain d = new IntervalDomain();
      for (int v : vs) {
        d.unionAdapt(v, v);
      }
      tableValues[i] = d;
      supports[i] = new long[vs.length][words];
      residues[i] = new int[vs.length];
      for (int t = 0; t < n; t++) {
        supports[i][valueIndex(i, tuples[t][i])][t >> 6] |= 1L << t;
      }
    }

    state = new long[words + 1 + arity];
    savedEpoch = new int[state.length];
    limitRecord = words;
    liveRecord = words + 1;
    index = new int[words];
    mask = new long[words];
    for (int t = 0; t < n; t++) {
      state[t >> 6] |= 1L << t;
    }
    // Initial live values and removal of the tuples with a value outside the domains.
    for (int i = 0; i < arity; i++) {
      int[] vs = values[i];
      int[] l = new int[vs.length];
      int front = 0;
      int back = vs.length - 1;
      IntDomain d = x[i].dom();
      for (int k = 0; k < vs.length; k++) {
        if (d.contains(vs[k])) {
          l[front++] = k;
        } else {
          l[back--] = k;
          for (int w = 0; w < words; w++) {
            state[w] &= ~supports[i][k][w];
          }
        }
      }
      live[i] = l;
      state[liveRecord + i] = front;
    }
    int front = 0;
    int back = words - 1;
    for (int w = 0; w < words; w++) {
      if (state[w] != 0) {
        index[front++] = w;
      } else {
        index[back--] = w;
      }
    }
    state[limitRecord] = front - 1;

    int minIndex = Integer.MAX_VALUE;
    int maxIndex = Integer.MIN_VALUE;
    for (IntVar v : x) {
      minIndex = Math.min(minIndex, v.storeIndex);
      maxIndex = Math.max(maxIndex, v.storeIndex);
    }
    if (minIndex >= 0 && (long) maxIndex - minIndex < 4L * arity + 64) {
      indexOffset = minIndex;
      positionByIndex = new int[maxIndex - minIndex + 1];
      Arrays.fill(positionByIndex, -1);
      for (int i = 0; i < arity; i++) {
        positionByIndex[x[i].storeIndex - indexOffset] = i;
      }
    }

    super.impose(store);
  }

  int valueIndex(int i, int v) {
    return Arrays.binarySearch(values[i], v);
  }

  // ---------------------------------------------------------------------------------------------
  // Trailing.

  void newEpochIfNeeded() {
    currentLevel = store.level;
    if (epochLevel != currentLevel) {
      if (epoch == Integer.MAX_VALUE) {
        Arrays.fill(savedEpoch, 0);
        epoch = 0;
      }
      epoch++;
      epochLevel = currentLevel;
    }
  }

  private void save(int record) {
    if (savedEpoch[record] == epoch) {
      return;
    }
    savedEpoch[record] = epoch;
    if (markTop == 0 || markLevel[markTop - 1] != currentLevel) {
      if (markTop == markLevel.length) {
        markLevel = Arrays.copyOf(markLevel, markTop * 2);
        markPosition = Arrays.copyOf(markPosition, markTop * 2);
      }
      markLevel[markTop] = currentLevel;
      markPosition[markTop++] = trailTop;
    }
    if (trailTop + 2 > trail.length) {
      trail = Arrays.copyOf(trail, trail.length * 2);
    }
    trail[trailTop] = record;
    trail[trailTop + 1] = state[record];
    trailTop += 2;
  }

  @Override
  public void removeLevel(int level) {
    while (markTop > 0 && markLevel[markTop - 1] >= level) {
      int start = markPosition[--markTop];
      while (trailTop > start) {
        trailTop -= 2;
        state[(int) trail[trailTop]] = trail[trailTop + 1];
      }
    }
    epochLevel = -1;
    for (int p = 0; p < queueSize; p++) {
      queued[queue[p]] = false;
    }
    queueSize = 0;
    pruning = false;
  }

  /**
   * It gives the column of a variable, or -1 if the variable is not a column.
   *
   * @param v the variable.
   * @return the column.
   */
  int column(Var v) {
    if (positionByIndex != null) {
      int k = v.storeIndex - indexOffset;
      return k >= 0 && k < positionByIndex.length ? positionByIndex[k] : -1;
    }
    Integer position = varMap.get(v);
    return position == null ? -1 : position;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (pruning) {
      return;
    }
    int p = column(v);
    if (p >= 0 && !queued[p]) {
      queued[p] = true;
      queue[queueSize++] = p;
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Reversible sparse bit-set.

  int limit() {
    return (int) state[limitRecord];
  }

  boolean isEmpty() {
    return limit() < 0;
  }

  private void clearMask() {
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      mask[index[p]] = 0L;
    }
  }

  private void addToMask(long[] set) {
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      mask[w] |= set[w];
    }
  }

  private void reverseMask() {
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      mask[w] = ~mask[w];
    }
  }

  private void intersectWithMask() {
    int limit = limit();
    for (int p = limit; p >= 0; p--) {
      int w = index[p];
      long old = state[w];
      long word = old & mask[w];
      if (word != old) {
        tableChanged = true;
        save(w);
        state[w] = word;
        if (word == 0L) {
          index[p] = index[limit];
          index[limit] = w;
          limit--;
        }
      }
    }
    if (limit != limit()) {
      save(limitRecord);
      state[limitRecord] = limit;
    }
  }

  /** It tells whether some valid tuple has value k in column i, as residues allow. */
  boolean supported(int i, int k) {
    long[] set = supports[i][k];
    int r = residues[i][k];
    if ((state[r] & set[r]) != 0L) {
      return true;
    }
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      if ((state[w] & set[w]) != 0L) {
        residues[i][k] = w;
        return true;
      }
    }
    return false;
  }

  /** The number of valid tuples with value k in column i, or bound if it is at least bound. */
  long count(int i, int k, long bound) {
    long[] set = supports[i][k];
    long c = 0;
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      c += Long.bitCount(state[w] & set[w]);
      if (c >= bound) {
        return bound;
      }
    }
    return c;
  }

  /** The number of valid tuples. */
  long count() {
    long c = 0;
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      c += Long.bitCount(state[index[p]]);
    }
    return c;
  }

  int liveSize(int i) {
    return (int) state[liveRecord + i];
  }

  private void setLiveSize(int i, int size) {
    save(liveRecord + i);
    state[liveRecord + i] = size;
  }

  /** It updates the valid tuples of the queued columns and empties the queue. */
  void updateQueued() {
    for (int p = 0; p < queueSize; p++) {
      int i = queue[p];
      queued[i] = false;
      updateTable(i);
    }
    queueSize = 0;
  }

  /** It updates the valid tuples after the domain of variable i changed. */
  void updateTable(int i) {
    if (isEmpty()) {
      return;
    }
    IntDomain d = x[i].dom();
    int[] l = live[i];
    int[] vs = values[i];
    int size = liveSize(i);
    int s = size;
    int p = 0;
    while (p < s) {
      int k = l[p];
      if (d.contains(vs[k])) {
        p++;
      } else {
        s--;
        l[p] = l[s];
        l[s] = k;
      }
    }
    if (s == size) {
      return;
    }
    setLiveSize(i, s);
    clearMask();
    long[][] sup = supports[i];
    if (s <= size - s) {
      for (int k = 0; k < s; k++) {
        addToMask(sup[l[k]]);
      }
    } else {
      for (int k = s; k < size; k++) {
        addToMask(sup[l[k]]);
      }
      reverseMask();
    }
    intersectWithMask();
  }

  /** It removes the values of column i that no valid tuple contains (positive table). */
  void filterPositive(int i) {
    IntVar xi = x[i];
    if (!tableValues[i].contains(xi.dom())) {
      xi.domain.in(store.level, xi, tableValues[i]);
    }
    int[] l = live[i];
    int[] vs = values[i];
    int size = liveSize(i);
    int s = size;
    int p = 0;
    while (p < s) {
      int k = l[p];
      boolean alive = xi.dom().contains(vs[k]);
      if (alive && !supported(i, k)) {
        xi.domain.inComplement(store.level, xi, vs[k]);
        alive = false;
      }
      if (alive) {
        p++;
      } else {
        s--;
        l[p] = l[s];
        l[s] = k;
      }
    }
    if (s != size) {
      setLiveSize(i, s);
    }
  }

  /**
   * It removes the values of column i that occur in valid tuples together with every combination of
   * values of the other columns (negative table). Since the tuples are distinct, this is the case
   * when their number equals the product of the other domain sizes.
   *
   * @param i the column.
   * @param valid the number of valid tuples.
   * @return true if a value was removed.
   */
  boolean filterNegative(int i, long valid) {
    long others = 1;
    for (int j = 0; j < arity && others <= valid; j++) {
      if (j != i) {
        others *= x[j].getSize();
      }
    }
    if (others > valid) {
      return false;
    }
    IntVar xi = x[i];
    int[] l = live[i];
    int[] vs = values[i];
    int size = liveSize(i);
    boolean pruned = false;
    for (int p = 0; p < size; p++) {
      int k = l[p];
      if (xi.dom().contains(vs[k]) && count(i, k, others) >= others) {
        xi.domain.inComplement(store.level, xi, vs[k]);
        pruned = true;
      }
    }
    if (pruned) {
      // The tuples with the removed values are no longer valid and must not be counted.
      updateTable(i);
    }
    return pruned;
  }

  /** It filters every column as a negative table until no value is removed. */
  void filterNegativeToFixpoint() {
    boolean pruned = true;
    while (pruned && !isEmpty()) {
      pruned = false;
      for (int i = 0; i < arity && !isEmpty(); i++) {
        pruned |= filterNegative(i, count());
      }
    }
  }

  /**
   * It checks whether the values of the variables, all fixed, form one of the tuples.
   *
   * @return true if the current assignment is a tuple of the table.
   */
  boolean assignmentInTable() {
    int[] v = new int[arity];
    for (int i = 0; i < arity; i++) {
      v[i] = x[i].value();
    }
    return Arrays.binarySearch(tuples, v, Arrays::compare) >= 0;
  }

  /**
   * It appends the tuples to a description of the constraint.
   *
   * @param s the description.
   * @return the description.
   */
  StringBuilder appendTuples(StringBuilder s) {
    s.append(Arrays.asList(x)).append(", [");
    for (int t = 0; t < tuples.length; t++) {
      s.append(Arrays.toString(tuples[t]));
      if (t < tuples.length - 1) {
        s.append(", ");
      }
    }
    return s.append("]");
  }
}
