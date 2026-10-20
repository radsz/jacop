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

  /** The sorted values of each column that occur in some tuple. */
  int[][] values;

  /** The values of each column as a domain. */
  IntDomain[] tableValues;

  /** The tuples with value values[i][k] in column i. */
  long[][][] supports;

  private int[][] residues;

  /** The value indices of each column that may still be in its domain, first liveSize of them. */
  private int[][] live;

  /** The valid tuples; the number of live values of column i is record liveRecord + i. */
  TrailedTupleSet valid;

  /** The words of the valid tuples, followed by the limit and the live sizes. */
  long[] state;

  /** The words, non-zero ones first. */
  int[] index;

  private int liveRecord;

  private final Map<IntVar, Integer> varMap;
  private int[] positionByIndex;
  private int indexOffset;

  /** Columns changed since the last consistency call. */
  int[] queue;

  int queueSize;
  boolean[] queued;

  /** Set while the constraint prunes, so that its own changes are not queued. */
  boolean pruning;

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
    valid = new TrailedTupleSet(n, arity);
    state = valid.state;
    index = valid.index;
    liveRecord = valid.limitRecord + 1;
    int words = valid.words;
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
    valid.rebuildIndex();
    positionByIndex = TrailedTupleSet.positionByIndex(x);
    indexOffset = TrailedTupleSet.minIndex(x);

    super.impose(store);
  }

  int valueIndex(int i, int v) {
    return Arrays.binarySearch(values[i], v);
  }

  void newEpochIfNeeded() {
    valid.newEpochIfNeeded(store.level);
  }

  @Override
  public void removeLevel(int level) {
    valid.removeLevel(level);
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
    return TrailedTupleSet.column(v, positionByIndex, indexOffset, varMap);
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
    return valid.limit();
  }

  boolean isEmpty() {
    return valid.isEmpty();
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
    valid.set(liveRecord + i, size);
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
    valid.clearMask();
    long[][] sup = supports[i];
    if (s <= size - s) {
      for (int k = 0; k < s; k++) {
        valid.addToMask(sup[l[k]]);
      }
    } else {
      for (int k = s; k < size; k++) {
        valid.addToMask(sup[l[k]]);
      }
      valid.reverseMask();
    }
    valid.intersectWithMask();
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
