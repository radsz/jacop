/*
 * TrailedTupleSet.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * The reversible sparse bit-set of the valid tuples of a compact table, with its trail. The words
 * of the bit-set are records 0..words-1 of state, the number of non-zero words minus one (the
 * limit) is record words, and the owner may keep further records after it. The non-zero words are
 * index[0..limit]. Each record is trailed at most once per search level, using epoch stamps.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class TrailedTupleSet {

  /** The records: the words, the limit, then the records of the owner. */
  final long[] state;

  /** The words, non-zero ones first. */
  final int[] index;

  /** Work space of the mask operations. */
  final long[] mask;

  final int words;

  /** The record of the limit; the records of the owner start after it. */
  final int limitRecord;

  /** Set when a word lost tuples; the owner clears it. */
  boolean changed;

  private final int[] savedEpoch;
  private int epoch;
  private int epochLevel = -1;
  private long[] trail = new long[64];
  private int trailTop;
  private int[] markLevel = new int[16];
  private int[] markPosition = new int[16];
  private int markTop;

  /** The level of the last mark, Integer.MIN_VALUE when there is none. */
  private int topLevel = Integer.MIN_VALUE;

  private int currentLevel;

  /**
   * It creates the set of all tuples 0..tuples-1.
   *
   * @param tuples the number of tuples.
   * @param records the number of further records of the owner.
   */
  TrailedTupleSet(int tuples, int records) {
    words = (tuples + 63) / 64;
    limitRecord = words;
    state = new long[words + 1 + records];
    savedEpoch = new int[state.length];
    index = new int[words];
    mask = new long[words];
    for (int w = 0; w < words; w++) {
      index[w] = w;
    }
    for (int t = 0; t < tuples; t++) {
      state[t >> 6] |= 1L << t;
    }
    state[limitRecord] = words - 1L;
  }

  /** It puts the non-zero words first in the index; it is used before the search only. */
  void rebuildIndex() {
    int front = 0;
    int back = words - 1;
    for (int w = 0; w < words; w++) {
      if (state[w] != 0) {
        index[front++] = w;
      } else {
        index[back--] = w;
      }
    }
    state[limitRecord] = front - 1L;
  }

  // ---------------------------------------------------------------------------------------------
  // Trailing.

  void newEpochIfNeeded(int level) {
    currentLevel = level;
    if (epochLevel != currentLevel) {
      if (epoch == Integer.MAX_VALUE) {
        Arrays.fill(savedEpoch, 0);
        epoch = 0;
      }
      epoch++;
      epochLevel = currentLevel;
    }
  }

  void save(int slot) {
    if (savedEpoch[slot] == epoch) {
      return;
    }
    savedEpoch[slot] = epoch;
    if (topLevel != currentLevel) {
      if (markTop == markLevel.length) {
        markLevel = Arrays.copyOf(markLevel, markTop * 2);
        markPosition = Arrays.copyOf(markPosition, markTop * 2);
      }
      markLevel[markTop] = currentLevel;
      markPosition[markTop++] = trailTop;
      topLevel = currentLevel;
    }
    if (trailTop + 2 > trail.length) {
      trail = Arrays.copyOf(trail, trail.length * 2);
    }
    trail[trailTop] = slot;
    trail[trailTop + 1] = state[slot];
    trailTop += 2;
  }

  /** It saves a record and sets it. */
  void set(int slot, long value) {
    save(slot);
    state[slot] = value;
  }

  /** It tells whether some record was changed at the level or later. */
  boolean changedSince(int level) {
    return topLevel >= level;
  }

  /** It restores the records changed at the level or later. */
  void removeLevel(int level) {
    // Most levels change no record; the stamps of the current epoch are then on no record.
    if (topLevel < level) {
      return;
    }
    do {
      int start = markPosition[--markTop];
      while (trailTop > start) {
        trailTop -= 2;
        state[(int) trail[trailTop]] = trail[trailTop + 1];
      }
      topLevel = markTop > 0 ? markLevel[markTop - 1] : Integer.MIN_VALUE;
    } while (topLevel >= level);
    epochLevel = -1;
  }

  // ---------------------------------------------------------------------------------------------
  // Sparse bit-set.

  int limit() {
    return (int) state[limitRecord];
  }

  boolean isEmpty() {
    return limit() < 0;
  }

  void clearMask() {
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      mask[index[p]] = 0L;
    }
  }

  void addToMask(long[] set) {
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      mask[w] |= set[w];
    }
  }

  void reverseMask() {
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      mask[w] = ~mask[w];
    }
  }

  /** It keeps only the valid tuples that are in the mask. */
  void intersectWithMask() {
    int limit = limit();
    for (int p = limit; p >= 0; p--) {
      int w = index[p];
      long old = state[w];
      long word = old & mask[w];
      if (word != old) {
        changed = true;
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
      set(limitRecord, limit);
    }
  }

  /** It removes tuple t, whose word is index[position]. */
  void removeTuple(int t, int position) {
    int w = t >> 6;
    changed = true;
    save(w);
    state[w] &= ~(1L << t);
    if (state[w] == 0L) {
      int limit = limit();
      index[position] = index[limit];
      index[limit] = w;
      set(limitRecord, limit - 1L);
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Columns of the variables.

  /**
   * It gives, for each store index between the smallest and the largest store index of the
   * variables, the column of the variable, or -1; null when the store indices are too spread.
   *
   * @param x the variables of the columns.
   * @return the columns by store index, from the smallest store index.
   */
  static int[] positionByIndex(IntVar[] x) {
    int minIndex = minIndex(x);
    int maxIndex = Integer.MIN_VALUE;
    for (IntVar v : x) {
      maxIndex = Math.max(maxIndex, v.storeIndex);
    }
    if (minIndex < 0 || (long) maxIndex - minIndex >= 4L * x.length + 64) {
      return null;
    }
    int[] positions = new int[maxIndex - minIndex + 1];
    Arrays.fill(positions, -1);
    for (int i = 0; i < x.length; i++) {
      positions[x[i].storeIndex - minIndex] = i;
    }
    return positions;
  }

  /**
   * It gives the smallest store index of the variables.
   *
   * @param x the variables.
   * @return the smallest store index.
   */
  static int minIndex(IntVar[] x) {
    int minIndex = Integer.MAX_VALUE;
    for (IntVar v : x) {
      minIndex = Math.min(minIndex, v.storeIndex);
    }
    return minIndex;
  }

  /** Up to this many columns a variable is looked up by a scan rather than in the map. */
  private static final int SCAN_COLUMNS = 16;

  /**
   * It gives the column of a variable, or -1 if the variable is not a column.
   *
   * @param v the variable.
   * @param x the variables of the columns.
   * @param positionByIndex the columns by store index, or null.
   * @param indexOffset the smallest store index of the columns.
   * @param varMap the columns of the variables.
   * @return the column.
   */
  static int column(
      Var v, IntVar[] x, int[] positionByIndex, int indexOffset, Map<IntVar, Integer> varMap) {
    if (positionByIndex != null) {
      int k = v.storeIndex - indexOffset;
      return k >= 0 && k < positionByIndex.length ? positionByIndex[k] : -1;
    }
    // it runs on every change of a column, where a few comparisons are cheaper than hashing
    if (x.length <= SCAN_COLUMNS) {
      for (int i = 0; i < x.length; i++) {
        if (x[i] == v) {
          return i;
        }
      }
      return -1;
    }
    Integer position = varMap.get(v);
    return position == null ? -1 : position;
  }
}
