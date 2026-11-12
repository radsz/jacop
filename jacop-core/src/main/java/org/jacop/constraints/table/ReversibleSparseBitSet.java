/*
 * ReversibleSparseBitSet.java
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

import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * ReversibleSparseBitSet implements the main data structure for table constraint. The words are
 * trailed one by one in a {@link TrailedTupleSet}, at most once per search level, instead of
 * copying the whole word array at each change.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class ReversibleSparseBitSet {

  private Store store;

  private TrailedTupleSet set;

  /** Creates an empty reversible sparse bit set. */
  public ReversibleSparseBitSet() {}

  /**
   * Creates a reversible sparse bit set initialized with valid tuples.
   *
   * @param store the constraint store
   * @param x the variables
   * @param tuple the tuples to validate and include
   */
  public ReversibleSparseBitSet(Store store, IntVar[] x, int[][] tuple) {

    int n = tuple.length;
    int lastWordSize = n % 64;
    int numberBitSets = n / 64 + (lastWordSize != 0 ? 1 : 0);

    long[] bs = new long[numberBitSets];
    for (int i = 0; i < n; i++) {
      if (validTuple(x, tuple[i])) {
        setBit(i, bs);
      }
    }

    init(store, bs);
  }

  /**
   * Initializes the reversible sparse bit set with the given words.
   *
   * @param store the constraint store
   * @param w the long array representing the bit set
   */
  void init(Store store, long[] w) {
    this.store = store;
    // the set of w.length * 64 tuples has w.length words, which are then replaced by w
    set = new TrailedTupleSet(w.length * 64, 0);
    System.arraycopy(w, 0, set.state, 0, w.length);
    // The non-zero words come first, so that a set without tuples is empty (limit -1).
    set.rebuildIndex();
    set.recordOn(store);
  }

  private void setBit(int n, long[] a) {

    int l = n % 64;
    int m = n / 64;

    a[m] |= 1L << l;
  }

  private boolean validTuple(IntVar[] x, int[] t) {

    int n = t.length;
    int i = 0;
    while (i < n) {
      if (!x[i].dom().contains(t[i])) {
        return false;
      }
      i++;
    }
    return true;
  }

  /**
   * The current words of the bit set; word w is element w. The array is changed in place, so it is
   * read, not kept, across changes of the set.
   */
  long[] words() {
    return set.state;
  }

  boolean isEmpty() {
    return set.isEmpty();
  }

  void clearMask() {
    set.clearMask();
  }

  void reverseMask() {
    set.reverseMask();
  }

  void addToMask(long[] m) {
    set.addToMask(m);
  }

  void intersectWithMask() {
    set.newEpochIfNeeded(store.level);
    set.intersectWithMask();
  }

  int intersectIndex(long[] m) {

    long[] wrds = set.state;
    int[] index = set.index;
    int limit = set.limit();
    for (int i = 0; i <= limit; i++) {
      int offset = index[i];
      if ((wrds[offset] & m[offset]) != 0) {
        return offset;
      }
    }
    return -1;
  }

  /**
   * It returns a string representation of the reversible sparse bit set.
   *
   * @return string describing the words and their values.
   */
  @Override
  public String toString() {
    StringBuilder s = new StringBuilder("words: ");

    long[] wrds = set.state;
    int[] index = set.index;
    long[] mask = set.mask;
    int n = set.limit() + 1;
    s.append("limit = ").append(n - 1).append("\n");
    for (int i = 0; i < n; i++) {
      int offset = index[i];
      s.append(offset).append(": ");
      s.append("0x%08X".formatted(wrds[offset]));
      if (i < n - 1) {
        s.append(", ");
      }
    }

    s.append("\nmask: ");
    for (int i = 0; i < mask.length; i++) {
      s.append(i).append(": ");
      s.append("0x%08X".formatted(mask[i])).append(", ");
    }
    return s.toString();
  }
}
