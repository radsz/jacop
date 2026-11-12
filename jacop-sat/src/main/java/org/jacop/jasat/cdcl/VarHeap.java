/*
 * VarHeap.java
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

package org.jacop.jasat.cdcl;

import java.util.Arrays;

/**
 * Binary max-heap of variables ordered by activity, used for EVSIDS decisions. Variables are
 * internal indices (0-based). The activities live in the solver; the heap keeps a reference to the
 * current array.
 *
 * <p>Each heap entry is one {@code long}: the variable in the low half and the high 32 bits of its
 * activity (sign, exponent and 20 mantissa bits, in an order-preserving encoding) in the high half.
 * A sift then compares the keys it already holds instead of reading the activity of each variable
 * it meets at a random place of the activity array. The key orders activities exactly up to a
 * relative difference of about 1e-6; only on equal keys does a comparison read the two activities,
 * so the heap orders the variables exactly as by their activities alone and the search does not
 * change.
 *
 * <p>A key is taken when a variable enters the heap or its activity increases ({@link #increased}).
 * A solver that changes the activity of a variable in the heap in any other way calls {@link
 * #rebuild} or, after scaling all activities by one positive factor, {@link #rescaled}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class VarHeap {

  private static final long KEY = 0xFFFF_FFFF_0000_0000L;

  private long[] heap = new long[16];
  private int size;
  private int[] index = initialIndex();
  private double[] activity;

  private static int[] initialIndex() {
    int[] index = new int[16];
    Arrays.fill(index, -1);
    return index;
  }

  // the entry of v: its activity's key in the high half, v in the low half
  private long entry(int v) {
    long bits = Double.doubleToRawLongBits(activity[v] + 0.0); // -0.0 as 0.0
    bits ^= (bits >> 63) >>> 1; // negative doubles in reverse order, so that signed order holds
    return (bits & KEY) | (v & 0xFFFF_FFFFL);
  }

  // whether entry e orders strictly before (above) entry f
  private boolean above(long e, long f) {
    long ke = e & KEY;
    long kf = f & KEY;
    return ke > kf || (ke == kf && activity[(int) e] > activity[(int) f]);
  }

  /**
   * Makes room for variables 0..n-1 and points the heap at the (possibly reallocated) activities.
   *
   * @param n the number of variables
   * @param activity the activity of each variable
   */
  public void grow(int n, double[] activity) {
    this.activity = activity;
    if (index.length < n) {
      int old = index.length;
      index = Arrays.copyOf(index, Math.max(n, 2 * old));
      Arrays.fill(index, old, index.length, -1);
    }
    if (heap.length < n) {
      heap = Arrays.copyOf(heap, Math.max(n, 2 * heap.length));
    }
  }

  /**
   * Tells whether a variable is in the heap.
   *
   * @param v the variable
   * @return true when it is in the heap
   */
  public boolean contains(int v) {
    return index[v] >= 0;
  }

  /**
   * Tells whether the heap is empty.
   *
   * @return true when no variable is in the heap
   */
  public boolean isEmpty() {
    return size == 0;
  }

  /**
   * Adds a variable, unless it is in the heap already.
   *
   * @param v the variable
   */
  public void insert(int v) {
    if (index[v] >= 0) {
      return;
    }
    int i = size++;
    heap[i] = entry(v);
    index[v] = i;
    up(i);
  }

  /**
   * Restores the heap order after the activity of v increased.
   *
   * @param v the variable
   */
  public void increased(int v) {
    int i = index[v];
    if (i >= 0) {
      heap[i] = entry(v);
      up(i);
    }
  }

  /**
   * Takes the keys again after every activity was multiplied by one positive factor, which keeps
   * the order of the variables, so that the heap stays as it is.
   */
  public void rescaled() {
    for (int i = 0; i < size; i++) {
      heap[i] = entry((int) heap[i]);
    }
  }

  /**
   * Removes a variable, if it is in the heap.
   *
   * @param v the variable
   */
  public void remove(int v) {
    int i = index[v];
    if (i < 0) {
      return;
    }
    index[v] = -1;
    long last = heap[--size];
    if (i < size) {
      heap[i] = last;
      int l = (int) last;
      index[l] = i;
      up(i);
      down(index[l]);
    }
  }

  /**
   * Returns the variable of highest activity, leaving it in the heap.
   *
   * @return the variable; the heap must not be empty
   */
  public int max() {
    return (int) heap[0];
  }

  /**
   * Removes the variable of highest activity.
   *
   * @return the variable; the heap must not be empty
   */
  public int removeMax() {
    int v = (int) heap[0];
    long last = heap[--size];
    index[v] = -1;
    if (size > 0) {
      heap[0] = last;
      index[(int) last] = 0;
      down(0);
    }
    return v;
  }

  /**
   * Rebuilds the heap from the given variables (all others are removed), for example after their
   * activities changed together.
   *
   * @param vars the variables, in the first n entries
   * @param n the number of variables
   */
  public void rebuild(int[] vars, int n) {
    for (int i = 0; i < size; i++) {
      index[(int) heap[i]] = -1;
    }
    size = 0;
    for (int i = 0; i < n; i++) {
      index[vars[i]] = size;
      heap[size++] = entry(vars[i]);
    }
    for (int i = size / 2 - 1; i >= 0; i--) {
      down(i);
    }
  }

  private void up(int i) {
    long e = heap[i];
    while (i > 0) {
      int parent = (i - 1) >> 1;
      long p = heap[parent];
      if (!above(e, p)) {
        break;
      }
      heap[i] = p;
      index[(int) p] = i;
      i = parent;
    }
    heap[i] = e;
    index[(int) e] = i;
  }

  private void down(int i) {
    long e = heap[i];
    while (true) {
      int child = 2 * i + 1;
      if (child >= size) {
        break;
      }
      long c = heap[child];
      if (child + 1 < size) {
        long r = heap[child + 1];
        if (above(r, c)) {
          child++;
          c = r;
        }
      }
      if (!above(c, e)) {
        break;
      }
      heap[i] = c;
      index[(int) c] = i;
      i = child;
    }
    heap[i] = e;
    index[(int) e] = i;
  }
}
