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
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class VarHeap {

  private int[] heap = new int[16];
  private int size;
  private int[] index = new int[0];
  private double[] activity;

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
    index[v] = size;
    heap[size++] = v;
    up(index[v]);
  }

  /**
   * Restores the heap order after the activity of v increased.
   *
   * @param v the variable
   */
  public void increased(int v) {
    if (index[v] >= 0) {
      up(index[v]);
    }
  }

  /**
   * Returns the variable of highest activity, leaving it in the heap.
   *
   * @return the variable; the heap must not be empty
   */
  public int max() {
    return heap[0];
  }

  /**
   * Removes the variable of highest activity.
   *
   * @return the variable; the heap must not be empty
   */
  public int removeMax() {
    int v = heap[0];
    int last = heap[--size];
    index[v] = -1;
    if (size > 0) {
      heap[0] = last;
      index[last] = 0;
      down(0);
    }
    return v;
  }

  /** Rebuilds the heap from the given variables (all others are removed). */
  void rebuild(int[] vars, int n) {
    for (int i = 0; i < size; i++) {
      index[heap[i]] = -1;
    }
    size = 0;
    for (int i = 0; i < n; i++) {
      index[vars[i]] = size;
      heap[size++] = vars[i];
    }
    for (int i = size / 2 - 1; i >= 0; i--) {
      down(i);
    }
  }

  private void up(int i) {
    int v = heap[i];
    double a = activity[v];
    while (i > 0) {
      int parent = (i - 1) >> 1;
      int p = heap[parent];
      if (activity[p] >= a) {
        break;
      }
      heap[i] = p;
      index[p] = i;
      i = parent;
    }
    heap[i] = v;
    index[v] = i;
  }

  private void down(int i) {
    int v = heap[i];
    double a = activity[v];
    while (true) {
      int child = 2 * i + 1;
      if (child >= size) {
        break;
      }
      if (child + 1 < size && activity[heap[child + 1]] > activity[heap[child]]) {
        child++;
      }
      int c = heap[child];
      if (activity[c] <= a) {
        break;
      }
      heap[i] = c;
      index[c] = i;
      i = child;
    }
    heap[i] = v;
    index[v] = i;
  }
}
